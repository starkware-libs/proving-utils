//! A fixed set of rayon thread pools ([`PoolSet`]) for partitioning prove work across a single
//! machine's cores.

use std::sync::Arc;

use rayon::{ThreadPool, ThreadPoolBuilder};

/// A fixed set of rayon thread pools for partitioning prove work across a single machine's cores.
///
/// Each prove already saturates rayon's global pool, so independent proves on the same pool just
/// contend. `K` pools of `M` threads let `K` proves run concurrently, each confined to its own `M`
/// cores — real speedup for the tree's independent siblings when per-prove scaling plateaus below the
/// full core count. Build once and reuse (pool creation spawns OS threads).
pub struct PoolSet {
    pub(crate) pools: Vec<Arc<ThreadPool>>,
}

impl PoolSet {
    /// Creates `n_pools` pools of `threads_per_pool` worker threads each (e.g. `PoolSet::new(2, 48)`
    /// on a 96-core machine).
    pub fn new(n_pools: usize, threads_per_pool: usize) -> Self {
        // Optionally deprioritize pool workers so GPU-producer / composition threads win CPU.
        // Byte-neutral. OFF unless RECURSION_POOL_NICE is set (an integer nice delta, or "idle").
        let sched = std::env::var("RECURSION_POOL_NICE").ok();
        let pools = (0..n_pools.max(1))
            .map(|_| {
                let sched = sched.clone();
                Arc::new(
                    ThreadPoolBuilder::new()
                        .num_threads(threads_per_pool)
                        .start_handler(move |_| apply_pool_thread_priority(sched.as_deref()))
                        .build()
                        .expect("build rayon pool"),
                )
            })
            .collect();
        Self { pools }
    }

    /// Number of pools (the max concurrency this set can run).
    pub fn n_pools(&self) -> usize {
        self.pools.len()
    }

    /// Runs `f` on pool `i % n_pools`, blocking until it completes. Unlike [`Self::map`], dispatches
    /// ONE job at a time, so a caller can stream jobs onto specific pools as they arrive.
    pub fn install_on<T, F>(&self, i: usize, f: F) -> T
    where
        F: FnOnce() -> T + Send,
        T: Send,
    {
        self.pools[i % self.pools.len()].install(f)
    }

    /// Runs `jobs` across the pools (round-robin, order-preserving), up to `n_pools()` in flight at
    /// once. A single job runs on the global pool (whole machine) since nothing runs alongside it.
    pub fn map<T, F>(&self, jobs: Vec<F>) -> Vec<T>
    where
        F: FnOnce() -> T + Send,
        T: Send,
    {
        if jobs.len() <= 1 {
            return jobs.into_iter().map(|f| f()).collect();
        }
        let k = self.pools.len();
        let mut buckets: Vec<Vec<(usize, F)>> = (0..k).map(|_| Vec::new()).collect();
        for (i, f) in jobs.into_iter().enumerate() {
            buckets[i % k].push((i, f));
        }
        let n: usize = buckets.iter().map(Vec::len).sum();
        let mut slots: Vec<Option<T>> = (0..n).map(|_| None).collect();
        std::thread::scope(|s| {
            let handles: Vec<_> = buckets
                .into_iter()
                .zip(self.pools.iter())
                .map(|(bucket, pool)| {
                    s.spawn(move || {
                        bucket
                            .into_iter()
                            .map(|(i, f)| (i, pool.install(f)))
                            .collect::<Vec<(usize, T)>>()
                    })
                })
                .collect();
            for h in handles {
                for (i, r) in h.join().expect("pool job panicked") {
                    slots[i] = Some(r);
                }
            }
        });
        slots.into_iter().map(Option::unwrap).collect()
    }
}

/// Lower THIS thread's scheduling priority (once per pool worker at startup). Byte-neutral scheduling
/// syscall only; unprivileged. `who==0` targets the calling thread (per-thread nice on Linux).
fn apply_pool_thread_priority(sched: Option<&str>) {
    match sched {
        None => {}
        Some("idle") | Some("IDLE") => {
            let p = libc::sched_param { sched_priority: 0 };
            unsafe {
                libc::sched_setscheduler(0, libc::SCHED_IDLE, &p);
            }
        }
        Some(s) => {
            let nice: i32 = s.parse().unwrap_or(10);
            unsafe {
                libc::setpriority(libc::PRIO_PROCESS, 0, nice);
            }
        }
    }
}
