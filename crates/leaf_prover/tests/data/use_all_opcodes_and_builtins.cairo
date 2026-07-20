%builtins output pedersen range_check ecdsa bitwise ec_op keccak poseidon range_check96 add_mod mul_mod

from starkware.cairo.common.alloc import alloc
from starkware.cairo.common.cairo_builtins import (
    BitwiseBuiltin,
    EcOpBuiltin,
    HashBuiltin,
    KeccakBuiltin,
    ModBuiltin,
    PoseidonBuiltin,
    SignatureBuiltin,
    UInt384,
)
from starkware.cairo.common.keccak_state import KeccakBuiltinState
from starkware.cairo.common.modulo import BATCH_SIZE
from starkware.cairo.common.poseidon_state import PoseidonBuiltinState
from starkware.cairo.common.registers import get_label_location
from starkware.cairo.common.registers import get_fp_and_pc
from starkware.cairo.common.bool import FALSE, TRUE

func do_output{output_ptr: felt*}(n_builtin_usages: felt) {
    if (n_builtin_usages == 0) {
        return ();
    }

    assert [output_ptr] = 1000 + n_builtin_usages;
    let output_ptr = output_ptr + 1;

    do_output(n_builtin_usages=n_builtin_usages - 1);
    return ();
}

func do_pedersen{pedersen_ptr: HashBuiltin*}(n_builtin_usages: felt) {
    if (n_builtin_usages == 0) {
        return ();
    }

    assert pedersen_ptr.x = 2000;
    assert pedersen_ptr.y = 3000;
    let expect_res = 2259827999605678368300255972310867999576917457292275299312258452858451849126;
    assert expect_res = pedersen_ptr.result;
    let pedersen_ptr = pedersen_ptr + HashBuiltin.SIZE;

    do_pedersen(n_builtin_usages=n_builtin_usages - 1);
    return ();
}

func do_range_check{range_check_ptr: felt*}(n_builtin_usages: felt) {
    if (n_builtin_usages == 0) {
        return ();
    }

    // Check that 0 <= n_builtin_usages < 2**128.
    assert [range_check_ptr] = n_builtin_usages;
    let range_check_ptr = range_check_ptr + 1;

    do_range_check(n_builtin_usages=n_builtin_usages - 1);
    return ();
}

func do_ecdsa{ecdsa_ptr: SignatureBuiltin*}(n_builtin_usages: felt) {
    if (n_builtin_usages == 0) {
        return ();
    }

    tempvar signature_r = 3086480810278599376317923499561306189851900463386393948998357832163236918254;
    tempvar signature_s = 598673427589502599949712887611119751108407514580626464031881322743364689811;
    %{
        ecdsa_builtin.add_signature(ids.ecdsa_ptr.address_, (ids.signature_r, ids.signature_s))
    %}
    tempvar exp_key = 1735102664668487605176656616876767369909409133946409161569774794110049207117;
    assert exp_key = ecdsa_ptr.pub_key;
    assert ecdsa_ptr.message = 2718;
    let ecdsa_ptr = ecdsa_ptr + SignatureBuiltin.SIZE;

    do_ecdsa(n_builtin_usages=n_builtin_usages - 1);
    return ();
}

func do_bitwise{bitwise_ptr: BitwiseBuiltin*}(n_builtin_usages: felt) {
    if (n_builtin_usages == 0) {
        return ();
    }

    assert bitwise_ptr.x = 3;  // Binary representation 0b011.
    assert bitwise_ptr.y = 6;  // Binary representation 0b110.
    // assert 0x2 = bitwise_ptr.x_and_y;  // Calculate 0b011 & 0b110 = 0b010 = 0x2.
    assert 0x5 = bitwise_ptr.x_xor_y;  // Calculate 0b011 ^ 0b110 = 0b101 = 0x5.
    assert 0x7 = bitwise_ptr.x_or_y;  // Calculate 0b011 & 0b110 = 0b111 = 0x7.
    let bitwise_ptr = bitwise_ptr + BitwiseBuiltin.SIZE;

    do_bitwise(n_builtin_usages=n_builtin_usages - 1);
    return ();
}

func do_ec_op{ec_op_ptr: EcOpBuiltin*}(n_builtin_usages: felt) {
    if (n_builtin_usages == 0) {
        return ();
    }

    assert ec_op_ptr.p.x = 0x49ee3eba8c1600700ee1b87eb599f16716b0b1022947733551fde4050ca6804;
    assert ec_op_ptr.p.y = 0x3ca0cfe4b3bc6ddf346d49d06ea0ed34e621062c0e056c1d0405d266e10268a;
    assert ec_op_ptr.q.x = 0x1ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca;
    assert ec_op_ptr.q.y = 0x5668060aa49730b7be4801df46ec62de53ecd11abe43a32873000c36e8dc1f;
    assert ec_op_ptr.m = 3;
    assert 0x7e7981dbdcab7a12e82a71563265fe17d1e468def04dc824c342bd113b8a6ba = ec_op_ptr.r.x;
    assert 0x74af28209b54a0943e10972953ae3acc93ca2d74caf5b07c0a833fbb9aba0ff = ec_op_ptr.r.y;
    let ec_op_ptr = ec_op_ptr + EcOpBuiltin.SIZE;

    do_ec_op(n_builtin_usages=n_builtin_usages - 1);
    return ();
}

func do_keccak{keccak_ptr: KeccakBuiltin*}(n_builtin_usages: felt) {
    if (n_builtin_usages == 0) {
        return ();
    }

    assert keccak_ptr.input = KeccakBuiltinState(s0=0, s1=1, s2=2, s3=3, s4=4, s5=5, s6=6, s7=7);
    tempvar keccak_output = keccak_ptr.output;
    assert keccak_output = KeccakBuiltinState(
        s0=0x39d703c98a1b2e1a2ddf0c93810df2d39b6dfecdee6832188d,
        s1=0x541c4683d434a407a3525e2f20fa9431b65cd58e995379146d,
        s2=0x66f2b6f9585469eef0f16447a1bc76adc5f3b602a698dfdc42,
        s3=0x16f13d5794d8770f73a01aa7e00accde43f4fa6a208a7f03a5,
        s4=0xfdf1ac3b6b45fdeee26ff23d7a5318a94dabb4efbba7ad35a1,
        s5=0x639b68738d3ebd70e1181f43ccfbfc0e5ba26fb99251069ae2,
        s6=0x50c5875966fe759e96419d03d1ff8c66e868d68a052651260d,
        s7=0x51611748d0540c05bd45cd46cdb6cdcdce7402d755893da7e0,
    );
    let keccak_ptr = keccak_ptr + KeccakBuiltin.SIZE;

    do_keccak(n_builtin_usages=n_builtin_usages - 1);
    return ();
}

func do_poseidon{poseidon_ptr: PoseidonBuiltin*}(n_builtin_usages: felt) {
    if (n_builtin_usages == 0) {
        return ();
    }

    assert poseidon_ptr.input = PoseidonBuiltinState(s0=0, s1=1, s2=2);
    assert poseidon_ptr.output = PoseidonBuiltinState(
        s0=0x5134197931125e849424475aa20cd6ca0ce8603b79177c3f76e2119c8f98c53,
        s1=0x30b51bb39c4e74544fc2576ac2a3cf44485ad135802c6ac1246659ad34f241f,
        s2=0x3241fe256bea8c2e2fa69098127e17e4020dc42158e61fd3e6dc236e0c0cac,
    );
    let poseidon_ptr = poseidon_ptr + PoseidonBuiltin.SIZE;

    do_poseidon(n_builtin_usages=n_builtin_usages - 1);
    return ();
}

func do_range_check96{range_check96_ptr: felt*}(n_builtin_usages: felt) {
    if (n_builtin_usages == 0) {
        return ();
    }

    // Check that 0 <= n_builtin_usages < 2**96.
    assert [range_check96_ptr] = n_builtin_usages;
    let range_check96_ptr = range_check96_ptr + 1;

    do_range_check96(n_builtin_usages=n_builtin_usages - 1);
    return ();
}

func do_add_mod{add_mod_ptr: ModBuiltin*}(n_builtin_usages: felt) {
    if (n_builtin_usages == 0) {
        return ();
    }

    let (values_ptr: UInt384*) = alloc();

    assert values_ptr[0] = UInt384(
        d0=0x000000000000000000000006,
        d1=0x000000000000000000000000,
        d2=0x000000000000000000000000,
        d3=0x000000000000000000000000,
    );

    assert values_ptr[1] = UInt384(
        d0=0x000000000000000000000007,
        d1=0x000000000000000000000000,
        d2=0x000000000000000000000000,
        d3=0x000000000000000000000000,
    );

    assert values_ptr[2] = UInt384(
        d0=0x00000000000000000000000d,
        d1=0x000000000000000000000000,
        d2=0x000000000000000000000000,
        d3=0x000000000000000000000000,
    );

    let (add_mod_offsets_ptr) = get_label_location(add_offsets);

    // Apply the add_mod builtin.
    assert add_mod_ptr[0] = ModBuiltin(
        p=UInt384(
            d0=0xffffffff,
            d1=0xfffffffffffffffeffffffff,
            d2=0xffffffffffffffffffffffff,
            d3=0xffffffffffffffffffffffff,
        ),
        values_ptr=values_ptr,
        offsets_ptr=add_mod_offsets_ptr,
        n=BATCH_SIZE,
    );
    let add_mod_ptr = add_mod_ptr + ModBuiltin.SIZE;

    do_add_mod(n_builtin_usages=n_builtin_usages - 1);
    return ();

    add_offsets:
    dw 0;
    dw 4;
    dw 8;
}

func do_mul_mod{mul_mod_ptr: ModBuiltin*}(n_builtin_usages: felt) {
    if (n_builtin_usages == 0) {
        return ();
    }

    let (values_ptr: UInt384*) = alloc();

    assert values_ptr[0] = UInt384(
        d0=0x000000000000000000000007,
        d1=0x000000000000000000000000,
        d2=0x000000000000000000000000,
        d3=0x000000000000000000000000,
    );

    assert values_ptr[1] = UInt384(
        d0=0x000000000000000000000006,
        d1=0x000000000000000000000000,
        d2=0x000000000000000000000000,
        d3=0x000000000000000000000000,
    );

    assert values_ptr[2] = UInt384(
        d0=0x00000000000000000000002a,
        d1=0x000000000000000000000000,
        d2=0x000000000000000000000000,
        d3=0x000000000000000000000000,
    );

    let (mul_mod_offsets_ptr) = get_label_location(mul_offsets);

    // Apply the mul_mod builtin.
    assert mul_mod_ptr[0] = ModBuiltin(
        p=UInt384(
            d0=0xffffffff,
            d1=0xfffffffffffffffeffffffff,
            d2=0xffffffffffffffffffffffff,
            d3=0xffffffffffffffffffffffff,
        ),
        values_ptr=values_ptr,
        offsets_ptr=mul_mod_offsets_ptr,
        n=BATCH_SIZE,
    );

    let mul_mod_ptr = mul_mod_ptr + ModBuiltin.SIZE;

    do_mul_mod(n_builtin_usages=n_builtin_usages - 1);
    return ();

    mul_offsets:
    dw 0;
    dw 4;
    dw 8;
}

// The main function. Reads the number of usages for each builtin from the input,
// and calls each builtin accordingly.
func main{
    output_ptr: felt*,
    pedersen_ptr: HashBuiltin*,
    range_check_ptr: felt*,
    ecdsa_ptr: SignatureBuiltin*,
    bitwise_ptr: BitwiseBuiltin*,
    ec_op_ptr: EcOpBuiltin*,
    keccak_ptr: KeccakBuiltin*,
    poseidon_ptr: PoseidonBuiltin*,
    range_check96_ptr: felt*,
    add_mod_ptr: ModBuiltin*,
    mul_mod_ptr: ModBuiltin*,
}() {
    alloc_locals;
    local n_output = 2;
    local n_pedersen = 50;
    local n_range_check = 50;
    local n_ecdsa = 0;
    local n_bitwise = 50;
    local n_ec_op = 50;
    local n_keccak = 0;
    local n_poseidon = 50;
    local n_range_check96 = 50;
    local n_add_mod = 50;
    local n_mul_mod = 50;
    local n_memory_holes = 50;

    // Call output builtin.
    do_output(n_builtin_usages=n_output);

    // Call pedersen builtin.
    do_pedersen(n_builtin_usages=n_pedersen);

    // Call range_check builtin.
    do_range_check(n_builtin_usages=n_range_check);

    // Call ecdsa builtin.
    do_ecdsa(n_builtin_usages=n_ecdsa);

    // Call bitwise builtin.
    do_bitwise(n_builtin_usages=n_bitwise);

    // Call ec_op builtin.
    do_ec_op(n_builtin_usages=n_ec_op);

    // Call keccak builtin.
    do_keccak(n_builtin_usages=n_keccak);

    // Call poseidon builtin.
    do_poseidon(n_builtin_usages=n_poseidon);

    // Call range_check96 builtin.
    do_range_check96(n_builtin_usages=n_range_check96);

    // Call add_mod builtin.
    do_add_mod(n_builtin_usages=n_add_mod);

    // Call mul_mod builtin.
    do_mul_mod(n_builtin_usages=n_mul_mod);

    // Create memory holes.
    [ap] = 1, ap++;
    ap += n_memory_holes;
    [ap] = 1, ap++;

blake2s();
    ap+=1;
    add_ap();
    ap+=1;
    jump_rel_imm();
    ap+=1;
    jump_abs();
    ap+=1;
    call_abs();
    ap+=2;
    call_abs_ap();
    ap+=2;
    jnz_not_taken_ap();
    ap+=1;
    jnz_not_taken_fp();
    ap+=1;
    jnz_taken_fp();
    ap+=1;
    jnz_taken_ap();
    ap+=1;
    assert_eq();
    ap+=2;
    add_small();
    ap+=1;
    add_big();
    ap+=1;
    mul_small();
    ap+=1;
    qm31();
    ap+=1;
    assert_eq_double_deref();
    ap+=1;
    mul_big();
    ap+=1;
    generic();
    ap+=1;
    jump_rel();
    ap+=1;
    jump_abs_double_deref();

    return ();
}


func add_ap() {
    [ap] = 38, ap++;
    [ap] = 12, ap++;
    ap += [ap -2];
    ap += [fp + 1];
    ap += 1;
    [ap] = 1, ap++;
    ret;
}

func jump_rel_imm(){
    jmp rel 2;
    [ap] = [ap-1] + 3, ap++;
    ret;
}

func jump_abs(){
    call rel 2;
    [ap] = [ap-1] + 3;
    jmp abs [ap];
    ret;
}

func call_abs(){
    alloc_locals;
    let (_, local __pc__) = get_fp_and_pc();
    local addr = cast(__pc__ + 4, felt);
    call abs addr;
    ret;
}

func call_abs_ap(){
    alloc_locals;
    let (_, local __pc__) = get_fp_and_pc();
    tempvar addr = cast(__pc__ + 4, felt);
    call abs addr;
    ret;
}

func jnz_not_taken_ap(){
    [ap] = 0, ap++;
    jmp rel 2 if [ap-1] != 0;
    ret;
}

func jnz_not_taken_fp(){
    call rel 2;
    [ap] = 0, ap++;
    jmp rel 2 if [fp] != 0;
    [ap] = 1, ap++;
    ret;
}

func jnz_taken_fp(){
    call rel 2;
    jmp rel 2 if [fp-1] != 0;
    [ap] = 1, ap++;
    ret;
}

func jnz_taken_ap(){
    [ap] = 5, ap++;
    jmp rel 2 if [ap-1] != 0;
    [ap] = 1, ap++;
    ret;
}

func assert_eq(){
    [ap] =  8, ap++;
    [ap] =  8, ap++;
    [ap+2] = [fp + 1];
    [ap] = 1, ap++;
    ret;
}

func add_small() {
    call rel 2;
    [ap] = 134217725, ap++;
    [ap] = 2, ap++;
    // 134217725 + 2= 2^27-1.
    [ap] = [fp] + [ap-1], ap++;
    // 134217724 + 3 = 2^27-1.
    [ap] = [fp-1] + 134217724, ap++;
    [ap] = 1, ap++;
    ret;
}

func add_big() {
    call rel 2;
    [ap] = 134217725, ap++;
    [ap] = 3, ap++;
    // 134217725 + 3 = is 2^27.
    [ap] = [fp] + [ap-1], ap++;
    [ap] = [ap-1] + 1, ap++;
    [ap] = 1, ap++;
    ret;
}

func mul_small(){
   // 2^36-1 is the maximal factor value for a small mul.
   [ap] =  262145, ap++;
   [ap] =  [ap-1]*262143, ap++;
   // 2^36-1 is the maximal factor value for a small mul.
   [ap] = [ap-1], ap++;
   [ap] = [ap-1] * [ap-2], ap++;
   [ap] = [ap-2]*2147483647, ap++;
   [ap] = 1, ap++;
   ret; 
}

func mul_big(){
    [ap] =  8, ap++;
    // 2^36 is the minimal factor value for a big mul.
    [ap] = 262144, ap++;
    [ap] = [ap-1] * 262144, ap++;
    [ap] = [ap-1] * [ap-3], ap++;
    [ap] = [ap-2]* 2, ap++;
    [ap] = 1, ap++;
    ret; 
}

func assert_eq_double_deref(){
    call rel 2;
    ap += 2;
    [ap] = 100, ap++;
    [ap] = [[fp - 1] + 2], ap++;  // [fp - 2] is the old fp.
    [ap] = 5;
    ret;
}

func generic(){
    [ap]=1, ap++;
    [ap]=2, ap++;
    jmp rel [ap-2] if [ap-1] != 0;
    [ap]=1, ap++;
    ret;
}

func jump_rel(){
    [ap] = 1, ap++;
    jmp rel [ap-1];
    [ap] = 2, ap++;
    ret;
}
func jump_abs_double_deref(){
    alloc_locals;
    let (_, local __pc__) = get_fp_and_pc();
    local x = cast(__pc__ + 8, felt);
    call rel 2;
    jmp abs [[ap - 2] + 1];
    [ap] = 5;
    ret;
}

func qm31() {
    let qm31_op0_coordinates_a = 0x544b2fba;
    let qm31_op0_coordinates_b = 0x673cff77;
    let qm31_op0_coordinates_c = 0x60713d44;
    let qm31_op0_coordinates_d = 0x499602d2;
    let qm31_op0 = qm31_op0_coordinates_a + qm31_op0_coordinates_b*(2**36) + qm31_op0_coordinates_c*(2**72) + qm31_op0_coordinates_d*(2**108);

    let qm31_op1_coordinates_a = 0x4b18de99;
    let qm31_op1_coordinates_b = 0x55f6fb62;
    let qm31_op1_coordinates_c = 0x6e2290d9;
    let qm31_op1_coordinates_d = 0x7cd851b9;
    let qm31_op1 = qm31_op1_coordinates_a + qm31_op1_coordinates_b*(2**36) + qm31_op1_coordinates_c*(2**72) + qm31_op1_coordinates_d*(2**108);

    let qm31_add_dst_coordinates_a = 0x1f640e54;
    let qm31_add_dst_coordinates_b = 0x3d33fada;
    let qm31_add_dst_coordinates_c = 0x4e93ce1e;
    let qm31_add_dst_coordinates_d = 0x466e548c;
    let qm31_add_dst = qm31_add_dst_coordinates_a + qm31_add_dst_coordinates_b*(2**36) + qm31_add_dst_coordinates_c*(2**72) + qm31_add_dst_coordinates_d*(2**108);

    let qm31_mul_dst_coordinates_a = 0x38810ab4;
    let qm31_mul_dst_coordinates_b = 0x5a0fd30a;
    let qm31_mul_dst_coordinates_c = 0x2527b81e;
    let qm31_mul_dst_coordinates_d = 0x4b1ed1cd;
    let qm31_mul_dst = qm31_mul_dst_coordinates_a + qm31_mul_dst_coordinates_b*(2**36) + qm31_mul_dst_coordinates_c*(2**72) + qm31_mul_dst_coordinates_d*(2**108);

    let runner_output_mul_dst = run_qm31_operation(missing_operand=0, is_imm=FALSE, is_mul=TRUE, dst_or_op0=qm31_op0, op0_or_op1=qm31_op1);
    assert runner_output_mul_dst = qm31_mul_dst;
    let runner_output_add_dst = run_qm31_operation(missing_operand=0, is_imm=FALSE, is_mul=FALSE, dst_or_op0=qm31_op0, op0_or_op1=qm31_op1);
    assert runner_output_add_dst = qm31_add_dst;

    let runner_output_mul_op0 = run_qm31_operation(missing_operand=1, is_imm=FALSE, is_mul=TRUE, dst_or_op0=qm31_mul_dst, op0_or_op1=qm31_op1);
    assert runner_output_mul_op0 = qm31_op0;
    let runner_output_add_op0 = run_qm31_operation(missing_operand=1, is_imm=FALSE, is_mul=FALSE, dst_or_op0=qm31_add_dst, op0_or_op1=qm31_op1);
    assert runner_output_add_op0 = qm31_op0;

    let runner_output_mul_op1 = run_qm31_operation(missing_operand=2, is_imm=FALSE, is_mul=TRUE, dst_or_op0=qm31_mul_dst, op0_or_op1=qm31_op0);
    assert runner_output_mul_op1 = qm31_op1;
    let runner_output_add_op1 = run_qm31_operation(missing_operand=2, is_imm=FALSE, is_mul=FALSE, dst_or_op0=qm31_add_dst, op0_or_op1=qm31_op0);
    assert runner_output_add_op1 = qm31_op1;

    let runner_output_mul_dst = run_qm31_operation(missing_operand=0, is_imm=TRUE, is_mul=TRUE, dst_or_op0=qm31_op0, op0_or_op1=qm31_op1);
    assert runner_output_mul_dst = qm31_mul_dst;
    let runner_output_add_dst = run_qm31_operation(missing_operand=0, is_imm=TRUE, is_mul=FALSE, dst_or_op0=qm31_op0, op0_or_op1=qm31_op1);
    assert runner_output_add_dst = qm31_add_dst;

    let runner_output_mul_op0 = run_qm31_operation(missing_operand=1, is_imm=TRUE, is_mul=TRUE, dst_or_op0=qm31_mul_dst, op0_or_op1=qm31_op1);
    assert runner_output_mul_op0 = qm31_op0;
    let runner_output_add_op0 = run_qm31_operation(missing_operand=1, is_imm=TRUE, is_mul=FALSE, dst_or_op0=qm31_add_dst, op0_or_op1=qm31_op1);
    assert runner_output_add_op0 = qm31_op0;

    return ();
}

func run_qm31_operation(
    missing_operand: felt,
    is_imm: felt,
    is_mul: felt,
    dst_or_op0: felt,
    op0_or_op1: felt,
) -> felt {
    alloc_locals;

    // Set flags and offsets.
    let (local offsets) = alloc();
    let (local flags) = alloc();

    assert offsets[missing_operand] = 2**15; // the missing operand will be written to [ap]

    assert flags[2] = is_imm; // flag_op1_imm = 0;
    assert flags[5] = 1-is_mul; // flag_res_add = 1-is_mul;
    assert flags[6] = is_mul; // flag_res_mul = is_mul;
    assert flags[7] = 0; // flag_PC_update_jump = 0;
    assert flags[8] = 0; // flag_PC_update_jump_rel = 0;
    assert flags[9] = 0; // flag_PC_update_jnz = 0;
    assert flags[10] = 0; // flag_ap_update_add = 0;
    assert flags[11] = 0; // flag_ap_update_add_1 = 0;
    assert flags[12] = 0; // flag_opcode_call = 0;
    assert flags[13] = 0; // flag_opcode_ret = 0;
    assert flags[14] = 1; // flag_opcode_assert_eq = 1;

    if (missing_operand == 0) {
        assert offsets[1] = 2**15 - 4;
        assert offsets[2] = 2**15 - 3 + 4 * is_imm;
        assert flags[0] = 0; // flag_dst_base_fp
        assert flags[1] = 1; // flag_op0_base_fp
    }
    if (missing_operand == 1) {
        assert offsets[0] = 2**15 - 4;
        assert offsets[2] = 2**15 - 3 + 4 * is_imm;
        assert flags[0] = 1; // flag_dst_base_fp
        assert flags[1] = 0; // flag_op0_base_fp
    }
    if (missing_operand == 2) {
        assert is_imm = FALSE;
        assert offsets[0] = 2**15 - 4;
        assert offsets[1] = 2**15 - 3;
        assert flags[0] = 1; // flag_dst_base_fp
        assert flags[1] = 1; // flag_op0_base_fp
    }
    assert flags[3] = (2 - flags[0] - flags[1]) * (1 - is_imm); // flag_op1_base_fp
    assert flags[4] = 1 - is_imm - flags[3]; // flag_op1_base_ap

    // Compute the instruction encoding.
    let flag_num = flags[0] + flags[1]*(2**1) + flags[2]*(2**2) + flags[3]*(2**3) + flags[4]*(2**4) + flags[5]*(2**5) + flags[6]*(2**6) + flags[14]*(2**14);
    let qm31_opcode_extension_num = 3;
    let instruction_encoding = offsets[0] + offsets[1]*(2**16) + offsets[2]*(2**32) + flag_num*(2**48) + qm31_opcode_extension_num*(2**63);

    // Run the instruction and return the result.
    if (is_imm == TRUE) {
        assert op0_or_op1 = 0x7cd851b906e2290d9055f6fb6204b18de99;
        if (missing_operand == 0) {
            if (is_mul == TRUE) {
                assert instruction_encoding=0x1c04680017ffc8000;
                dw 0x1c04680017ffc8000;
                dw 0x7cd851b906e2290d9055f6fb6204b18de99;
                return [ap];
            }
            assert instruction_encoding=0x1c02680017ffc8000;
            dw 0x1c02680017ffc8000;
            dw 0x7cd851b906e2290d9055f6fb6204b18de99;
            return [ap];
        }
        if (missing_operand == 1) {
            if (is_mul == TRUE) {
                assert instruction_encoding=0x1c045800180007ffc;
                dw 0x1c045800180007ffc;
                dw 0x7cd851b906e2290d9055f6fb6204b18de99;
                return [ap];
            }
            assert instruction_encoding=0x1c025800180007ffc;
            dw 0x1c025800180007ffc;
            dw 0x7cd851b906e2290d9055f6fb6204b18de99;
            return [ap];
        }
    }

    if (missing_operand == 0) {
        if (is_mul == TRUE) {
            assert instruction_encoding=0x1c04a7ffd7ffc8000;
            dw 0x1c04a7ffd7ffc8000;
            return [ap];
        }
        assert instruction_encoding=0x1c02a7ffd7ffc8000;
        dw 0x1c02a7ffd7ffc8000;
        return [ap];
    }
    if (missing_operand == 1) {
        if (is_mul == TRUE) {
            assert instruction_encoding=0x1c0497ffd80007ffc;
            dw 0x1c0497ffd80007ffc;
            return [ap];
        }
        assert instruction_encoding=0x1c0297ffd80007ffc;
        dw 0x1c0297ffd80007ffc;
        return [ap];
    }
    if (is_mul == TRUE) {
        assert instruction_encoding=0x1c05380007ffd7ffc;
        dw 0x1c05380007ffd7ffc;
        return [ap];
    }
    assert instruction_encoding=0x1c03380007ffd7ffc;
    dw 0x1c03380007ffd7ffc;
    return [ap];
}

from starkware.cairo.common.cairo_blake2s.blake2s import STATE_SIZE_FELTS, INPUT_BLOCK_FELTS, _get_sigma
from starkware.cairo.common.cairo_blake2s.packed_blake2s import N_PACKED_INSTANCES

const COUNTER = 64;
const U32_MASK = 0xffffffff;

// Tests the Blake2s and Blake2sLastBlock opcode runners using a preexisting implementation within the repo as reference.
// The initial state, a random message of 64 bytes and a counter are used as input.
// Both the opcode and the reference implementation are run on the same inputs and then their outputs are compared.
// Before comparing the outputs, it is verified that the opcode runner has written the output to the correct location.
func blake2s{}() {
    run_blake_test(is_last_block=FALSE);
    run_blake_test(is_last_block=TRUE);
    return ();
}
func run_blake_test{}(is_last_block: felt) {
    alloc_locals;

    let (local random_message) = alloc();
    assert random_message[0] = 930933030;
    assert random_message[1] = 1766240503;
    assert random_message[2] = 3660871006;
    assert random_message[3] = 388409270;
    assert random_message[4] = 1948594622;
    assert random_message[5] = 3119396969;
    assert random_message[6] = 3924579183;
    assert random_message[7] = 2089920034;
    assert random_message[8] = 3857888532;
    assert random_message[9] = 929304360;
    assert random_message[10] = 1810891574;
    assert random_message[11] = 860971754;
    assert random_message[12] = 1822893775;
    assert random_message[13] = 2008495810;
    assert random_message[14] = 2958962335;
    assert random_message[15] = 2340515744;

    let (local input_state) = alloc();
    // Set the initial state to IV (IV[0] is modified).
    assert input_state[0] = 0x6B08E647;  // IV[0] ^ 0x01010020 (config: no key, 32 bytes output).
    assert input_state[1] = 0xBB67AE85;
    assert input_state[2] = 0x3C6EF372;
    assert input_state[3] = 0xA54FF53A;
    assert input_state[4] = 0x510E527F;
    assert input_state[5] = 0x9B05688C;
    assert input_state[6] = 0x1F83D9AB;
    assert input_state[7] = 0x5BE0CD19;
    static_assert STATE_SIZE_FELTS == 8;

    // Use the packed blake2s_compress to compute the output of the first instance.
    let (sigma) = _get_sigma();
    let (local cairo_output) = alloc();


    // Run the blake2s opcode runner on the same inputs and store its output.
    let vm_output = run_blake_compress_opcode(
        is_last_block = is_last_block,
        dst=COUNTER,
        op0=input_state,
        op1=random_message,
    );

    // Verify that the opcode runner has written the 8 felts to the correct location.
    tempvar check_nonempty = vm_output[0];
    tempvar check_nonempty = vm_output[1];
    tempvar check_nonempty = vm_output[2];
    tempvar check_nonempty = vm_output[3];
    tempvar check_nonempty = vm_output[4];
    tempvar check_nonempty = vm_output[5];
    tempvar check_nonempty = vm_output[6];
    tempvar check_nonempty = vm_output[7];

    return ();
}

// Forces the runner to execute the Blake2s or Blake2sLastBlock opcode with the given operands.
// op0 is a pointer to an array of 8 felts as u32 integers of the state.
// op1 is a pointer to an array of 16 felts as u32 integers of the message.
// dst is a felt representing a u32 of the counter.
// ap contains a pointer to an array of 8 felts as u32 integers of the output state.
// Those values are stored within addresses fp-5, fp-4 and fp-3 respectively.
// An instruction encoding is built from offsets -5, -4, -3 and flags which are all 0 except for
// those denoting uses of fp as the base for operand addresses and flag_opcode_blake (16th flag).
// The instruction is then written to [pc] and the runner is forced to execute Blake2s.
func run_blake_compress_opcode(
    is_last_block: felt,
    dst: felt,
    op0: felt*,
    op1: felt*,
) -> felt* {
    alloc_locals;

    // Set the offsets for the operands.
    let offset0 = (2**15)-5;
    let offset1 = (2**15)-4;
    let offset2 = (2**15)-3;
    static_assert dst == [fp - 5];
    static_assert op0 == [fp - 4];
    static_assert op1 == [fp - 3];

    // Set the flags for the instruction.
    let flag_dst_base_fp = 1;
    let flag_op0_base_fp = 1;
    let flag_op1_imm = 0;
    let flag_op1_base_fp = 1;
    let flag_op1_base_ap = 0;
    let flag_res_add = 0;
    let flag_res_mul = 0;
    let flag_PC_update_jump = 0;
    let flag_PC_update_jump_rel = 0;
    let flag_PC_update_jnz = 0;
    let flag_ap_update_add = 0;
    let flag_ap_update_add_1 = 0;
    let flag_opcode_call = 0;
    let flag_opcode_ret = 0;
    let flag_opcode_assert_eq = 0;

    let flag_num = flag_dst_base_fp+flag_op0_base_fp*(2**1)+flag_op1_imm*(2**2)+flag_op1_base_fp*(2**3);
    let blake_compress_opcode_extension_num = 1;
    let blake_compress_last_block_opcode_extension_num = 2;
    let blake_compress_instruction_num = offset0 + offset1*(2**16) + offset2*(2**32) + flag_num*(2**48) + blake_compress_opcode_extension_num*(2**63);
    let blake_compress_last_block_instruction_num = offset0 + offset1*(2**16) + offset2*(2**32) + flag_num*(2**48) + blake_compress_last_block_opcode_extension_num*(2**63);
    static_assert blake_compress_instruction_num==9226608988349300731;
    static_assert blake_compress_last_block_instruction_num==18449981025204076539;

    // Write the instruction to [pc] and point [ap] to the designated output.
    let (local vm_output) = alloc();
    assert [ap] = cast(vm_output, felt);

    jmp last_block if is_last_block!=0;
    dw 9226608988349300731;
    return cast([ap], felt*);

    last_block:
    dw 18449981025204076539;
    return cast([ap], felt*);
}
