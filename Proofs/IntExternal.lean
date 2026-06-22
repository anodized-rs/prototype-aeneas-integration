import examples.e02.translation.FunsExternal

/-!
# `@[step]` specifications for the external `anodized_logic.arithmetic.int` operations

`anodized_logic.arithmetic.int` is `num_bigint::BigInt` (mathematical ℤ) but is extracted as
an opaque type, and its arithmetic/comparison interop ops are emitted as opaque axioms in
`examples.e02.translation.FunsExternal`. Here we give each of those ops a `@[step]` spec so
`step*` can reason about them.

`int.toInt` is the value model (the assumed `int ≅ ℤ`). Each spec mirrors the Rust impl,
which lifts the `i32` operand via `int::from` and then does exact integer arithmetic /
comparison. Division and remainder truncate toward zero (`num_bigint` semantics) and require
a non-zero divisor.

Stated as axioms for now (no proofs); they can be discharged once `int` has a concrete model.
This file lives outside the generated `translation/` directory so it survives re-extraction.
-/

open Aeneas Std Result
open anodized_logic.arithmetic (int)

/-- Value model: the mathematical integer denoted by a logical `int`. -/
axiom anodized_logic.arithmetic.int.toInt : int → Int

/-- `int + i32` : exact integer addition (`self + int::from(rhs)`). -/
@[step] axiom int_add_i32_step (x : int) (y : Std.I32) :
  (int.Insts.CoreOpsArithAddI32int.add x y) ⦃ z => z.toInt = x.toInt + y.val ⦄

/-- `&int / i32` : truncated integer division; divisor must be non-zero. -/
@[step] axiom int_div_i32_step (x : int) (y : Std.I32) (h : y.val ≠ 0) :
  (Shared0int.Insts.CoreOpsArithDivI32int.div x y) ⦃ z => z.toInt = Int.tdiv x.toInt y.val ⦄

/-- `&int % i32` : truncated remainder (sign of dividend); divisor must be non-zero. -/
@[step] axiom int_rem_i32_step (x : int) (y : Std.I32) (h : y.val ≠ 0) :
  (Shared0int.Insts.CoreOpsArithRemI32int.rem x y) ⦃ z => z.toInt = Int.tmod x.toInt y.val ⦄

/-- `i32 * &int` : exact integer multiplication (`self * (*rhs)`). -/
@[step] axiom i32_mul_int_step (y : Std.I32) (x : int) :
  (I32.Insts.CoreOpsArithMulShared0intint.mul y x) ⦃ z => z.toInt = y.val * x.toInt ⦄

/-- `int == i32` : equality against the lifted `i32`. -/
@[step] axiom int_eq_i32_step (x : int) (y : Std.I32) :
  (int.Insts.CoreCmpPartialEqI32.eq x y) ⦃ b => b = decide (x.toInt = y.val) ⦄

/-- `int > i32` : strict comparison against the lifted `i32`. -/
@[step] axiom int_gt_i32_step (x : int) (y : Std.I32) :
  (int.Insts.CoreCmpPartialOrdI32.gt x y) ⦃ b => b = decide (x.toInt > y.val) ⦄

/-- `int::from(u8)` : the lifted value of a `u8`. -/
@[step] axiom int_from_u8_step (x : Std.U8) :
  (int.Insts.CoreConvertFromU8.from x) ⦃ z => z.toInt = (x.val : Int) ⦄

/-- `int + int` : exact integer addition. -/
@[step] axiom int_add_int_step (x y : int) :
  (int.Insts.CoreOpsArithAddintint.add x y) ⦃ z => z.toInt = x.toInt + y.toInt ⦄

/-- `int - int` : exact integer subtraction. -/
@[step] axiom int_sub_int_step (x y : int) :
  (int.Insts.CoreOpsArithSubintint.sub x y) ⦃ z => z.toInt = x.toInt - y.toInt ⦄

/-- `int == int` : equality. -/
@[step] axiom int_eq_int_step (x y : int) :
  (int.Insts.CoreCmpPartialEqint.eq x y) ⦃ b => b = decide (x.toInt = y.toInt) ⦄

/-- `int ≤ int` : comparison. -/
@[step] axiom int_le_int_step (x y : int) :
  (int.Insts.CoreCmpPartialOrdint.le x y) ⦃ b => b = decide (x.toInt ≤ y.toInt) ⦄
