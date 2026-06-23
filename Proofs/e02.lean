import examples.e02.translation.Funs
import Proofs.Anodized
import Proofs.IntExternal

open Aeneas Std.Result
open e02
open anodized_logic.arithmetic (int)

-- Tag the extracted spec predicates so `step*` unfolds them automatically.
register_anodized_simps

theorem collatz_spec (n : int) (hn : __anodized_fn_requires_collatz n = ok true) :
    collatz n ⦃ result => __anodized_fn_ensures_collatz n result = ok true ⦄ := by
  unfold collatz collatz_loop __anodized_fn_ensures_collatz
  -- easy to prove once we have proven the collatz conjecture
  sorry

/-! ## `u8` functions specified with the logical `int` type

These functions operate on `u8`, but their `#[spec]` clauses are written with `int` because the
`u8` operations are fallible and so cannot appear in a pure-`bool` spec predicate. The proofs go
through `step*` plus the `@[step]` `int` specs in `Proofs.IntExternal`; `eq_ok_iff` turns the
monadic `… = ok true` (pre)conditions into `⦃ ⦄` triples that `step*` can run. -/

theorem decrement_spec : Anodized decrement := by
  intro x hx
  simp only [step_simps] at hx
  unfold decrement
  step*
  rw [eq_ok_iff]; step*

-- Characterise `add`'s pre/postconditions as plain arithmetic facts. `eq_ok_iff` + `step*`
-- run the monadic `int` predicate to a `decide (...)`, which then reduces to the proposition.
theorem requires_add_spec' {x y : Std.U8} :
    __anodized_fn_requires_add x y = ok true ↔ x.val + y.val ≤ 255 := by
  have hk : __anodized_fn_requires_add x y = ok (decide ((x.val : Int) + y.val ≤ 255)) := by
    rw [eq_ok_iff]; step*; simp_all
  rw [hk]; simp only [Std.Result.ok.injEq, decide_eq_true_eq]; omega

theorem ensures_add_spec' {x y out : Std.U8} :
    __anodized_fn_ensures_add x y out = ok true ↔ out.val = x.val + y.val := by
  have hk : __anodized_fn_ensures_add x y out = ok (decide ((out.val : Int) = x.val + y.val)) := by
    rw [eq_ok_iff]; step*; simp_all
  rw [hk]; simp only [Std.Result.ok.injEq, decide_eq_true_eq]; omega

theorem add_spec : Anodized add := by
  intro x y h
  rw [requires_add_spec'] at h -- precondition ↦ no-overflow bound
  simp only [ensures_add_spec'] -- postcondition ↦ result.val = x.val + y.val
  unfold add
  step*

theorem sub_spec : Anodized sub := by
  intro x y h
  have hbound : (y.val : Int) ≤ x.val := by
    have hk : __anodized_fn_requires_sub x y = ok (decide ((y.val : Int) ≤ x.val)) := by
      rw [eq_ok_iff]
      step*
      simp_all
    rw [hk] at h; simpa using h
  unfold sub
  step*
  rw [eq_ok_iff]; step*
