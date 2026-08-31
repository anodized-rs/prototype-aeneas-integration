import examples.e01.translation.Funs
import Anodized
import Proofs.SliceIterExternal
import Proofs.ToAeneas

open Aeneas Std.Result
open Aeneas.Std (Slice)
open e01

register_anodized_simps

@[step]
theorem f2_spec : Anodized f2 := by
  intro _
  unfold f2
  step*

@[step]
theorem f4_spec : Anodized f4 := by
  intro x hx
  -- precondition `x > 0`
  simp only [step_simps] at hx
  unfold f4
  step*

/-! ## Postconditions

Both loop functions carry the same two-clause `ensures`: `output` is an upper bound for `x`, and
`x.contains(output) == (x.len() > 0)` — i.e. the bound is attained whenever there is anything to
attain it. Aeneas extracts the conjunction short-circuited, as *run clause 1; if it holds, run
clause 2*, so `ensures_conj_iff` below splits it once for both functions.

Clause 1 goes through the opaque `Iterator::all` and so needs `slice_iter_all_spec` from
`Proofs.SliceIterExternal`, whose `hq` hypothesis is discharged by `le_closure_body_spec`.
Clause 2 needs nothing assumed: Aeneas models `core::slice::contains` as `List.anyM`. -/

/-- The two ensures functions have identical shape — clause 1, then clause 2 guarded by it.
Given each clause's reduction to a decidable proposition, the whole thing is their conjunction. -/
private theorem ensures_conj_iff {call₁ call₂ : Std.Result Bool} {P Q : Prop}
    [Decidable P] [Decidable Q]
    (h₁ : call₁ = ok (decide P)) (h₂ : call₂ = ok (decide Q)) :
    (do let b ← call₁; if b then call₂ else ok false) = ok true ↔ P ∧ Q := by
  rw [h₁]
  by_cases hp : P <;> simp [hp, h₂]

/-- The body Aeneas generates for the closure `|item| item <= captured`: it decides `· ≤ out` and
returns the captured state unchanged. Both loops get their own copy of this closure, differing
only in name, so the content is proved once here. -/
private theorem le_closure_body_spec (out v : Std.U8) :
    (do
      let b ← Shared1A.Insts.CoreCmpPartialOrdShared0B.le Std.core.cmp.PartialOrdU8 v out
      ok (b, out)) ⦃ r => r.1 = decide (v.val ≤ out.val) ∧ r.2 = out ⦄ := by
  step*
  simp only [Std.core.cmp.impls.PartialOrdU8.le]

/-- Clause 1, `x.iter().all(|item| item <= output)`, run to a proposition. -/
private theorem iter_all_le_eq
    (inst : Std.core.ops.function.FnMut Std.U8 Std.U8 Bool)
    (hinst : ∀ out v, inst.call_mut out v ⦃ r => r.1 = decide (v.val ≤ out.val) ∧ r.2 = out ⦄)
    (x : Slice Std.U8) (out : Std.U8) :
    (do
      let i ← Std.core.slice.Slice.iter x
      let (b, _) ← core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all inst i out
      ok b) = ok (decide (∀ v ∈ x.val, v.val ≤ out.val)) := by
  rw [eq_ok_iff]
  unfold Std.core.slice.Slice.iter
  simp only [Std.bind_tc_ok]
  step with (slice_iter_all_spec inst out (fun v => decide (v.val ≤ out.val)) (hinst out) ⟨x, 0⟩)
  rw [b_post, List.drop_zero, Bool.eq_iff_iff]
  simp

/-- `List.anyM` over a predicate that never fails is just `List.any`. -/
private theorem anyM_ok {α : Type} (p : α → Bool) :
    ∀ l : List α, List.anyM (fun e => (ok (p e) : Std.Result Bool)) l = ok (l.any p)
  | [] => rfl
  | a :: l => by
    simp only [List.anyM, List.any_cons, Std.bind_tc_ok]
    by_cases h : p a
    · rw [h]; rfl
    · simp only [Bool.not_eq_true] at h
      rw [h]
      simpa using anyM_ok p l

/-- `List.any` against `u8` equality decides membership. -/
private theorem any_eq_decide_mem (out : Std.U8) :
    ∀ l : List Std.U8, l.any (Std.core.cmp.impls.PartialEqU8.eq out) = decide (out ∈ l)
  | [] => by simp
  | a :: t => by
    simp only [List.any_cons, any_eq_decide_mem out t, List.mem_cons,
      Std.core.cmp.impls.PartialEqU8.eq]
    simp

/-- Clause 2, `x.contains(output) == (x.len() > 0)`, run to a proposition. Unlike clause 1 this
needs nothing assumed — Aeneas models `core::slice::contains` as `List.anyM`. -/
private theorem contains_clause_eq (x : Slice Std.U8) (out : Std.U8) :
    (do
      let b ← Std.core.slice.Slice.contains Std.core.cmp.PartialEqU8 x out
      let n := Std.Slice.len x
      ok (b = (n > 0#usize))) = ok (decide (out ∈ x.val ↔ 0 < x.length)) := by
  simp [Std.core.slice.Slice.contains, anyM_ok, any_eq_decide_mem]

/-- `f_loop`'s postcondition: `out` dominates `x`, and is an element of `x` exactly when `x` is
non-empty — i.e. `out` is the maximum. -/
theorem ensures_f_loop_iff (x : Slice Std.U8) (out : Std.U8) :
    __anodized_fn_ensures_f_loop x out = ok true
      ↔ (∀ v ∈ x.val, v.val ≤ out.val) ∧ (out ∈ x.val ↔ 0 < x.length) := by
  unfold __anodized_fn_ensures_f_loop
    __anodized_fn_ensures_f_loop.closure.Insts.CoreOpsFunctionFnTupleSharedU8Bool.call
    __anodized_fn_ensures_f_loop.closure_1.Insts.CoreOpsFunctionFnTupleSharedU8Bool.call
  exact ensures_conj_iff (iter_all_le_eq _ le_closure_body_spec x out) (contains_clause_eq x out)

/-- `f_while`'s postcondition: as `ensures_f_loop_iff`. -/
theorem ensures_f_while_iff (x : Slice Std.U8) (out : Std.U8) :
    __anodized_fn_ensures_f_while x out = ok true
      ↔ (∀ v ∈ x.val, v.val ≤ out.val) ∧ (out ∈ x.val ↔ 0 < x.length) := by
  unfold __anodized_fn_ensures_f_while
    __anodized_fn_ensures_f_while.closure.Insts.CoreOpsFunctionFnTupleSharedU8Bool.call
    __anodized_fn_ensures_f_while.closure_1.Insts.CoreOpsFunctionFnTupleSharedU8Bool.call
  exact ensures_conj_iff (iter_all_le_eq _ le_closure_body_spec x out) (contains_clause_eq x out)

/-! ## Loop specifications

Both loops accumulate a running maximum, so both invariants say *the accumulator dominates the
prefix already scanned*. Each iteration extends that prefix by one index, which is the content of
`forall_index_succ` below; the four branches of the two loop proofs differ only in what they
supply as the new bound. -/

/-- Extend a dominance invariant by one index: if `old` dominates the first `k` elements, `new` is
at least `old`, and `new` also dominates `x[k]`, then `new` dominates the first `k + 1`. -/
private theorem forall_index_succ {x : Slice Std.U8} {k : Nat} {old new : Std.U8}
    (hprev : ∀ j, j < k → (x[j]!).val ≤ old.val)
    (hold : old.val ≤ new.val)
    (hk : (x[k]!).val ≤ new.val) :
    ∀ j, j < k + 1 → (x[j]!).val ≤ new.val := by
  intro j hj
  by_cases hje : j = k
  · exact hje ▸ hk
  · exact le_trans (hprev j (by omega)) hold

/-- Bridge the two ways of saying "`res` dominates `x`": the loop invariants are stated by index,
the extracted postconditions by membership. -/
private theorem forall_mem_of_forall_index {x : Slice Std.U8} {res : Std.U8}
    (h : ∀ j, j < x.length → (x[j]!).val ≤ res.val) : ∀ v ∈ x.val, v.val ≤ res.val := by
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
  have h := h j hj
  simp_lists at h
  exact h

/-- Turn the two loop invariants at exit into the extracted postcondition.

The accumulator disjunct is `res.val = 0 ∨ res ∈ x`, which is what the loops maintain cheaply:
the accumulator starts at `0` and only ever becomes an element. On a non-empty slice the first
disjunct is not a weakness — a zero accumulator bounds every element above by `0`, so `x[0]` is
itself `0` and equals the accumulator. -/
private theorem max_spec_of_invariants {x : Slice Std.U8} {res : Std.U8}
    (hub : ∀ j, j < x.length → (x[j]!).val ≤ res.val)
    (hmem : res.val = 0 ∨ res ∈ x.val) :
    (∀ v ∈ x.val, v.val ≤ res.val) ∧ (res ∈ x.val ↔ 0 < x.length) := by
  refine ⟨forall_mem_of_forall_index hub, List.length_pos_of_mem, fun hpos => ?_⟩
  rcases hmem with hz | h
  · have h0 := hub 0 hpos
    simp_lists at h0
    have hval : (x.val[0]'hpos).val = res.val := by omega
    exact Std.UScalar.eq_of_val_eq hval ▸ List.getElem_mem _
  · exact h

@[step]
private theorem f_loop_loop_spec (x : Slice Std.U8) :
    f_loop_loop { start := 0#usize, «end» := Std.Slice.len x } x 0#u8
      ⦃ res => (∀ j, j < x.length → (x[j]!).val ≤ res.val) ∧ (res.val = 0 ∨ res ∈ x.val) ⦄ := by
  apply Std.loop.spec_decr_nat
    (measure := fun s => x.length - s.1.start.val)
    (inv := fun s => s.1.«end».val = x.length ∧ s.1.start.val ≤ x.length ∧
      (∀ j, j < s.1.start.val → (x[j]!).val ≤ s.2.val) ∧ (s.2.val = 0 ∨ s.2 ∈ x.val))
  · rintro ⟨iter, max⟩ ⟨hend, hlo, hinv, hmem⟩
    simp only at hend hlo hinv hmem
    unfold f_loop_loop.body
    by_cases hlt : iter.start.val < iter.«end».val
    · step*
      · -- cont, `x[i] > max`: accumulator becomes the element just read, so it is in `x`.
        rename_i hoi hmax
        obtain rfl : i = iter.start := Option.some.inj (hoi.symm.trans o_post1)
        refine ⟨by simp [o_post3, hend], by omega, ?_, Or.inr ?_, by omega⟩
        · simp only [o_post2]
          exact forall_index_succ hinv (by scalar_tac) (by simp_lists [i1_post]; scalar_tac)
        · rw [i1_post]
          exact List.getElem_mem _
      · -- cont, `x[i] ≤ max`: accumulator unchanged, so its disjunct carries over.
        rename_i hoi hmax
        obtain rfl : i = iter.start := Option.some.inj (hoi.symm.trans o_post1)
        refine ⟨by simp [o_post3, hend], by omega, ?_, hmem, by omega⟩
        simp only [o_post2]
        exact forall_index_succ hinv (by scalar_tac) (by simp_lists [i1_post]; scalar_tac)
    · push Not at *
      step with Std.core.iter.range.IteratorRange.next_Usize_spec_none
      simp only [*]
      step*
      grind
  · simp

@[step]
theorem f_loop_spec : Anodized f_loop := by
  intro x _
  simp only [ensures_f_loop_iff]
  unfold f_loop
  step*
  exact max_spec_of_invariants ‹_› ‹_›

@[step]
private theorem f_while_loop_spec (x : Slice Std.U8) :
    f_while_loop x 0#u8 0#usize
      ⦃ res => (∀ j, j < x.length → (x[j]!).val ≤ res.val) ∧ (res.val = 0 ∨ res ∈ x.val) ⦄ := by
  unfold f_while_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s => x.length - s.2.val)
    (inv := fun s => s.2.val ≤ x.length ∧ (∀ j, j < s.2.val → (x[j]!).val ≤ s.1.val) ∧
      (s.1.val = 0 ∨ s.1 ∈ x.val))
  -- `hBody`, as in `f_loop_loop_spec`. Here the guard is inside the body rather than in an
  -- iterator, so `step*` leaves the `done` branch as a separate goal and `split` separates the
  -- two `cont` branches; the bullets are ordered `cont`, `cont`, `done` to match.
  · rintro ⟨max, i⟩ ⟨hi, hinv, hmem⟩
    simp only at hi hinv hmem -- beta-reduce the `(max, i).1` / `.2` projections
    unfold f_while_loop.body
    step*
    split <;> step*
    · -- cont, `x[i] > max`: accumulator becomes the element just read.
      refine ⟨by scalar_tac, ?_, Or.inr ?_, by scalar_tac⟩
      · simp only [i3_post]
        exact forall_index_succ hinv (by scalar_tac) (by simp_lists [i2_post]; scalar_tac)
      · rw [i2_post]
        exact List.getElem_mem _
    · -- cont, `x[i] ≤ max`: accumulator unchanged.
      refine ⟨by scalar_tac, ?_, hmem, by scalar_tac⟩
      simp only [i3_post]
      exact forall_index_succ hinv (by scalar_tac) (by simp_lists [i2_post]; scalar_tac)
    · -- done: guard false, so `i = x.length` and the invariant is already `post`.
      exact ⟨fun j hj => hinv j (by scalar_tac), hmem⟩
  · -- Entry: the invariant is vacuous at `i = 0`.
    simp

@[step]
theorem f_while_spec : Anodized f_while := by
  intro x _
  simp only [ensures_f_while_iff]
  unfold f_while
  step*
  exact max_spec_of_invariants ‹_› ‹_›
