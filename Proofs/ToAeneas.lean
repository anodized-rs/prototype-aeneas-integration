import Aeneas

/-!
# Lemmas that belong in Aeneas

Gaps in the Aeneas Lean backend that this project ran into, filled here so the proofs can
proceed. Everything in this file is proved, nothing is assumed.

Contents:

* `core.iter.range.IteratorRange.next_Usize_spec_none` — mirrors the existing
  `next_U8_spec_none` in `Aeneas/Std/RangeIter.lean`, whose absence for `Usize` is flagged by a
  note in that file.
-/

namespace Aeneas.Std

open Result core.ops.range WP

/-- Step spec for `IteratorRange.next` on `Range Usize` when the range is exhausted.

`Aeneas/Std/RangeIter.lean` provides `next_Usize_spec` (the `some` case) and `next_U8_spec_none`,
but no `none` case for `Usize`; the note above `next_Usize_spec` says the variant is missing.
Without it, `step*` can only take the `some` branch and so demands the unprovable
`start < end` when a loop reaches its exit test.

Deliberately *not* `@[step]`: it would shadow the `some` spec, which `step*` would then try to
apply in the non-exhausted branch too. Invoke it explicitly with `step with`. -/
theorem core.iter.range.IteratorRange.next_Usize_spec_none
    (range : core.ops.range.Range Usize)
    (hge : range.start.val ≥ range.«end».val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range
    ⦃ (opt : Option Usize) (range' : core.ops.range.Range Usize) =>
      opt = none ∧ range' = range ⦄ := by
  simp only [core.iter.range.IteratorRange.next,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, liftFun2,
    show ¬ (range.start.val < range.«end».val) from by omega]
  simp [WP.spec_ok]

end Aeneas.Std
