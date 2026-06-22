import examples.e01.translation.Funs

open Aeneas Std.Result
open e01

theorem f2_anodized_spec (_ : __anodized_fn_requires_f2 = ok true) :
  f2 ⦃ result =>
    __anodized_fn_ensures_f2 result = ok true⦄ := by
  unfold f2 __anodized_fn_ensures_f2 __anodized_fn_ensures_f2.closure.Insts.CoreOpsFunctionFnTupleSharedU8Bool.call
  step*
