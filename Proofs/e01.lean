import examples.e01.translation.Funs
import Proofs.Anodized

open Aeneas Std.Result
open e01

register_anodized_simps

theorem f2_spec : Anodized f2 := by
  intro _
  unfold f2
  step*

theorem f4_spec : Anodized f4 := by
  intro x hx
  -- precondition `x > 0`
  simp only [step_simps] at hx
  unfold f4
  step*
