module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped ModularForm

namespace UpperTheory.V.Sd

variable {N : ℕ} {k : ℤ} {F : Type} [FunLike F ℍ ℂ] [hF : ModularFormClass F (Gamma1 N) k]

include hF in
theorem modularForm_coef_smul (c : ℂ) (f : F) (n : ℕ) :
    coef (c • (f : ℍ → ℂ)) n = c * coef f n := by
  unfold coef
  rw [ModularForm.qExpansion_smul (Γ := (Gamma1 N : Subgroup (GL (Fin 2) ℝ))) one_pos (by simp [strictPeriods_Gamma1]) c f]
  simp

theorem modularForm_coef_sum_smul {I : Type} (s : Finset I) (c : I → ℂ)
    (f : I → ModularForm (Gamma1 N) k) (n : ℕ) :
    coef (∑ i ∈ s, c i • f i : ModularForm (Gamma1 N) k) n = ∑ i ∈ s, c i * coef (f i) n := by
  classical
  unfold coef
  change (ModularForm.qExpansionAddHom one_pos (by simp [strictPeriods_Gamma1]) k
    (∑ i ∈ s, c i • f i)).coeff n = _
  rw [map_sum]
  simp only [map_sum, ModularForm.qExpansionAddHom_apply, FunLike.coe_smul]
  exact Finset.sum_congr rfl fun i _ => modularForm_coef_smul (c i) (f i) n

end UpperTheory.V.Sd
