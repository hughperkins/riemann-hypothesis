module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ConstSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisSlash
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisVan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ModularFormCoefficients
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.TsumNormEisensteinTranslate
import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

private theorem eisChi_coe_sum {N : ℕ} {k : ℤ} {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (F : ι → ModularForm (Gamma1 N) k) :
    ((∑ a ∈ s, c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ) = ∑ a ∈ s, c a • (F a : ℍ → ℂ) := by
  simp only [FunLike.coe_sum, FunLike.coe_smul]

private theorem eisChi_slash_sum {k : ℤ} {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (F : ι → ℍ → ℂ) (γ : SL(2, ℤ)) :
    (∑ a ∈ s, c a • F a) ∣[k] γ = ∑ a ∈ s, c a • (F a ∣[k] γ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, SlashAction.add_slash, ModularForm.SL_smul_slash]

private theorem eisChi_gs {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (e : ZMod N) :
    ∑ a : ZMod N, χ⁻¹ a * (ZMod.stdAddChar (a * e) : ℂ) = χ e * gaussSum χ⁻¹ ZMod.stdAddChar := by
  simpa only [ZMod.dft_apply, mul_neg, neg_neg, smul_eq_mul, inv_inv, mul_comm] using
    hχ.inv.fourierTransform_eq_inv_mul_gaussSum (-e)

theorem UpperTheory.V.Sd.eisChi :
    UpperTheory.V.Sd.EisChi := by
  intro N k _ hN hk χ hχ hpar
  choose F hF using UpperTheory.V.Sd.eisMF N k hk
  have hi : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have hg : gaussSum χ⁻¹ (ZMod.stdAddChar (N := N)) ≠ 0 :=
    fun h0 => by
      have h := gauss_mul_gauss_inv χ⁻¹ hi
      rw [h0, zero_mul, zero_mul] at h
      exact (Nat.cast_ne_zero.2 (NeZero.ne N)) h.symm
  set g := gaussSum χ⁻¹ (ZMod.stdAddChar (N := N)) with hgdef
  haveI : Fact (1 < N) := ⟨hN⟩
  have h0 : χ⁻¹ (0 : ZMod N) = 0 := MulChar.map_nonunit _ not_isUnit_zero
  refine ⟨∑ a : ZMod N, ((2 * g)⁻¹ * χ⁻¹ a) • F a, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    rw [eisChi_coe_sum, eisChi_slash_sum, Finset.smul_sum]
    simp only [hF, UpperTheory.V.Sd.eisSlash N k hk _ γ hγ]
    have hd : IsUnit (((γ 1 1 : ℤ)) : ZMod N) := by
      have h1 := γ.det_coe
      rw [Matrix.det_fin_two] at h1
      have h2 : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.1 hγ
      have h3 := congrArg (Int.cast : ℤ → ZMod N) h1
      push_cast at h3
      rw [h2, mul_zero, sub_zero] at h3
      exact IsUnit.of_mul_eq_one_right _ h3
    obtain ⟨u, hu⟩ := hd
    rw [← hu]
    refine Fintype.sum_equiv (Units.mulRight u) _ _ fun a => ?_
    rw [smul_smul]
    congr 1
    have : χ (u : ZMod N) * χ⁻¹ (u : ZMod N) = 1 := by
      rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
    simp only [Units.mulRight_apply, map_mul]
    linear_combination (-((2 * g)⁻¹ * χ⁻¹ a)) * this
  · intro γ hγ
    rw [eisChi_coe_sum, eisChi_slash_sum]
    refine Submodule.sum_mem (zeroAtImInftySubmodule ℂ) fun a _ => ?_
    by_cases ha : IsUnit a
    · refine Submodule.smul_mem _ _ ?_
      rw [hF]
      exact UpperTheory.V.Sd.eisVan N k hk a ha hN γ hγ
    · rw [MulChar.map_nonunit _ ha, mul_zero, zero_smul]
      exact Submodule.zero_mem _
  · intro n hn
    rw [UpperTheory.V.Sd.modularForm_coef_sum_smul]
    have h1 : ∀ a : ZMod N, (2 * g)⁻¹ * χ⁻¹ a * coef (F a) n = ∑ e ∈ n.divisors, (2 * g)⁻¹ * (e : ℂ) ^ (k - 1) *
        (χ⁻¹ a * (ZMod.stdAddChar (a * (e : ZMod N)) : ℂ) +
          (-1) ^ k * (χ⁻¹ a * (ZMod.stdAddChar (a * (-(e : ZMod N))) : ℂ))) := by
      intro a
      by_cases ha : a = 0
      · simp [ha, h0]
      · rw [hF, (UpperTheory.V.Sd.eisCoef N k hk a ha).2 n hn, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [mul_neg]; ring
    simp only [h1]
    rw [Finset.sum_comm, sigChi]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, eisChi_gs hχ, eisChi_gs hχ, ← hgdef,
      ← neg_one_mul (e : ZMod N), map_mul, hpar]
    have h2 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
    have h3 : (2 * g)⁻¹ * (2 * g) = 1 := inv_mul_cancel₀ (mul_ne_zero two_ne_zero hg)
    linear_combination ((2 * g)⁻¹ * (e : ℂ) ^ (k - 1) * χ (e : ZMod N) * g) * h2 + ((e : ℂ) ^ (k - 1) * χ (e : ZMod N)) * h3
  · rw [UpperTheory.V.Sd.modularForm_coef_sum_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a = 0
    · simp [ha, h0]
    · rw [hF, (UpperTheory.V.Sd.eisCoef N k hk a ha).1]
      have h3 : (2 * g)⁻¹ * (2 * g) = 1 := inv_mul_cancel₀ (mul_ne_zero two_ne_zero hg)
      linear_combination (χ⁻¹ a * Lk k (ZMod.stdAddChar a : ℂ)) * h3
