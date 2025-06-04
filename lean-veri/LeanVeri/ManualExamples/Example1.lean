/-
Copyright (c) 2025 Iván Renison, Jam Khan. All rights reserved.
Authors: Iván Renison, Jam Khan
-/
import LeanVeri.Commons
import LeanVeri.LinearMapPropositions
import LeanVeri.OuterProduct
import LeanVeri.ProjectionSubmodule
import Mathlib.Analysis.InnerProductSpace.Trace

variable {𝕜 : Type*} [RCLike 𝕜]
local notation "𝕜²" => EuclideanSpace 𝕜 (Fin 2)


lemma trace_eq (T : 𝕜² →ₗ[𝕜] 𝕜²) : LinearMap.trace 𝕜 𝕜² T = inner 𝕜 ket0 (T ket0) + inner 𝕜 ket1 (T ket1) := by
  rw [T.trace_eq_sum_inner stOrthonormalBasis, Fin.sum_univ_two, stOrthonormalBasis_eq_stBasis_val]
  simp only [stBasis_val]

lemma LinearMap.isDensityOperator.eq_ketbraP_of_toSubmodule_le_toSubmodule_ketbraP {T : 𝕜² →ₗ[𝕜] 𝕜²}
  (hT : T.isDensityOperator) (hT' : T.toSubmodule ≤ ketbraP.toSubmodule) :
    T = ketbraP := sorry


lemma obligation1 (T : 𝕜² →ₗ[𝕜] 𝕜²) (hT : T.isDensityOperator) (hT' : T.toSubmodule ≤ ketbraP.toSubmodule) :
    LinearMap.trace 𝕜 𝕜² (ketbra0 * T) = 1/2 := by
  calc
    (LinearMap.trace 𝕜 𝕜²) (ketbra0 * T)
      = (LinearMap.trace 𝕜 𝕜²) (ketbra0 * ketbraP) := by rw [hT.eq_ketbraP_of_toSubmodule_le_toSubmodule_ketbraP hT']
    _ = inner 𝕜 ket0 ((ketbra0 * ketbraP :  𝕜² →ₗ[𝕜] 𝕜²) ket0) + inner 𝕜 ket1 ((ketbra0 * ketbraP :  𝕜² →ₗ[𝕜] 𝕜²) ket1):= by rw [trace_eq]
    _ = inner 𝕜 ket0 (ketbra0 (ketbraP ket0)) + inner 𝕜 ket1 (ketbra0 (ketbraP ket1)) := rfl
    _ = inner 𝕜 ket0 (ketbra0 ((1 / √2 : 𝕜) • ketP)) + inner 𝕜 ket1 (ketbra0 ((1 / √2 : 𝕜) • ketP)) := by rw [ketbraP_ket0_eq_smul_ketP, ketbraP_ket1_eq_smul_ketP]
    _ = inner 𝕜 ket0 ((1 / √2 : 𝕜) • ketbra0 ketP) + inner 𝕜 ket1 ((1 / √2 : 𝕜) • ketbra0 ketP) := by rw [map_smul]
    _ = inner 𝕜 ket0 ((1 / √2 : 𝕜) • ((1 / √2 : 𝕜) • ket0)) + inner 𝕜 ket1 ((1 / √2 : 𝕜) • ((1 / √2 : 𝕜) • ket0)) := by rw [ketbra0_ketP_eq_smul_ket0]
    _ = inner 𝕜 ket0 (((1 / √2 : 𝕜) * (1 / √2 : 𝕜)) • ket0 : 𝕜²) + inner 𝕜 ket1 (((1 / √2 : 𝕜) * (1 / √2 : 𝕜)) • ket0 : 𝕜²) := by rw [mul_smul]
    _ = inner 𝕜 ket0 ((1/2 : 𝕜) • ket0 : 𝕜²) + inner 𝕜 ket1 ((1/2 : 𝕜) • ket0 : 𝕜²) := by rw [show (1 / √2 : 𝕜) * (1 / √2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]]
    _ = (1/2 : 𝕜) * inner 𝕜 (E := 𝕜²) ket0 ket0 + (1/2 : 𝕜) * inner 𝕜 (E := 𝕜²) ket1 ket0 := by repeat rw [inner_smul_right]
    _ = (1/2 : 𝕜) * 1 + (1/2 : 𝕜) * 0 := by rw [inner_ket0_ket0, inner_ket1_ket0]
    _ = 1/2 := by ring

lemma obligation2 (T : 𝕜² →ₗ[𝕜] 𝕜²) (hT : T.isDensityOperator) (hT' : T.toSubmodule ≤ ketbraP.toSubmodule) :
    LinearMap.trace 𝕜 𝕜² (ketbra1 * T) = 1/2 := by
  calc
    (LinearMap.trace 𝕜 𝕜²) (ketbra1 * T)
      = (LinearMap.trace 𝕜 𝕜²) (ketbra1 * ketbraP) := by rw [hT.eq_ketbraP_of_toSubmodule_le_toSubmodule_ketbraP hT']
    _ = inner 𝕜 ket0 ((ketbra1 * ketbraP :  𝕜² →ₗ[𝕜] 𝕜²) ket0) + inner 𝕜 ket1 ((ketbra1 * ketbraP :  𝕜² →ₗ[𝕜] 𝕜²) ket1):= by rw [trace_eq]
    _ = inner 𝕜 ket0 (ketbra1 (ketbraP ket0)) + inner 𝕜 ket1 (ketbra1 (ketbraP ket1)) := rfl
    _ = inner 𝕜 ket0 (ketbra1 ((1 / √2 : 𝕜) • ketP)) + inner 𝕜 ket1 (ketbra1 ((1 / √2 : 𝕜) • ketP)) := by rw [ketbraP_ket0_eq_smul_ketP, ketbraP_ket1_eq_smul_ketP]
    _ = inner 𝕜 ket0 ((1 / √2 : 𝕜) • ketbra1 ketP) + inner 𝕜 ket1 ((1 / √2 : 𝕜) • ketbra1 ketP) := by rw [map_smul]
    _ = inner 𝕜 ket0 ((1 / √2 : 𝕜) • ((1 / √2 : 𝕜) • ket1)) + inner 𝕜 ket1 ((1 / √2 : 𝕜) • ((1 / √2 : 𝕜) • ket1)) := by rw [ketbra1_ketP_eq_smul_ket1]
    _ = inner 𝕜 ket0 (((1 / √2 : 𝕜) * (1 / √2 : 𝕜)) • ket1 : 𝕜²) + inner 𝕜 ket1 (((1 / √2 : 𝕜) * (1 / √2 : 𝕜)) • ket1 : 𝕜²) := by rw [mul_smul]
    _ = inner 𝕜 ket0 ((1/2 : 𝕜) • ket1 : 𝕜²) + inner 𝕜 ket1 ((1/2 : 𝕜) • ket1 : 𝕜²) := by rw [show (1 / √2 : 𝕜) * (1 / √2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]]
    _ = (1/2 : 𝕜) * inner 𝕜 (E := 𝕜²) ket0 ket1 + (1/2 : 𝕜) * inner 𝕜 (E := 𝕜²) ket1 ket1 := by repeat rw [inner_smul_right]
    _ = (1/2 : 𝕜) * 0 + (1/2 : 𝕜) * 1 := by rw [inner_ket0_ket1, inner_ket1_ket1]
    _ = 1/2 := by ring
