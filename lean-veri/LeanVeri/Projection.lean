/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib
/-!
This file extends the file `Mathlib.Analysis.InnerProductSpace.Projection`.
-/

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

lemma Submodule.le_iff_orthogonal_le_orthogonal (K₀ K₁ : Submodule 𝕜 E) [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ ≤ K₁ ↔ K₁ᗮ ≤ K₀ᗮ := by
  apply Iff.intro
  · intro h
    intro x hx
    rw [mem_orthogonal]
    rw [mem_orthogonal] at hx
    intro u hu
    exact hx u (h hu)
  · intro h
    rw [← K₀.orthogonal_orthogonal, ← K₁.orthogonal_orthogonal]
    intro x hx
    rw [mem_orthogonal]
    rw [mem_orthogonal] at hx
    intro u hu
    exact hx u (h hu)

lemma Submodule.orthogonal_le_iff_orthogonal_le (K₀ K₁ : Submodule 𝕜 E) [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ᗮ ≤ K₁ ↔ K₁ᗮ ≤ K₀ := by
  rw [le_iff_orthogonal_le_orthogonal, orthogonal_orthogonal]

lemma Submodule.le_orthogonal_iff_le_orthogonal (K₀ K₁ : Submodule 𝕜 E) [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ ≤ K₁ᗮ ↔ K₁ ≤ K₀ᗮ := by
  rw [le_iff_orthogonal_le_orthogonal, orthogonal_orthogonal]


open Module
lemma Submodule.eq_orthogonal_of_finrank_add_of_orthogonal [FiniteDimensional 𝕜 E]
    (K₀ K₁ : Submodule 𝕜 E) [K₁.HasOrthogonalProjection] (H01 : K₀ ⟂ K₁)
    (hrank : finrank 𝕜 E ≤ finrank 𝕜 K₀ + finrank 𝕜 K₁) : K₀ = K₁ᗮ := by
  suffices finrank 𝕜 K₀ ≥ finrank 𝕜 K₁ᗮ from Submodule.eq_of_le_of_finrank_le H01 this
  have := Submodule.finrank_add_finrank_orthogonal K₁
  omega

lemma Submodule.span_singleton_eq_orthogonal_of_inner_eq_zero [FiniteDimensional 𝕜 E]
    (hdim : Module.finrank 𝕜 E = 2) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : inner 𝕜 x y = 0) :
    (𝕜 ∙ x) = (𝕜 ∙ y)ᗮ := by
  apply eq_orthogonal_of_finrank_add_of_orthogonal (𝕜 ∙ x) (𝕜 ∙ y)
  · rw [isOrtho_span]
    intro u hu v hv
    rw [hu, hv]
    exact hxy
  · rw [hdim, finrank_span_singleton hx, finrank_span_singleton hy]
