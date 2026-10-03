/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3PauliDirac.DiracMinimalDimension
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Weyl and Fock–Ivanenko 1929 — Dirac in curved spacetime

Dirac (1928) took the square root of the Klein–Gordon operator in flat spacetime. In 1929 Weyl
and Fock–Ivanenko carried it to curved spacetime: a tetrad `e` writes the metric at each point
as `g = eᵀ η e`, and the curved gamma matrices are `Γ_μ = e^a_μ γ_a`. Space, time and gravity
then enter one algebraic relation,

  `Γ_μ Γ_ν + Γ_ν Γ_μ = 2 g_μν`,

and the Dirac symbol `Γ(p) = p^μ Γ_μ` is the square root of the metric:

  `(Γ(p) − m)(Γ(p) + m) = (g(p, p) − m²) · 1`.

Klein–Gordon factors into Dirac at every point of a curved spacetime. Here the metric is a
fixed background at one point: the statements are algebraic and say nothing about how matter
curves spacetime.

The tetrad is invertible, so the flat matrices `γ_a = (e⁻¹)^μ_a Γ_μ` are recovered from the
curved ones, and Dirac's minimal dimension 4 survives gravity unchanged.

## Main results

- `Dirac1929.IsClifford.transform` : a change of frame `P` carries `g` to `Pᵀ g P`.
- `Dirac1929.IsClifford.symbol_mul_self` : `Γ(p)² = g(p, p) · 1`.
- `Dirac1929.IsClifford.dirac_factorization` : `(Γ(p) − m)(Γ(p) + m) = (g(p, p) − m²) · 1`.
- `Dirac1929.tetrad_isClifford` : `Γ_μ = e^a_μ γ_a` satisfies the curved relation for `eᵀ η e`.
- `Dirac1929.four_le_dim` : every nonzero curved representation has `4 ≤ n`.
- `Dirac1929.isLeast_dim` : for every invertible tetrad the minimal dimension is still 4.
-/

@[expose] public noncomputable section

namespace Dirac1929

open Matrix Dirac1928

variable {n : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- The Clifford relation `{Γ_μ, Γ_ν} = 2 g_μν · 1` for a bilinear form `g`. -/
def IsClifford (g : Matrix κ κ ℂ) (Γ : κ → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ μ ν, Γ μ * Γ ν + Γ ν * Γ μ = (2 * g μ ν) • (1 : Matrix (Fin n) (Fin n) ℂ)

/-- The Minkowski form `η = diag(1, −1, −1, −1)`. -/
def minkowski : Matrix (Fin 4) (Fin 4) ℂ := diagonal eta

/-- The Dirac symbol `Γ(p) = p^μ Γ_μ`. -/
def symbol (Γ : κ → Matrix (Fin n) (Fin n) ℂ) (p : κ → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ μ, p μ • Γ μ

/-- The curved gamma matrices `Γ_μ = e^a_μ γ_a` of a tetrad `e`. -/
def tetradGamma (e : Matrix (Fin 4) (Fin 4) ℂ) (γ : Fin 4 → Matrix (Fin n) (Fin n) ℂ)
    (μ : Fin 4) : Matrix (Fin n) (Fin n) ℂ :=
  symbol γ fun a => e a μ

theorem isClifford_minkowski_iff (γ : Fin 4 → Matrix (Fin n) (Fin n) ℂ) :
    IsClifford minkowski γ ↔ CliffordRelation γ := by
  refine forall₂_congr fun μ ν => ?_
  by_cases h : μ = ν <;> simp [minkowski, h]

omit [Fintype ι] in
theorem congr_apply (P : Matrix κ ι ℂ) (g : Matrix κ κ ℂ) (a b : ι) :
    (Pᵀ * g * P) a b = ∑ μ, ∑ ν, P μ a * P ν b * g μ ν := by
  simp only [mul_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable {g : Matrix κ κ ℂ} {Γ : κ → Matrix (Fin n) (Fin n) ℂ}

omit [Fintype ι] in
/-- **Change of frame**: `Γ'_a = P^μ_a Γ_μ` satisfies the relation for `Pᵀ g P`. -/
theorem IsClifford.transform (hΓ : IsClifford g Γ) (P : Matrix κ ι ℂ) :
    IsClifford (Pᵀ * g * P) fun a => symbol Γ fun μ => P μ a := by
  intro a b
  calc _ = ∑ μ, ∑ ν, (P μ a * P ν b) • (Γ μ * Γ ν + Γ ν * Γ μ) := by
          simp only [symbol, Finset.sum_mul_sum, smul_mul_smul_comm, smul_add,
            Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_comm]
          simp only [mul_comm]
    _ = (2 * (Pᵀ * g * P) a b) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
          simp only [congr_apply, Finset.mul_sum, Finset.sum_smul]
          refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
          rw [hΓ, smul_smul]
          ring_nf

/-- **The Dirac symbol is the square root of the metric**: `Γ(p)² = g(p, p) · 1`. -/
theorem IsClifford.symbol_mul_self (hΓ : IsClifford g Γ) (p : κ → ℂ) :
    symbol Γ p * symbol Γ p = (p ⬝ᵥ g *ᵥ p) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have h := hΓ.transform (ι := Unit) (of fun μ (_ : Unit) => p μ) () ()
  rw [← two_smul ℂ (_ * _), mul_smul] at h
  have h' := smul_right_injective _ two_ne_zero h
  simp only [congr_apply, of_apply] at h'
  convert h' using 2
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Klein–Gordon factors into Dirac in curved spacetime**:
`(Γ(p) − m)(Γ(p) + m) = (g(p, p) − m²) · 1`. -/
theorem IsClifford.dirac_factorization (hΓ : IsClifford g Γ) (p : κ → ℂ) (m : ℂ) :
    (symbol Γ p - m • 1) * (symbol Γ p + m • 1) =
      (p ⬝ᵥ g *ᵥ p - m ^ 2) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [sub_mul, mul_add, hΓ.symbol_mul_self, Matrix.mul_smul, Matrix.smul_mul, mul_one,
    one_mul, smul_smul, sub_smul]
  abel_nf
  simp [sq]

/-- **Gravity enters through the tetrad**: `Γ_μ = e^a_μ γ_a` satisfies the curved relation for
the metric `g = eᵀ η e`. -/
theorem tetrad_isClifford {γ : Fin 4 → Matrix (Fin n) (Fin n) ℂ} (hγ : CliffordRelation γ)
    (e : Matrix (Fin 4) (Fin 4) ℂ) :
    IsClifford (eᵀ * minkowski * e) (tetradGamma e γ) :=
  ((isClifford_minkowski_iff γ).mpr hγ).transform e

/-- **Every nonzero curved representation has `4 ≤ n`**: the flat matrices are recovered with
the inverse tetrad. -/
theorem four_le_dim {e : Matrix (Fin 4) (Fin 4) ℂ} (he : IsUnit e.det)
    {Γ : Fin 4 → Matrix (Fin n) (Fin n) ℂ} (hΓ : IsClifford (eᵀ * minkowski * e) Γ)
    (hn : 0 < n) : 4 ≤ n := by
  have h := hΓ.transform e⁻¹
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, Matrix.mul_assoc,
    mul_nonsing_inv _ he, transpose_one, Matrix.one_mul, Matrix.mul_one] at h
  exact Dirac1928.four_le_dim ((isClifford_minkowski_iff _).mp h) hn

/-- **Gravity does not change Dirac's 4**: for every invertible tetrad, the minimal complex
dimension of the curved Dirac algebra is 4. -/
theorem isLeast_dim {e : Matrix (Fin 4) (Fin 4) ℂ} (he : IsUnit e.det) :
    IsLeast {n | 0 < n ∧ ∃ Γ : Fin 4 → Matrix (Fin n) (Fin n) ℂ,
      IsClifford (eᵀ * minkowski * e) Γ} 4 :=
  ⟨⟨by norm_num, _, tetrad_isClifford diracGamma_clifford e⟩,
    fun _ ⟨hn, _, hΓ⟩ => four_le_dim he hΓ hn⟩

end Dirac1929
