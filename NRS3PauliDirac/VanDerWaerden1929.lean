/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# van der Waerden 1929 — the uncertainty cone

Spinor calculus (van der Waerden 1929) rests on one identification: a Hermitian `2 × 2` matrix is
`v₀ 1 + v₁ σ₁ + v₂ σ₂ + v₃ σ₃` for exactly one real four-vector `v`, its determinant is the
Minkowski interval `v₀² − v₁² − v₂² − v₃²`, and `A ↦ M A Mᴴ` with `M ∈ SL(2, ℂ)` is a Lorentz
transformation: it keeps the interval and the future cone.

The Gram matrix of two fluctuation vectors `x = (A − ⟨A⟩)ψ`, `y = (B − ⟨B⟩)ψ` is Hermitian and
positive semidefinite. In the four-vector it carries, `v₁` is the covariance and `v₂` is half the
commutator; Robertson–Schrödinger (1929–30) says that `v` is a future causal vector. Rescaling
`A → λA`, `B → B/λ` keeps `[A, B]` and is the boost `diag(λ, λ⁻¹) ∈ SL(2, ℂ)`, so every ratio
built from the interval and `v₂` carries no units: in NRS³ this is `C_Nava`
(base repository, `D50`).

Over `ℝ` the inner product is real and `v₂ = 0`: without complex numbers there is no commutator
axis. The four components are statistics of the pair, not coordinates of events.

## Main results

- `VanDerWaerden1929.det_herm` : `det (v₀ 1 + v·σ) = v₀² − v₁² − v₂² − v₃²`.
- `VanDerWaerden1929.herm_coords` : every Hermitian `2 × 2` matrix is `v₀ 1 + v·σ`.
- `VanDerWaerden1929.future_of_posSemidef` : positive semidefinite means future causal.
- `VanDerWaerden1929.det_conj`, `VanDerWaerden1929.posSemidef_conj` : `SL(2, ℂ)` keeps the
  interval and the future cone.
- `VanDerWaerden1929.robertsonSchrodinger_future` : the Gram matrix of two vectors is a future
  causal vector.
- `VanDerWaerden1929.gram_boost` : `A → λA`, `B → B/λ` is the boost `diag(λ, λ⁻¹)`.
-/

@[expose] public noncomputable section

namespace VanDerWaerden1929

open Matrix Complex
open scoped ComplexOrder MatrixGroups

/-! ## 1. Hermitian matrices are four-vectors -/

/-- The Minkowski interval `v₀² − v₁² − v₂² − v₃²`. -/
def interval (v : Fin 4 → ℝ) : ℝ := v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2

/-- The matrix `v₀ 1 + v₁ σ₁ + v₂ σ₂ + v₃ σ₃`. -/
def herm (v : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((v 0 + v 3 : ℝ) : ℂ), (v 1 : ℂ) - (v 2 : ℂ) * I;
    (v 1 : ℂ) + (v 2 : ℂ) * I, ((v 0 - v 3 : ℝ) : ℂ)]

/-- The four-vector of a `2 × 2` matrix. -/
def coords (A : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ :=
  ![((A 0 0).re + (A 1 1).re) / 2, (A 1 0).re, (A 1 0).im, ((A 0 0).re - (A 1 1).re) / 2]

theorem herm_isHermitian (v : Fin 4 → ℝ) : (herm v).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [herm]

/-- **The determinant is the interval.** -/
theorem det_herm (v : Fin 4 → ℝ) : (herm v).det = ((interval v : ℝ) : ℂ) := by
  rw [herm, det_fin_two_of, interval]
  push_cast
  linear_combination (v 2 : ℂ) ^ 2 * I_sq

/-- **Every Hermitian matrix is a four-vector.** -/
theorem herm_coords {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.IsHermitian) : herm (coords A) = A := by
  have h00 : (A 0 0).im = 0 := by
    have := congrArg Complex.im (hA.apply 0 0)
    simp at this
    linarith
  have h11 : (A 1 1).im = 0 := by
    have := congrArg Complex.im (hA.apply 1 1)
    simp at this
    linarith
  have h01 : A 0 1 = star (A 1 0) := (hA.apply 0 1).symm
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [herm, coords, h00, h11, h01] <;> ring

/-! ## 2. The future cone -/

/-- **Positive semidefinite means future causal**: `0 ≤ v₀` and `0 ≤ η(v, v)`. -/
theorem future_of_posSemidef {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) :
    0 ≤ coords A 0 ∧ 0 ≤ interval (coords A) := by
  have ht : 0 ≤ (A 0 0).re + (A 1 1).re := by
    simpa [trace_fin_two] using (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hd := (Complex.nonneg_iff.mp hA.det_nonneg).1
  rw [← herm_coords hA.isHermitian, det_herm, ofReal_re] at hd
  exact ⟨by simp only [coords, cons_val_zero]; linarith, hd⟩

/-- **`SL(2, ℂ)` keeps the interval.** -/
theorem det_conj (M : SL(2, ℂ)) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (M.1 * A * M.1ᴴ).det = A.det := by
  simp [det_mul, det_conjTranspose]

/-- **`SL(2, ℂ)` keeps the future cone.** -/
theorem posSemidef_conj (M : SL(2, ℂ)) {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) :
    (M.1 * A * M.1ᴴ).PosSemidef :=
  hA.mul_mul_conjTranspose_same M.1

/-! ## 3. The uncertainty cone -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Robertson–Schrödinger.** The Gram matrix of two vectors is a future causal vector. -/
theorem robertsonSchrodinger_future (x y : E) :
    0 ≤ coords (gram ℂ ![x, y]) 0 ∧ 0 ≤ interval (coords (gram ℂ ![x, y])) :=
  future_of_posSemidef (posSemidef_gram ℂ ![x, y])

/-- The commutator component: `v₂ = Im ⟪y, x⟫`. -/
theorem coords_gram_two (x y : E) : coords (gram ℂ ![x, y]) 2 = (inner ℂ y x).im := rfl

theorem gram_two (x y : E) :
    gram ℂ ![x, y] = !![inner ℂ x x, inner ℂ x y; inner ℂ y x, inner ℂ y y] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The boost `diag(λ, λ⁻¹)`. -/
def boost {l : ℝ} (hl : l ≠ 0) : SL(2, ℂ) :=
  ⟨!![(l : ℂ), 0; 0, (l : ℂ)⁻¹], by
    rw [det_fin_two_of, mul_inv_cancel₀ (by exact_mod_cast hl)]
    ring⟩

/-- **Units are a boost.** `A → λA`, `B → B/λ` acts on the Gram matrix as `diag(λ, λ⁻¹)`. -/
theorem gram_boost (x y : E) {l : ℝ} (hl : l ≠ 0) :
    gram ℂ ![(l : ℂ) • x, (l : ℂ)⁻¹ • y] =
      (boost hl).1 * gram ℂ ![x, y] * (boost hl).1ᴴ := by
  rw [gram_two, gram_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [boost, mul_apply, Fin.sum_univ_two, conjTranspose_apply, of_apply, cons_val',
      cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, Fin.isValue,
      inner_smul_left, inner_smul_right, Complex.star_def, Complex.conj_ofReal, map_inv₀,
      map_zero, mul_zero, zero_mul, add_zero, zero_add, Fin.zero_eta, Fin.mk_one] <;> ring

/-- The interval of the uncertainty vector does not change under the boost. -/
theorem interval_gram_boost (x y : E) {l : ℝ} (hl : l ≠ 0) :
    (gram ℂ ![(l : ℂ) • x, (l : ℂ)⁻¹ • y]).det = (gram ℂ ![x, y]).det := by
  rw [gram_boost x y hl, det_conj]

end VanDerWaerden1929
