/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.LinearCombination

/-!
# Pauli 1925–27 — exclusion, the shells `2n²` and the spin matrices

What Pauli could settle in his own setting, with modern tools.

* **Exclusion (1925).** A two-particle amplitude that is antisymmetric under exchange vanishes
  when both particles sit in the same state; the antisymmetrized product of a state with itself
  is zero. With two spin values per orbital, the shell `n` holds `∑_{l<n} 2(2l + 1) = 2n²`
  electrons: `2, 8, 18, 32`.
* **Spin matrices (1927).** The three Pauli matrices anticommute, square to `1` and multiply
  cyclically, `σ₁σ₂ = iσ₃`; checked by `decide` over `ℤ[i]`. Three is the most `2 × 2` can hold:
  four anticommuting involutions would give five trace-orthogonal matrices in a space of
  dimension 4. Three generators, one per axis, as the three axes of NRS³.

## Main results

- `Pauli1925.antisymm_apply_self`, `Pauli1925.antisymmetrize_self` : exclusion.
- `Pauli1925.shell_card` : `∑_{l<n} 2(2l + 1) = 2n²`.
- `Pauli1925.sigma_anticomm`, `Pauli1925.sigma_mul` : the Pauli algebra.
- `Pauli1925.no_four_anticommuting` : no four anticommuting involutions in `Mat₂(ℂ)`.
-/

@[expose] public noncomputable section

namespace Pauli1925

open Matrix

/-! ## Exclusion -/

/-- **Exclusion**: an antisymmetric amplitude vanishes when both particles share a state. -/
theorem antisymm_apply_self {ι : Type*} (f : ι → ι → ℂ) (hf : ∀ i j, f j i = -f i j) (i : ι) :
    f i i = 0 := by
  have := hf i i
  linear_combination this / 2

/-- The antisymmetrized product `ψ ∧ φ`. -/
def antisymmetrize {ι : Type*} (ψ φ : ι → ℂ) (i j : ι) : ℂ := ψ i * φ j - ψ j * φ i

theorem antisymmetrize_swap {ι : Type*} (ψ φ : ι → ℂ) (i j : ι) :
    antisymmetrize ψ φ j i = -antisymmetrize ψ φ i j := by
  simp only [antisymmetrize]; ring

/-- Two fermions cannot be prepared in the same state: `ψ ∧ ψ = 0`. -/
theorem antisymmetrize_self {ι : Type*} (ψ : ι → ℂ) : antisymmetrize ψ ψ = 0 := by
  funext i j; simp only [antisymmetrize, Pi.zero_apply]; ring

/-- **The shells**: `2(2l + 1)` states per subshell `l`, `2n²` per shell `n`. -/
theorem shell_card (n : ℕ) : ∑ l ∈ Finset.range n, 2 * (2 * l + 1) = 2 * n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-! ## The Pauli matrices -/

/-- The Pauli matrices over `ℤ[i]`. -/
def sigmaZ : Fin 3 → Matrix (Fin 2) (Fin 2) GaussianInt :=
  let i : GaussianInt := ⟨0, 1⟩
  ![!![0, 1; 1, 0], !![0, -i; i, 0], !![1, 0; 0, -1]]

theorem sigmaZ_anticomm (a b : Fin 3) :
    sigmaZ a * sigmaZ b + sigmaZ b * sigmaZ a = diagonal fun _ => if a = b then 2 else 0 := by
  revert a b; decide +kernel

theorem sigmaZ_mul : sigmaZ 0 * sigmaZ 1 = (⟨0, 1⟩ : GaussianInt) • sigmaZ 2 ∧
    sigmaZ 1 * sigmaZ 2 = (⟨0, 1⟩ : GaussianInt) • sigmaZ 0 ∧
    sigmaZ 2 * sigmaZ 0 = (⟨0, 1⟩ : GaussianInt) • sigmaZ 1 := by
  decide +kernel

/-- The Pauli matrices `σ₁, σ₂, σ₃` in `Mat₂(ℂ)`. -/
def sigma (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := GaussianInt.toComplex.mapMatrix (sigmaZ a)

theorem sigma_anticomm (a b : Fin 3) :
    sigma a * sigma b + sigma b * sigma a = (if a = b then 2 else 0 : ℂ) • 1 := by
  have h := congrArg GaussianInt.toComplex.mapMatrix (sigmaZ_anticomm a b)
  simp only [map_add, map_mul, RingHom.mapMatrix_apply, diagonal_map (map_zero _)] at h
  simp only [sigma, RingHom.mapMatrix_apply]
  rw [h, smul_one_eq_diagonal]
  congr 1; funext; split_ifs <;> simp [map_ofNat]

theorem toComplex_i : GaussianInt.toComplex ⟨0, 1⟩ = Complex.I := by
  simp [GaussianInt.toComplex_def]

/-- **The cyclic products**: `σ₁σ₂ = iσ₃`, `σ₂σ₃ = iσ₁`, `σ₃σ₁ = iσ₂`. -/
theorem sigma_mul : sigma 0 * sigma 1 = Complex.I • sigma 2 ∧
    sigma 1 * sigma 2 = Complex.I • sigma 0 ∧ sigma 2 * sigma 0 = Complex.I • sigma 1 := by
  obtain ⟨h1, h2, h3⟩ := sigmaZ_mul
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [sigma, sigma, sigma, ← map_mul]
    first | rw [h1] | rw [h2] | rw [h3]
    ext i j
    simp [RingHom.mapMatrix_apply, toComplex_i]

/-! ## Three is the most `2 × 2` can hold -/

section NoFour

variable {τ : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ}
  (hτ : ∀ a b, τ a * τ b + τ b * τ a = (if a = b then 2 else 0 : ℂ) • 1)
include hτ

theorem trace_mul (a b : Fin 4) : (τ a * τ b).trace = if a = b then 2 else 0 := by
  have h := congrArg trace (hτ a b)
  rw [trace_add, trace_mul_comm (τ b), trace_smul, trace_one, Fintype.card_fin] at h
  split_ifs at h ⊢ <;> push_cast at h <;> linear_combination h / 2

theorem trace_eq_zero (a : Fin 4) : (τ a).trace = 0 := by
  obtain ⟨b, hb⟩ : ∃ b, b ≠ a := exists_ne a
  have hsq : τ b * τ b = 1 := by
    have := hτ b b; simp only [↓reduceIte] at this
    rw [← two_smul ℂ (τ b * τ b)] at this
    exact smul_right_injective _ two_ne_zero (this.trans (by simp))
  have hanti : τ b * τ a = -(τ a * τ b) := by
    have := hτ b a; simp only [hb, ↓reduceIte, zero_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  have h : (τ b * τ a * τ b).trace = -(τ a).trace := by
    rw [hanti, neg_mul, mul_assoc, hsq, mul_one, trace_neg]
  rw [mul_assoc, trace_mul_comm, mul_assoc, hsq, mul_one] at h
  linear_combination h / 2

/-- **No four anticommuting involutions in `Mat₂(ℂ)`.** -/
theorem no_four_anticommuting : False := by
  let v : Option (Fin 4) → Matrix (Fin 2) (Fin 2) ℂ := fun o => o.elim 1 τ
  have hpair (b x : Option (Fin 4)) : (v b * v x).trace = if b = x then 2 else 0 := by
    cases b <;> cases x <;> simp [v, trace_eq_zero hτ, trace_mul hτ]
  have hli : LinearIndependent ℂ v := by
    refine Fintype.linearIndependent_iff.mpr fun c hc b => ?_
    have := congrArg (fun M => (v b * M).trace) hc
    simp only [Finset.mul_sum, mul_smul_comm, trace_sum, trace_smul, hpair, smul_eq_mul,
      mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, trace_zero] at this
    simpa using this
  have h := hli.fintype_card_le_finrank
  simp [Module.finrank_matrix] at h

end NoFour

end Pauli1925
