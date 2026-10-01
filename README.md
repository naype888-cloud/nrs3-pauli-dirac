# NRS³ · Pauli–Dirac

**Two fermions cannot share a state, `2 × 2` holds exactly three anticommuting spin matrices, and
adding time forces `4 × 4`** — Pauli 1925–27 and Dirac 1928 in Lean 4.

**[▶ Try it: spin, exclusion, shells and Dirac's table, live](https://naype888-cloud.github.io/nrs3-pauli-dirac/)**

![NRS³ · Pauli–Dirac](docs/figures/pauli1925.png)

## Results

### Pauli 1925–27

| Statement | Lean |
|---|---|
| an antisymmetric amplitude vanishes when both particles share a state | `antisymm_apply_self` |
| `ψ ∧ ψ = 0` | `antisymmetrize_self` |
| shells: `∑_{l<n} 2(2l + 1) = 2n²` (2, 8, 18, 32) | `shell_card` |
| `σ_a σ_b + σ_b σ_a = 2δ_ab`, `σ_x σ_y = iσ_z` (by `decide` over `ℤ[i]`) | `sigma_anticomm`, `sigma_mul` |
| no four anticommuting involutions in `Mat₂(ℂ)` | `no_four_anticommuting` |

The shell numbers are capacities, not the lengths of the periods of the table, which also depend
on the energy ordering of subshells.

### Dirac 1928

| Statement | Lean |
|---|---|
| a word with an odd number of letters `≠ k` is traceless | `trace_word_eq_zero` |
| the 16 ordered monomials are independent in every nonzero representation | `monomial_linearIndependent` |
| `4 ≤ n` | `four_le_dim` |
| no `2 × 2` gamma matrices | `no_dirac_two_by_two` |
| Dirac's `4 × 4` matrices attain it (checked by `decide` over `ℤ[i]`) | `isLeast_dim` |

![Dirac 1928](docs/figures/dirac1928_minimal_dimension.png)

## In NRS³

NRS³ has three axes; spin has three generators, one per axis, and `2 × 2` has room for exactly
three (`no_four_anticommuting`). A fourth generator, time, forces `4 × 4` (`isLeast_dim`).

## History

Pauli stated exclusion in 1925, as two electrons never sharing all four quantum numbers, which
explained the closing of the shells; the antisymmetric form came with Heisenberg and Dirac
(1926), and the spin matrices with Pauli (1927). Everything here could have been stated then;
the proofs use modern tools.

Dirac (1928) needed four matrices with `{γ^μ, γ^ν} = 2η^{μν}` to take the square root of the
Klein–Gordon operator; the trace argument here is the standard one, with no faithfulness
assumption.

## Build

Lean 4 `v4.34.0`, Mathlib `v4.34.0`, nothing else.

```bash
lake exe cache get
lake build
lake env lean Verification/Axioms.lean   # only propext, Classical.choice, Quot.sound
```

Every file: no `sorry`, lines of at most 100 characters, English headers.

## Timeline 1911–1945

NRS answers a question of the Solvay era with later tools. The series is placed in that window:
what falls inside it is the history the theorem belongs to; what falls after it is a proposal,
not part of NRS³.

| Year | Event | Repository |
|---|---|---|
| 1911 | First Solvay conference: radiation and the quanta | |
| 1911–12 | Poincaré: Planck's law forces discrete levels | [`nrs3-poincare`](https://github.com/naype888-cloud/nrs3-poincare) |
| 1915–20 | Szegő: limit theorems for Toeplitz matrices (the limit `C∞`, `D8`) | [base repository (NRS, NRS³)](https://github.com/naype888-cloud/nava-robertson-schrodinger) |
| 1925–27 | Pauli: exclusion, shells `2n²`, spin matrices | **[`nrs3-pauli-dirac`](https://github.com/naype888-cloud/nrs3-pauli-dirac)** (this one) |
| 1927 | Heisenberg's relation; fifth Solvay conference: electrons and photons | |
| 1928 | Dirac: the `4 × 4` gamma matrices | **[`nrs3-pauli-dirac`](https://github.com/naype888-cloud/nrs3-pauli-dirac)** (this one) |
| **1929–30** | **Robertson and Schrödinger: the uncertainty inequality** | **[base repository (NRS, NRS³)](https://github.com/naype888-cloud/nava-robertson-schrodinger)** |
| 1945–46 | Mandelstam–Tamm: the time–energy bound; Rao (1945), Cramér (1946) | [`nrs3-mandelstam-tamm-cramer-rao`](https://github.com/naype888-cloud/nrs3-mandelstam-tamm-cramer-rao) |

**Tools from after the window.** Niven (1956: rational values of the trigonometric functions),
Fiedler (1973: algebraic connectivity), Lean 4 and Mathlib (the verification). The question is
of 1929; the tools are later; the checking is of 2026.

**After the window: proposals, not NRS³.** [`nrs3-penrose`](https://github.com/naype888-cloud/nrs3-penrose) (Penrose 1996, gravity-related
collapse) and [`nrs3-rovelli-lqg`](https://github.com/naype888-cloud/nrs3-rovelli-lqg) (loop quantum gravity, area spectrum 1995). They use NRS³ results
but their physical readings belong to quantum information and quantum gravity.
[`nrs3-defect-curvature`](https://github.com/naype888-cloud/nrs3-defect-curvature) restates base theorems (`D16`–`D16i`); its Bekenstein–Hawking (1973–75) reading
is a declared bridge.

## The mosaic

- [NRS and NRS³ — the base theorem](https://github.com/naype888-cloud/nava-robertson-schrodinger)
- [NRS³ · Mandelstam–Tamm and Cramér–Rao](https://github.com/naype888-cloud/nrs3-mandelstam-tamm-cramer-rao)
- [NRS³ · Penrose](https://github.com/naype888-cloud/nrs3-penrose) (proposal)
- **[NRS³ · Pauli–Dirac](https://github.com/naype888-cloud/nrs3-pauli-dirac)** (this one)
- [NRS³ · Poincaré](https://github.com/naype888-cloud/nrs3-poincare)
- [NRS³ · Defect and curvature](https://github.com/naype888-cloud/nrs3-defect-curvature)
- [NRS³ · Rovelli — Loop Quantum Gravity](https://github.com/naype888-cloud/nrs3-rovelli-lqg) (proposal)

## License

NRS Noncommercial License 1.0.0, see [`LICENSE`](LICENSE). Author: Eduardo Nava-Hernandez.
