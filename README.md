# NRS³ · Dirac

**There are no `2 × 2` gamma matrices; the least dimension is 4** — the algebraic bottleneck that
gave Dirac's equation four components, in Lean 4.

![NRS³ · Dirac](docs/figures/dirac1928_minimal_dimension.png)

## Results

| Statement | Lean |
|---|---|
| a word with an odd number of letters `≠ k` is traceless | `trace_word_eq_zero` |
| the 16 ordered monomials are independent in every nonzero representation | `monomial_linearIndependent` |
| `4 ≤ n` | `four_le_dim` |
| no `2 × 2` gamma matrices | `no_dirac_two_by_two` |
| Dirac's `4 × 4` matrices attain it (checked by `decide` over `ℤ[i]`) | `isLeast_dim` |

## In NRS³

Three anticommuting directions, one per axis of NRS³, fit in `2 × 2` (the Pauli matrices,
`nrs3-pauli`); adding time as a fourth generator forces `4 × 4`.

## History

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

## The mosaic

- [NRS and NRS³ — the base theorem](https://github.com/naype888-cloud/nava-robertson-schrodinger)
- [NRS³ · Cramér–Rao](https://github.com/naype888-cloud/nrs3-cramer-rao)
- [NRS³ · Mandelstam–Tamm](https://github.com/naype888-cloud/nrs3-mandelstam-tamm)
- [NRS³ · Penrose](https://github.com/naype888-cloud/nrs3-penrose)
- **[NRS³ · Dirac](https://github.com/naype888-cloud/nrs3-dirac)** (this one)
- [NRS³ · Pauli](https://github.com/naype888-cloud/nrs3-pauli)
- [NRS³ · Poincaré](https://github.com/naype888-cloud/nrs3-poincare)

## License

NRS Noncommercial License 1.0.0, see [`LICENSE`](LICENSE). Author: Eduardo Nava-Hernandez.
