"""Figure for Dirac 1928: the minimal dimension of the gamma matrices (numpy, matplotlib).

Writes docs/figures/dirac1928_minimal_dimension.png. Exact (Lean): 4 ≤ n for every nonzero
representation and Dirac's 4 × 4 matrices attain it (Dirac1928.isLeast_dim).

Run:  python3 docs/simulation/figures_dirac.py
"""

import matplotlib.pyplot as plt
import numpy as np

from style import BLUE, GRID, INK, INK2, MUTED, ORANGE, OUT, SURFACE


def dirac_gammas():
    i = 1j
    return [np.diag([1, 1, -1, -1]).astype(complex),
            np.array([[0, 0, 0, 1], [0, 0, 1, 0], [0, -1, 0, 0], [-1, 0, 0, 0]], complex),
            np.array([[0, 0, 0, -i], [0, 0, i, 0], [0, i, 0, 0], [-i, 0, 0, 0]]),
            np.array([[0, 0, 1, 0], [0, 0, 0, -1], [-1, 0, 0, 0], [0, 1, 0, 0]], complex)]



def fig_dirac():
    g = dirac_gammas()
    fig = plt.figure(figsize=(12.4, 4.8), dpi=150)
    gs = fig.add_gridspec(2, 6, width_ratios=[2.2, 0.15, 1, 1, 1, 1], hspace=0.45, wspace=0.35)

    ax = fig.add_subplot(gs[:, 0])
    ns = np.arange(1, 7)
    cols = [MUTED if n < 4 else (ORANGE if n == 4 else BLUE) for n in ns]
    ax.bar(ns, ns ** 2, color=cols, width=0.62, zorder=3)
    ax.axhline(16, color=INK2, lw=1.4, ls="--", zorder=4)
    ax.text(0.6, 16.8, "16 independent monomials", color=INK2, fontsize=9.5)
    ax.text(2, 2.8 ** 2 + 1, "n² < 16:\nimpossible", ha="center", color=INK2, fontsize=9.5)
    ax.text(4, 22.5, "attained\n(Dirac)", ha="center", color=ORANGE, fontsize=9.5)
    ax.set_xticks(ns)
    ax.set_xlabel("matrix size  n")
    ax.set_ylabel("dim Matₙ(ℂ) = n²")
    ax.set_ylim(0, 40)
    ax.grid(axis="y", color=GRID, zorder=0)
    ax.set_title("Minimal dimension = 4  (Lean: isLeast_dim)", loc="left", fontsize=11.5)

    for mu in range(4):
        for row, (part, name) in enumerate([(np.real, "Re"), (np.imag, "Im")]):
            cx = fig.add_subplot(gs[row, 2 + mu])
            cx.imshow(part(g[mu]), cmap="RdBu_r", vmin=-1, vmax=1)
            cx.set_xticks([])
            cx.set_yticks([])
            cx.set_title(f"{name} γ{'⁰¹²³'[mu]}", fontsize=10)
            for (r, c), v in np.ndenumerate(part(g[mu])):
                if v != 0:
                    cx.text(c, r, f"{v:+.0f}", ha="center", va="center", fontsize=7.5,
                            color=SURFACE)

    anti = np.array([[np.allclose(g[m] @ g[n] + g[n] @ g[m],
                                  2 * (m == n) * (1 if m == 0 else -1) * np.eye(4))
                      for n in range(4)] for m in range(4)])
    assert anti.all()
    fig.text(0.5, -0.04, "{γ^μ, γ^ν} = 2η^μν · 1,  η = diag(1, −1, −1, −1):  all 16 relations "
             "hold (Lean: diracGamma_clifford, by decide over ℤ[i])", ha="center", color=INK2,
             fontsize=9.5)
    fig.suptitle("Dirac 1928 — no 2 × 2 gamma matrices; the minimum is 4 × 4", x=0.01,
                 ha="left", fontsize=13, color=INK)
    fig.savefig(OUT / "dirac1928_minimal_dimension.png", facecolor=SURFACE, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    fig_dirac()
