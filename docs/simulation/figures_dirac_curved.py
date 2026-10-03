"""Figure for Dirac1929: Dirac in curved spacetime (numpy, matplotlib).

Writes docs/figures/dirac1929_curved.png.

Left: the mass shell g(p, p) = m² in the (p⁰, p¹) plane for the flat metric η and for three
tetrads (a shift, a lapse, a shear; a pure boost leaves η unchanged); on each shell Γ(p) = p^μ Γ_μ has the eigenvalues ±m, so
Γ(p) − m is singular there and nowhere else (det(Γ(p) − m) = (g(p, p) − m²)², computed).
Middle and right: for random tetrads, the largest entry of {Γ_μ, Γ_ν} − 2g_μν (numerical
round-off) and the rank of the 16 ordered monomials of the Γ_μ: 16 for every invertible tetrad, so n² ≥ 16 and
n ≥ 4; a singular tetrad (one row zero) drops it to 8.

Exact (Lean, Dirac1929): IsClifford.dirac_factorization, tetrad_isClifford, isLeast_dim.

Run:  python3 docs/simulation/figures_dirac_curved.py
"""

from itertools import combinations

import matplotlib.pyplot as plt
import numpy as np

from figures_dirac import dirac_gammas
from style import BLUE, INK, INK2, MUTED, ORANGE, OUT, SURFACE

ETA = np.diag([1.0, -1, -1, -1])
GAMMA = dirac_gammas()


def curved(e):
    """Γ_μ = e^a_μ γ_a and g = eᵀ η e."""
    return [sum(e[a, mu] * GAMMA[a] for a in range(4)) for mu in range(4)], e.T @ ETA @ e


def clifford_error(e):
    gam, g = curved(e)
    return max(np.abs(gam[m] @ gam[v] + gam[v] @ gam[m] - 2 * g[m, v] * np.eye(4)).max()
               for m in range(4) for v in range(4))


def monomial_rank(e):
    gam, _ = curved(e)
    mons = []
    for k in range(5):
        for s in combinations(range(4), k):
            m = np.eye(4, dtype=complex)
            for i in s:
                m = m @ gam[i]
            mons.append(m.ravel())
    return np.linalg.matrix_rank(np.array(mons), tol=1e-9)


def fig_dirac_curved():
    lapse = np.diag([1.6, 1, 1, 1])
    shift = np.eye(4)
    shift[0, 1] = 0.6
    shear = np.eye(4)
    shear[1, 0] = 0.7
    frames = [("flat η", np.eye(4), INK), ("shift 0.6", shift, BLUE),
              ("lapse 1.6", lapse, ORANGE), ("shear 0.7", shear, MUTED)]
    m = 1.0
    fig, (ax, bx, cx) = plt.subplots(1, 3, figsize=(14.2, 4.9), dpi=150,
                                     gridspec_kw={"width_ratios": [1.15, 1, 0.62]})

    p0, p1 = np.meshgrid(np.linspace(-3, 3, 600), np.linspace(-3, 3, 600))
    for name, e, c in frames:
        g = e.T @ ETA @ e
        q = g[0, 0] * p0 ** 2 + 2 * g[0, 1] * p0 * p1 + g[1, 1] * p1 ** 2
        ax.contour(p0, p1, q - m ** 2, levels=[0], colors=[c], linewidths=2 if c == INK else 1.6)
        ax.plot([], [], color=c, lw=2, label=name)
    gam, _ = curved(shift)
    worst = 0.0
    for t in np.linspace(-1.1, 1.1, 9):
        pp = np.linalg.solve(shift, np.array([np.cosh(t), np.sinh(t), 0, 0]) * m)
        G = sum(pp[mu] * gam[mu] for mu in range(4))
        worst = max(worst, abs(np.linalg.det(G - m * np.eye(4))))
        ax.plot(pp[0], pp[1], "o", color=BLUE, ms=4.5, mec=SURFACE, mew=0.8, zorder=4)
    ax.text(-2.9, -2.85, f"dots: |det(Γ(p) − m)| ≤ {worst:.0e} on the shifted shell",
            color=INK2, fontsize=8.8)
    ax.set_xlim(-3, 3)
    ax.set_ylim(-3, 3)
    ax.set_aspect("equal")
    ax.set_xlabel("p⁰")
    ax.set_ylabel("p¹")
    ax.legend(loc="upper center", fontsize=8.6, framealpha=0.95, ncol=4,
              title="mass shell g(p, p) = m² for the tetrad", title_fontsize=8.6,
              bbox_to_anchor=(0.5, 1.0))
    ax.set_title("(Γ(p) − m)(Γ(p) + m) = (g(p, p) − m²)·1", loc="left", fontsize=11.5)

    rng = np.random.default_rng(1929)
    errs, ranks = [], []
    for _ in range(400):
        e = rng.normal(size=(4, 4))
        errs.append(clifford_error(e))
        ranks.append(monomial_rank(e))
    sing = []
    for _ in range(40):
        e = rng.normal(size=(4, 4))
        e[3] = 0
        sing.append(monomial_rank(e))
    bx.hist(np.log10(np.maximum(errs, 1e-17)), bins=20, color=BLUE, alpha=0.85)
    bx.set_xlabel("log₁₀ max |{Γ_μ, Γ_ν} − 2g_μν|")
    bx.set_ylabel("random tetrads (of 400)")
    bx.set_title("{Γ_μ, Γ_ν} = 2g_μν: round-off only", loc="left", fontsize=11.5)

    cx.bar([0, 1], [np.mean(ranks), np.mean(sing)], color=[BLUE, ORANGE], width=0.6)
    cx.axhline(16, color=INK, lw=0.9, ls=":")
    cx.set_xticks([0, 1], ["invertible\n(400)", "singular\n(40)"])
    cx.set_yticks([0, 4, 8, 12, 16])
    cx.set_ylim(0, 18.5)
    for x, r in [(0, ranks), (1, sing)]:
        cx.text(x, np.mean(r) + 0.4, f"{min(r)}–{max(r)}", ha="center", color=INK2, fontsize=9.5)
    cx.set_ylabel("rank of the 16 monomials")
    cx.set_title("16 ⇒ n ≥ 4", loc="left", fontsize=11.5)

    fig.suptitle("Weyl and Fock–Ivanenko 1929 — Dirac in curved spacetime: gravity does not "
                 "move the 4", x=0.01, ha="left", fontsize=13, color=INK)
    fig.tight_layout()
    fig.savefig(OUT / "dirac1929_curved.png", facecolor=SURFACE)
    plt.close(fig)


if __name__ == "__main__":
    fig_dirac_curved()
