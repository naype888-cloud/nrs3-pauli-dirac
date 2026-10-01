"""Figure for Pauli 1925–27: shells, exclusion and the spin matrices (numpy, matplotlib).

Writes docs/figures/pauli1925.png.

Left: shell capacities 2n², stacked by subshell 2(2l + 1) (Lean: shell_card). These are shell
capacities, not lengths of the periods of the table, which also depend on energy ordering.
Middle: |ψ ∧ φ|(i, j) for two random states on d = 8 sites; the diagonal is zero (Lean:
antisymm_apply_self). Right: the three Pauli matrices, one per axis (Lean: sigma_mul).

Run:  python3 docs/simulation/figures_pauli.py
"""

import matplotlib.pyplot as plt
import numpy as np

from style import BLUE, INK, INK2, MUTED, ORANGE, OUT, SURFACE


def fig_pauli():
    fig = plt.figure(figsize=(13, 4.6), dpi=150)
    gs = fig.add_gridspec(2, 5, width_ratios=[1.35, 0.12, 1.15, 0.12, 1.25], hspace=0.5)

    ax = fig.add_subplot(gs[:, 0])
    cols = [BLUE, ORANGE, MUTED, "#1c5cab"]
    for n in range(1, 5):
        base = 0
        for l in range(n):
            h = 2 * (2 * l + 1)
            ax.bar(n, h, bottom=base, color=cols[l], width=0.62, edgecolor=SURFACE, zorder=3,
                   label=f"l = {l}: 2(2l + 1) = {h}" if n == 4 else None)
            base += h
        ax.text(n, base + 0.8, f"{base}", ha="center", color=INK, fontsize=11, fontweight="bold")
    ax.set_xticks(range(1, 5))
    ax.set_ylim(0, 38)
    ax.set_xlabel("shell  n")
    ax.set_ylabel("electrons the shell holds")
    ax.legend(loc="upper left", fontsize=8.8)
    ax.set_title("Shells hold 2n²", loc="left", fontsize=11.5)

    bx = fig.add_subplot(gs[:, 2])
    rng = np.random.default_rng(1925)
    psi, phi = (rng.normal(size=8) + 1j * rng.normal(size=8) for _ in range(2))
    w = np.outer(psi, phi) - np.outer(phi, psi)
    bx.imshow(np.abs(w), cmap="Blues")
    bx.plot(range(8), range(8), "x", color=ORANGE, ms=7, mew=1.6)
    bx.set_xticks(range(8))
    bx.set_yticks(range(8))
    bx.grid(False)
    bx.set_xlabel("site of particle 2")
    bx.set_ylabel("site of particle 1")
    bx.set_title("|ψ ∧ φ|: zero on the diagonal", loc="left", fontsize=11.5)

    i = 1j
    sig = [np.array([[0, 1], [1, 0]]), np.array([[0, -i], [i, 0]]), np.array([[1, 0], [0, -1]])]
    cx = fig.add_subplot(gs[:, 4])
    cx.set_axis_off()
    for a, (m, ax_name) in enumerate(zip(sig, "xyz")):
        x0 = a * 1.1
        for (r, c), v in np.ndenumerate(m):
            fc = SURFACE if v == 0 else (BLUE if v.real > 0 or v.imag > 0 else ORANGE)
            cx.add_patch(plt.Rectangle((x0 + c * 0.45, 1 - r * 0.45), 0.43, 0.43, fc=fc,
                                       ec=MUTED, lw=0.8))
            lab = "" if v == 0 else {1: "1", -1: "−1", 1j: "i", -1j: "−i"}[complex(v)]
            cx.text(x0 + c * 0.45 + 0.215, 1 - r * 0.45 + 0.215, lab, ha="center",
                    va="center", color=SURFACE if v != 0 else INK, fontsize=11)
        cx.text(x0 + 0.44, 1.55, f"σ_{ax_name}", ha="center", fontsize=12, color=INK)
    cx.text(1.55, 0.25, "σ_x σ_y = i σ_z  (and cyclic)\nthree anticommuting, no fourth\n"
            "in 2 × 2 — one per axis", ha="center", va="top", color=INK2, fontsize=9.5)
    cx.set_xlim(-0.1, 3.25)
    cx.set_ylim(-0.6, 1.8)
    cx.set_aspect("equal")
    cx.set_title("Spin matrices", loc="left", fontsize=11.5)

    fig.suptitle("Pauli 1925–27 — exclusion, shells and spin", x=0.01, ha="left", fontsize=13,
                 color=INK)
    fig.savefig(OUT / "pauli1925.png", facecolor=SURFACE, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    fig_pauli()
