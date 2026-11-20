"""Render the two exact candidate curves for k=3 as a vector PDF."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

root = Path(__file__).resolve().parents[1]
plt.rcParams.update({
    "font.family": "serif",
    "font.serif": ["DejaVu Serif"],
    "mathtext.fontset": "cm",
    "font.size": 9,
    "axes.labelsize": 10,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
})
x = np.linspace(0, 1/3, 700)
beta = (np.sqrt(321)-3)/52
fig, ax = plt.subplots(figsize=(5.65, 2.65))
ax.plot(x, 1-(1-x)**3, color="#245980", lw=1.7,
        label=r"$F_3(B_x)=1-(1-x)^3$")
ax.plot(x, (3*x)**3, color="#A8502E", lw=1.7,
        label=r"$F_3(C_{3,x})=(3x)^3$")
ax.axvline(beta, color="#555555", lw=.8, linestyle=(0, (3, 3)))
ax.scatter([beta], [(3*beta)**3], color="#222222", s=16, zorder=4)
ax.set(xlim=(0, 1/3), ylim=(0, 1.02), xlabel=r"Mean $x$",
       ylabel="Success probability")
ax.set_xticks([0, .1, .2, beta, 1/3],
              [r"$0$", r"$0.1$", r"$0.2$", r"$\beta_3$", r"$1/3$"])
ax.set_yticks([0, .25, .5, .75, 1])
ax.spines[["top", "right"]].set_visible(False)
ax.grid(axis="y", color="#DDDDDD", linewidth=.5)
ax.legend(loc="upper left", frameon=False)
fig.tight_layout(pad=.6)
(root/"figures").mkdir(exist_ok=True)
fig.savefig(root/"figures"/"critical_mean.pdf", bbox_inches="tight")
fig.savefig(root/"figures"/"critical_mean.png", dpi=180, bbox_inches="tight")
plt.close(fig)
