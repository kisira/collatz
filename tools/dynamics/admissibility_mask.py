import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as patches

# ==========================================
# 1. Define the Unified Table (The Logic)
# ==========================================
# We map (Family, j) -> Alpha
# This defines the "Shape" of the machine.
ROWS = {
    # Family e (1 mod 6)
    ('e', 0): {'alpha': 2, 'move': 'Psi_0/psi_0'},
    ('e', 1): {'alpha': 4, 'move': 'Psi_1/psi_1'},
    ('e', 2): {'alpha': 6, 'move': 'Psi_2/psi_2'},
    # Family o (5 mod 6)
    ('o', 0): {'alpha': 3, 'move': 'omega_0/Omega_0'},
    ('o', 1): {'alpha': 1, 'move': 'omega_1/Omega_1'},
    ('o', 2): {'alpha': 5, 'move': 'omega_2/Omega_2'},
}

def get_admissible_row(x):
    """Determines which row is active for input x."""
    # 1. Determine Family
    if x % 6 == 1:
        s = 'e'
    elif x % 6 == 5:
        s = 'o'
    else:
        return None # Not on odd layer

    # 2. Determine Router j
    # j = floor(x/6) mod 3
    j = (x // 6) % 3

    return ROWS.get((s, j))

# ==========================================
# 2. Generate the Data Grid
# ==========================================

# We will scan a range of integers to visualize the pattern
x_min, x_max = 1, 109
x_values = range(x_min, x_max, 2) # Odds only

# We'll create a visual grid where:
# X-axis = The integer x
# Y-axis = The row index j (0, 1, 2) + offset for family
# Color = The alpha value (The "Gain" of that step)

points_e = [] # (x, j, alpha)
points_o = [] # (x, j, alpha)

for x in x_values:
    if x % 3 == 0: continue # Skip multiples of 3 (not in 1,5 mod 6)

    row = get_admissible_row(x)
    if row:
        j = (x // 6) % 3
        alpha = row['alpha']

        if x % 6 == 1:
            points_e.append((x, j, alpha))
        else:
            points_o.append((x, j, alpha))

# ==========================================
# 3. Plotting the Mask
# ==========================================

fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 8), sharex=True)

# Helper to plot grid
def plot_strip(ax, points, title, cmap_name):
    # Create grid: rows are j=0,1,2. Cols are x.
    # We plot dots where admissible.

    xs = [p[0] for p in points]
    js = [p[1] for p in points]
    alphas = [p[2] for p in points]

    sc = ax.scatter(xs, js, c=alphas, cmap=cmap_name, s=100, marker='s', edgecolors='gray')

    ax.set_yticks([0, 1, 2])
    ax.set_yticklabels(['$j=0$', '$j=1$', '$j=2$'])
    ax.set_ylabel("Router Index $j$")
    ax.set_title(title)
    ax.grid(True, axis='x', linestyle=':', alpha=0.6)

    # Annotate alpha values on the squares
    for x, j, a in points:
        ax.text(x, j, str(a), ha='center', va='center', color='white', fontweight='bold', fontsize=8)

    return sc

# Plot Family E
# FIX: Replaced \pmod 6 with (\mathrm{mod}\ 6)
sc1 = plot_strip(ax1, points_e, r"Family $\mathbf{e}$ Admissibility Mask ($x \equiv 1 \ (\mathrm{mod}\ 6)$)", 'Blues')
cbar1 = plt.colorbar(sc1, ax=ax1, ticks=[2,4,6])
cbar1.set_label(r"Exponent $\alpha$")

# Plot Family O
# FIX: Replaced \pmod 6 with (\mathrm{mod}\ 6)
sc2 = plot_strip(ax2, points_o, r"Family $\mathbf{o}$ Admissibility Mask ($x \equiv 5 \ (\mathrm{mod}\ 6)$)", 'Reds')
cbar2 = plt.colorbar(sc2, ax=ax2, ticks=[1,3,5])
cbar2.set_label(r"Exponent $\alpha$")

ax2.set_xlabel("Input Integer $x$")
plt.suptitle("The Admissibility Mask: Periodic Activation of Row Parameters", fontsize=14)

plt.tight_layout()
plt.savefig('figure_admissibility_mask.png', dpi=300)
print("Generated 'figure_admissibility_mask.png'")
plt.show()