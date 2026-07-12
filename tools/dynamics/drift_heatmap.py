import numpy as np
import matplotlib.pyplot as plt
import matplotlib.colors as mcolors

# ==========================================
# 1. Drift Calculation Logic
# ==========================================

def calculate_drift_grid(alpha, family_type, r_max=100, p_max=5):
    """
    Generates a grid of log10(drift) values.
    rows: p (0 to p_max)
    cols: r (1 to r_max)
    """
    p_values = np.arange(0, p_max + 1)
    r_values = np.arange(1, r_max + 1)

    # Initialize grid
    # dimensions: (p, r)
    drift_grid = np.zeros((len(p_values), len(r_values)))

    for i, p in enumerate(p_values):
        # Constants for this p
        # K = (2^(alpha + 6p) - 3) * 4^p
        K = (2**(alpha + 6*p) - 3) * (4**p)

        # q_p = (4^p - 1) / 3
        q_p = (4**p - 1) // 3

        # Delta depends on family
        if family_type == 'e': # x = 1 mod 6
            Delta = 2 * q_p
        else: # family 'o', x = 5 mod 6
            Delta = 5 * q_p - 1

        for j, r in enumerate(r_values):
            # Drift d = r*K + Delta
            # We visualize the absolute magnitude |2d| = |x' - x|
            d = r * K + Delta
            magnitude = abs(2 * d)

            # Use log10 for visualization because values grow huge
            # Avoid log(0) by using a small epsilon if needed, though K>=1 usually
            if magnitude > 0:
                drift_grid[i, j] = np.log10(magnitude)
            else:
                drift_grid[i, j] = 0

    return drift_grid

# ==========================================
# 2. Plotting the Grid of Panels
# ==========================================

# We will plot alphas 1..6
# alpha=1,3,5 are Family 'o'
# alpha=2,4,6 are Family 'e'

configs = [
    {'alpha': 1, 'fam': 'o', 'title': r'$\alpha=1$ (Family $\mathbf{o}$)'},
    {'alpha': 2, 'fam': 'e', 'title': r'$\alpha=2$ (Family $\mathbf{e}$)'},
    {'alpha': 3, 'fam': 'o', 'title': r'$\alpha=3$ (Family $\mathbf{o}$)'},
    {'alpha': 4, 'fam': 'e', 'title': r'$\alpha=4$ (Family $\mathbf{e}$)'},
    {'alpha': 5, 'fam': 'o', 'title': r'$\alpha=5$ (Family $\mathbf{o}$)'},
    {'alpha': 6, 'fam': 'e', 'title': r'$\alpha=6$ (Family $\mathbf{e}$)'},
]

fig, axes = plt.subplots(2, 3, figsize=(15, 9), sharex=True, sharey=True)
axes = axes.flatten()

# Common settings
r_max = 100
p_max = 4

for idx, cfg in enumerate(configs):
    ax = axes[idx]

    # Calculate Data
    grid = calculate_drift_grid(cfg['alpha'], cfg['fam'], r_max=r_max, p_max=p_max)

    # Plot Heatmap
    # X-axis: r (1..100), Y-axis: p (0..4)
    im = ax.imshow(grid, origin='lower', aspect='auto', cmap='plasma',
                   extent=[1, r_max, -0.5, p_max + 0.5])

    # Labeling
    ax.set_title(cfg['title'], fontsize=12)
    ax.grid(False) # Heatmap is self-gridded

    # Add text annotations for a few cells to show scale
    # (p=0, r=50) and (p=3, r=50)
    val_low = grid[0, 49]
    val_high = grid[3, 49]
    ax.text(50, 0, f"10^{val_low:.1f}", color='white', ha='center', va='center', fontsize=8, fontweight='bold')
    ax.text(50, 3, f"10^{val_high:.1f}", color='black', ha='center', va='center', fontsize=8, fontweight='bold')

# Axis labels
for ax in axes[-3:]:
    ax.set_xlabel(r"Coarse Index $r = \lfloor x/6 \rfloor$")

for ax in axes[0::3]:
    ax.set_ylabel(r"Column Lift $p$")
    ax.set_yticks(range(p_max + 1))

# Colorbar
cbar_ax = fig.add_axes([0.92, 0.15, 0.02, 0.7])
cbar = fig.colorbar(im, cax=cbar_ax)
cbar.set_label(r"Drift Magnitude $\log_{10}(|x' - x|)$", fontsize=12)

plt.suptitle(r"Drift Magnitude $|x' - x|$ vs Index $(r)$ and Lift $(p)$", fontsize=16)
plt.savefig('figure_drift_heatmap.png', dpi=300, bbox_inches='tight')
