import numpy as np
import matplotlib.pyplot as plt
import math

# ==========================================
# 1. Core Logic (Matches your Paper/Coq)
# ==========================================

# Row parameters (alpha, beta, c, delta) for the unified table
# Key: (Family, Index) -> (alpha, beta, c, delta)
# We map these to simple IDs for the loop.
ROWS = [
    # Family e (1 mod 6)
    {'label': 'Psi_0', 's': 'e', 'j': 0, 'alpha': 2, 'beta': 2,   'c': -2, 'delta': 1},
    {'label': 'Psi_1', 's': 'e', 'j': 1, 'alpha': 4, 'beta': 56,  'c': -2, 'delta': 1},
    {'label': 'Psi_2', 's': 'e', 'j': 2, 'alpha': 6, 'beta': 416, 'c': -2, 'delta': 1},
    # Family o (5 mod 6)
    {'label': 'omega_0', 's': 'o', 'j': 0, 'alpha': 3, 'beta': 20,  'c': -2, 'delta': 1},
    {'label': 'omega_1', 's': 'o', 'j': 1, 'alpha': 1, 'beta': 11,  'c': -2, 'delta': 1},
    {'label': 'omega_2', 's': 'o', 'j': 2, 'alpha': 5, 'beta': 272, 'c': -2, 'delta': 1},
    # Family e -> o output
    {'label': 'psi_0',   's': 'e', 'j': 0, 'alpha': 4, 'beta': 8,   'c': -8, 'delta': 5},
    {'label': 'psi_1',   's': 'e', 'j': 1, 'alpha': 6, 'beta': 224, 'c': -8, 'delta': 5},
    {'label': 'psi_2',   's': 'e', 'j': 2, 'alpha': 2, 'beta': 26,  'c': -8, 'delta': 5},
    # Family o -> o output
    {'label': 'Omega_0', 's': 'o', 'j': 0, 'alpha': 5, 'beta': 80,  'c': -8, 'delta': 5},
    {'label': 'Omega_1', 's': 'o', 'j': 1, 'alpha': 3, 'beta': 44,  'c': -8, 'delta': 5},
    {'label': 'Omega_2', 's': 'o', 'j': 2, 'alpha': 1, 'beta': 17,  'c': -8, 'delta': 5},
]

def calculate_uv(row, p):
    """Calculates u (gain) and v (fixed point) for a given row and lift p."""
    alpha = row['alpha']

    # K = (2^(alpha + 6p) - 3) * 4^p
    K = (2**(alpha + 6*p) - 3) * (4**p)

    # A = 1 + K/3
    A = 1 + K/3.0

    # q_p = (4^p - 1) / 3
    q_p = (4**p - 1) // 3

    # B depends on the *input* family of the row (epsilon)
    # In your paper's definition of B_epsilon (Def 3):
    # B_1 = 4*q_p - K/3
    # B_5 = 10*q_p - 2 - 5*K/3

    # Calculate both potential B values to map the fiber
    B_e = 4*q_p - K/3.0
    B_o = 10*q_p - 2 - 5*K/3.0

    # u = log(A)
    u = math.log(A)

    # v = B / (A - 1)
    v_e = B_e / (A - 1)
    v_o = B_o / (A - 1)

    return u, v_e, v_o, A

# ==========================================
# 2. Generating the Data
# ==========================================

p_values = range(0, 4) # Columns 0 to 3
data_points = []

for p in p_values:
    for row in ROWS:
        u, v_e, v_o, A = calculate_uv(row, p)
        data_points.append({
            'label': row['label'],
            'p': p,
            'alpha': row['alpha'],
            'u': u,
            'v_e': v_e,
            'v_o': v_o,
            'type': row['s']  # Input family
        })

# ==========================================
# 3. Plotting Figure 1 & 2: The Operator Portrait
# ==========================================

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

# --- Plot A: Heatmap of Gain u over (alpha, p) ---
# We create a grid for alpha (1-6) vs p (0-3)
grid_u = np.zeros((4, 7)) # p rows, alpha cols (1-indexed)
grid_u[:] = np.nan

for dp in data_points:
    if dp['alpha'] <= 6:
        grid_u[dp['p'], dp['alpha']] = dp['u']

im = ax1.imshow(grid_u[:, 1:], origin='lower', cmap='viridis', aspect='auto')
ax1.set_title("Gain $u = \log(A)$ over $(\\alpha, p)$")
ax1.set_xlabel("Row Exponent $\\alpha$")
ax1.set_ylabel("Column Lift $p$")
ax1.set_xticks(range(6))
ax1.set_xticklabels(range(1, 7))
ax1.set_yticks(range(4))
cbar = fig.colorbar(im, ax=ax1)
cbar.set_label("Gain magnitude")

# --- Plot B: Fixed Point Scatter (v) over Gain (u) ---
# This visualizes the "vertical fibers" mentioned in Lemma 17
us = []
ves = []
vos = []
colors = []

for dp in data_points:
    us.append(dp['u'])
    ves.append(dp['v_e'])
    vos.append(dp['v_o'])
    # Color by input family
    colors.append('blue' if dp['type'] == 'e' else 'red')

ax2.scatter(us, ves, c='blue', marker='o', label='Family e ($v_1$)', alpha=0.7)
ax2.scatter(us, vos, c='red', marker='s', label='Family o ($v_5$)', alpha=0.7)

# Connect pairs belonging to the same parameter tuple
for i in range(len(us)):
    ax2.plot([us[i], us[i]], [ves[i], vos[i]], 'k-', alpha=0.2)

ax2.set_title("Operator Fixed Points $v$ vs Gain $u$")
ax2.set_xlabel("Gain $u$")
ax2.set_ylabel("Fixed Point $v = B/(A-1)$")
ax2.legend()
ax2.grid(True, linestyle='--', alpha=0.5)

plt.tight_layout()
plt.savefig('figure_operator_geometry.png', dpi=300)
print("Generated 'figure_operator_geometry.png'")

# ==========================================
# 4. Plotting Figure 4: Drift Heatmap
# ==========================================

# We visualize |x' - x| for a specific case, e.g., row Psi_0 (alpha=2)
# Drift approx = 2 * r * K
# We plot log(Drift) for varying r and p

r_range = np.arange(1, 100)
p_range = np.arange(0, 5)
drift_grid = np.zeros((len(p_range), len(r_range)))

# Using Psi_0 parameters: alpha=2
alpha = 2
for idx_p, p_val in enumerate(p_range):
    K = (2**(alpha + 6*p_val) - 3) * (4**p_val)
    q_p = (4**p_val - 1) // 3
    # Delta for family e is 2*q_p
    Delta = 2 * q_p

    for idx_r, r_val in enumerate(r_range):
        drift = 2 * (r_val * K + Delta)
        drift_grid[idx_p, idx_r] = math.log10(drift) if drift > 0 else 0

plt.figure(figsize=(8, 6))
plt.imshow(drift_grid, origin='lower', cmap='plasma', aspect='auto',
           extent=[1, 100, 0, 4])
plt.colorbar(label="$\log_{10}(|x' - x|)$")
plt.title("Drift Magnitude Heatmap (Row $\Psi_0$)")
plt.xlabel("Input Index $r = \lfloor x/6 \\rfloor$")
plt.ylabel("Column Lift $p$")
plt.savefig('figure_drift_heatmap.png', dpi=300)
print("Generated 'figure_drift_heatmap.png'")

plt.show()
