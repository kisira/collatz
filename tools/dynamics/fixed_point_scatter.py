import numpy as np
import matplotlib.pyplot as plt
import math

# ==========================================
# 1. Mathematical Definitions
# ==========================================

def calculate_geometry(alpha, p):
    """
    Computes the Operator Geometry (u, v) for a given (alpha, p).
    Returns:
        u: Gain (log A)
        v_e: Fixed point for family e
        v_o: Fixed point for family o
    """
    # 1. Calculate K and q_p
    # K = (2^(alpha + 6p) - 3) * 4^p
    K = (2**(alpha + 6*p) - 3) * (4**p)
    q_p = (4**p - 1) // 3

    # 2. Calculate Slope A
    # A = 1 + K/3
    A = 1 + K/3.0

    # 3. Calculate Offsets B_epsilon
    # B_1 (Family e) = 4*q_p - K/3
    B_e = 4*q_p - K/3.0

    # B_5 (Family o) = 10*q_p - 2 - 5*K/3
    B_o = 10*q_p - 2 - 5*K/3.0

    # 4. Calculate Coordinates (u, v)
    if A <= 0: return None, None, None # Filter degenerate cases if any (usually A > 0)
    if A == 1: return None, None, None # Singularity

    u = math.log(A)

    # Fixed point v = B / (A - 1)
    v_e = B_e / (A - 1)
    v_o = B_o / (A - 1)

    return u, v_e, v_o

# ==========================================
# 2. Generate Data
# ==========================================

alphas = range(1, 7) # Standard table alphas 1..6
ps = range(0, 4)     # Column lifts 0..3

data = []

for p in ps:
    for alpha in alphas:
        u, v_e, v_o = calculate_geometry(alpha, p)
        if u is not None:
            data.append({
                'p': p,
                'alpha': alpha,
                'u': u,
                'v_e': v_e,
                'v_o': v_o
            })

# ==========================================
# 3. Plotting
# ==========================================

plt.figure(figsize=(10, 7))

# Extract lists for plotting
us = [d['u'] for d in data]
ves = [d['v_e'] for d in data]
vos = [d['v_o'] for d in data]

# 1. Draw the "Vertical Fibers" (connecting v_e and v_o for same parameters)
# This visually proves Lemma 18 (The Arithmetic Fiber)
for i in range(len(data)):
    plt.plot([us[i], us[i]], [ves[i], vos[i]], color='gray', linestyle='-', alpha=0.3, zorder=1)

# 2. Scatter points
# Family e (Blue Circles)
scatter_e = plt.scatter(us, ves, c=us, cmap='Blues', marker='o',
                        s=100, edgecolors='black', label='Family $\mathbf{e}$ ($v_1$)', zorder=2)

# Family o (Red Squares)
scatter_o = plt.scatter(us, vos, c=us, cmap='Reds', marker='s',
                        s=100, edgecolors='black', label='Family $\mathbf{o}$ ($v_5$)', zorder=2)

# 3. Annotate a few key points (e.g. p=0)
for d in data:
    if d['p'] == 0:
        plt.text(d['u'], d['v_e'], f"$\\alpha={d['alpha']}$",
                 fontsize=8, ha='right', va='bottom', color='blue')

# Formatting
plt.title("Operator Geometry: Fixed Points $v$ vs. Gain $u = \log(A)$", fontsize=14)
plt.xlabel("Gain $u$ (Expansion Rate)", fontsize=12)
plt.ylabel("Geometric Fixed Point $v = B/(A-1)$", fontsize=12)
plt.axhline(0, color='black', linewidth=0.5)
plt.grid(True, linestyle='--', alpha=0.5)
plt.legend(fontsize=11)

# Explanation box
text_str = (
    "Vertical Lines = The Arithmetic Fiber\n"
    "For a fixed Gain (u), the Fixed Point (v)\n"
    "splits based on the input family."
)
plt.text(0.05, 0.95, text_str, transform=plt.gca().transAxes, fontsize=10,
         verticalalignment='top', bbox=dict(boxstyle='round', facecolor='white', alpha=0.9))

plt.tight_layout()
plt.savefig('figure_fixedpoint_scatter.png', dpi=300)
print("Generated 'figure_fixedpoint_scatter.png'")
plt.show()
