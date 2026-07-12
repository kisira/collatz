import numpy as np
import matplotlib.pyplot as plt
import matplotlib.colors as mcolors

# ==========================================
# 1. Definitions
# ==========================================

def get_AB(alpha, p, family_epsilon):
    """Calculates A and B for a given parameter set."""
    # K = (2^(alpha + 6p) - 3) * 4^p
    K = (2**(alpha + 6*p) - 3) * (4**p)

    # A = 1 + K/3
    A = 1 + K/3.0

    # q_p = (4^p - 1) / 3
    q_p = (4**p - 1) // 3

    if family_epsilon == 1: # Family e
        # B_1 = 4*q_p - K/3
        B = 4*q_p - K/3.0
    else: # Family o
        # B_5 = 10*q_p - 2 - 5*K/3
        B = 10*q_p - 2 - 5*K/3.0

    return A, B

def calculate_distance(A1, B1, A2, B2, X_bound=1000):
    """
    Calculates the operator metric d_X(T1, T2).
    d_X <= |A1 - A2|*X + |B1 - B2|
    """
    term_A = abs(A1 - A2) * X_bound
    term_B = abs(B1 - B2)
    return term_A + term_B

# ==========================================
# 2. Setup: Reference vs. The World
# ==========================================

# Reference: Psi_0 (alpha=2, p=0, family=e)
ref_alpha = 2
ref_p = 0
ref_fam = 1 # e
A_ref, B_ref = get_AB(ref_alpha, ref_p, ref_fam)

# Grid ranges
alpha_range = np.linspace(1, 8, 100) # Continuous alpha for contour smoothness
p_range = np.linspace(0, 3, 100)     # Continuous p

Z = np.zeros((len(p_range), len(alpha_range)))

# We will check distance against Family 'e' (epsilon=1) for the grid
target_fam = 1

# ==========================================
# 3. Compute Grid
# ==========================================

for i, p_val in enumerate(p_range):
    for j, a_val in enumerate(alpha_range):
        # We interpret the continuous values as parameters for the affine formula
        # even if 'row alpha' is discrete integers, the math A(alpha, p) is continuous.

        # We use the integer-approximated formulas but with floats
        # K approx 2^(a+6p) * 4^p = 2^(a+8p)
        # We can use the exact formula with floats

        K_val = (2**(a_val + 6*p_val) - 3) * (4**p_val)
        A_val = 1 + K_val/3.0
        q_p_val = (4**p_val - 1) / 3.0

        # B_e formula
        B_val = 4*q_p_val - K_val/3.0

        dist = calculate_distance(A_ref, B_ref, A_val, B_val, X_bound=1000)

        # Use log10 for visualization because distances explode
        Z[i, j] = np.log10(dist) if dist > 0 else -1

# ==========================================
# 4. Plotting
# ==========================================

plt.figure(figsize=(10, 7))

# Contour plot
cp = plt.contourf(alpha_range, p_range, Z, levels=20, cmap='magma')
cbar = plt.colorbar(cp)
cbar.set_label(r"Log Distance $\log_{10}(d_{1000}(\Psi_0, T))$", fontsize=12)

# Mark the discrete Integer points (The actual rows)
discrete_alphas = [1, 2, 3, 4, 5, 6]
discrete_ps = [0, 1, 2, 3]

for p in discrete_ps:
    for a in discrete_alphas:
        # Check if it's the reference point
        if p == ref_p and a == ref_alpha:
            plt.scatter(a, p, c='white', s=150, marker='*', edgecolors='black', label='Reference ($\Psi_0$)', zorder=10)
        else:
            plt.scatter(a, p, c='white', s=30, alpha=0.5, edgecolors='none', zorder=5)

plt.title("Operator Distance Contours (Relative to $\Psi_0$ at $p=0$)", fontsize=14)
plt.xlabel(r"Row Parameter $\alpha$", fontsize=12)
plt.ylabel(r"Column Lift $p$", fontsize=12)
plt.legend(loc='upper right')

# Annotation
plt.text(ref_alpha + 0.2, ref_p + 0.1, "Zero Distance", color='white', fontweight='bold')

plt.tight_layout()
plt.savefig('figure_operator_distance.png', dpi=300)
print("Generated 'figure_operator_distance.png'")
plt.show()
