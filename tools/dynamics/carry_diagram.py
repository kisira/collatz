import numpy as np
import matplotlib.pyplot as plt

# ==========================================
# 1. Definitions (The Physics)
# ==========================================

def calculate_carry(r, family_epsilon, alpha, p):
    """
    Calculates the Carry 'c' for a specific input r and row parameters.
    Formula: c = floor( (epsilon + 2*d) / 6 )
    Where d = r*K + Delta
    """
    # 1. Calculate K and q_p
    # K = (2^(alpha + 6p) - 3) * 4^p
    K = (2**(alpha + 6*p) - 3) * (4**p)
    q_p = (4**p - 1) // 3

    # 2. Calculate Delta and Drift d
    if family_epsilon == 1: # Family e
        Delta = 2 * q_p
    else: # Family o (epsilon=5)
        Delta = 5 * q_p - 1

    d = r * K + Delta

    # 3. Calculate Carry
    # r' = r + c
    c = (family_epsilon + 2 * d) // 6
    return c

# ==========================================
# 2. Setup the Experiment
# ==========================================

r_values = np.arange(0, 20) # Look at the first 20 blocks of numbers

# We will compare three different "Energies" of rows:
scenarios = [
    # (Name, family_epsilon, alpha, p, color)
    (r"Low Energy ($\Psi_0, p=0$)", 1, 2, 0, 'blue'),    # alpha=2, K=1
    (r"Medium Energy ($\Psi_1, p=0$)", 1, 4, 0, 'green'), # alpha=4, K=13
    (r"High Energy ($\Psi_0, p=1$)", 1, 2, 1, 'red'),     # alpha=2+6=8, High K
]

# ==========================================
# 3. Plotting
# ==========================================

plt.figure(figsize=(10, 6))

for label, eps, alpha, p, color in scenarios:
    carries = [calculate_carry(r, eps, alpha, p) for r in r_values]

    # Plot as step function to emphasize discreteness
    plt.step(r_values, carries, where='mid', label=label, color=color, linewidth=2)

    # Add dots to show the exact integer points
    plt.scatter(r_values, carries, color=color, s=30, alpha=0.6)

# Formatting
plt.title("The Carry Diagram: Index Jumps ($c$) vs Input Index ($r$)", fontsize=14)
plt.xlabel("Input Coarse Index $r = \lfloor x/6 \\rfloor$", fontsize=12)
plt.ylabel("Carry Magnitude $c = r' - r$", fontsize=12)
plt.grid(True, linestyle='--', alpha=0.5)
plt.legend(fontsize=11)

# Annotate the "Turbulence"
plt.text(1, 10, "Steeper Slope = More 'Turbulence'\n(Higher 2-adic valuation)",
         fontsize=10, bbox=dict(facecolor='white', alpha=0.8))

plt.tight_layout()
plt.savefig('figure_carry_diagram.png', dpi=300)
print("Generated 'figure_carry_diagram.png'")
plt.show()
