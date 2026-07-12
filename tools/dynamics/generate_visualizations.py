import numpy as np
import matplotlib.pyplot as plt

# --- 1. Define Parameters and Functions ---

# Row parameters from the paper (Table 2)
# Key: (Family, j) -> (Type, alpha, beta, c, delta)
# Family: 'e' (1 mod 6), 'o' (5 mod 6)
ROWS = {
    ('e', 0): {'name': r'$\Psi_0$', 'type': 'ee', 'alpha': 2},
    ('e', 1): {'name': r'$\Psi_1$', 'type': 'ee', 'alpha': 4},
    ('e', 2): {'name': r'$\Psi_2$', 'type': 'ee', 'alpha': 6},
    ('o', 0): {'name': r'$\omega_0$', 'type': 'oe', 'alpha': 3},
    ('o', 1): {'name': r'$\omega_1$', 'type': 'oe', 'alpha': 1},
    ('o', 2): {'name': r'$\omega_2$', 'type': 'oe', 'alpha': 5},
    ('e', 0, 'alt'): {'name': r'$\psi_0$', 'type': 'eo', 'alpha': 4},
    ('e', 1, 'alt'): {'name': r'$\psi_1$', 'type': 'eo', 'alpha': 6},
    ('e', 2, 'alt'): {'name': r'$\psi_2$', 'type': 'eo', 'alpha': 2},
    ('o', 0, 'alt'): {'name': r'$\Omega_0$', 'type': 'oo', 'alpha': 5},
    ('o', 1, 'alt'): {'name': r'$\Omega_1$', 'type': 'oo', 'alpha': 3},
    ('o', 2, 'alt'): {'name': r'$\Omega_2$', 'type': 'oo', 'alpha': 1},
}

def get_row_params(token_key, p=0):
    row = ROWS[token_key]
    alpha = row['alpha']
    # K = (2^(alpha+6p) - 3) * 4^p
    K = (2**(alpha + 6*p) - 3) * (4**p)

    # A = 1 + K/3
    A = 1 + K/3.0

    # q_p = (4^p - 1)/3
    q_p = (4**p - 1)//3

    # B depends on input family
    if row['type'].startswith('e'):
        B = 4*q_p - K/3.0  # Family e
    else:
        B = 10*q_p - 2 - 5*K/3.0 # Family o

    return A, B, K, row['name']

def collatz_forward(x):
    """Applies the accelerated odd Collatz map U(x)."""
    val = 3 * x + 1
    while val % 2 == 0:
        val //= 2
    return val

def generate_orbit(start_x):
    """Generates the orbit x -> ... -> 1."""
    orbit = [start_x]
    curr = start_x
    while curr != 1:
        curr = collatz_forward(curr)
        orbit.append(curr)
    return orbit

# --- 2. Generate Data ---

# A. Trajectory Data for 3071
# We generate the orbit 3071 -> 1, then reverse it to get the inverse witness 1 -> 3071
x_start = 3071
orbit = generate_orbit(x_start)
inverse_orbit = orbit[::-1]

tags = [(x - 1)//2 for x in inverse_orbit]
rs = [x // 6 for x in inverse_orbit]
# Calculate actual drifts d = t_{n+1} - t_n
drifts = []
for i in range(len(tags)-1):
    drifts.append(tags[i+1] - tags[i])

# B. Operator Geometry Data
geo_points = []
for key in ROWS:
    # p=0
    A, B, K, name = get_row_params(key, p=0)
    if A > 1: # Skip singularities if any
       u = np.log(A)
       v = B / (A - 1)
       geo_points.append({'u': u, 'v': v, 'name': name, 'p': 0, 'fam': key[0]})

    # p=1
    A1, B1, K1, name1 = get_row_params(key, p=1)
    u1 = np.log(A1)
    v1 = B1 / (A1 - 1)
    geo_points.append({'u': u1, 'v': v1, 'name': name1 + "'", 'p': 1, 'fam': key[0]})


# --- 3. Create Plots ---

# PLOT 1: Drift Space (d vs r)
plt.figure(figsize=(8, 6))
r_vals = np.linspace(0, max(rs)+2, 100)

tokens_to_plot = [
    (('e', 0), 'blue', r'$\Psi_0$'),
    (('o', 1), 'green', r'$\omega_1$'),
    (('e', 2, 'alt'), 'red', r'$\psi_2$'),
    (('o', 0, 'alt'), 'purple', r'$\Omega_0$')
]

for key, color, label in tokens_to_plot:
    A, B, K, name = get_row_params(key, p=0)
    epsilon = 1 if key[0] == 'e' else 5
    Delta = (epsilon * K - 1) / 6.0
    plt.plot(r_vals, K * r_vals + Delta, label=f'Theoretical {label} ($K={K}$)', color=color, linestyle='--', alpha=0.5)

traj_r = rs[:-1]
traj_d = drifts
plt.scatter(traj_r, traj_d, color='black', zorder=10, s=40, label='Orbit $1 \\to 3071$')

plt.title('Drift vs. Coarse Index $r$ (Orbit 1 $\\to$ 3071)')
plt.xlabel('Coarse Index $r = \\lfloor x/6 \\rfloor$')
plt.ylabel('Drift $d = t(x_{next}) - t(x)$')
plt.legend()
plt.grid(True, alpha=0.3)
plt.savefig('drift_plot.png')


# PLOT 2: Operator Geometry
plt.figure(figsize=(8, 6))
e_points = [p for p in geo_points if p['fam'] == 'e']
o_points = [p for p in geo_points if p['fam'] == 'o']

plt.scatter([p['u'] for p in e_points], [p['v'] for p in e_points], color='blue', label='Family e (Input $\equiv 1$)')
plt.scatter([p['u'] for p in o_points], [p['v'] for p in o_points], color='red', label='Family o (Input $\equiv 5$)')

unique_us = sorted(list(set(p['u'] for p in geo_points)))
for u_val in unique_us:
    fiber_pts = [p for p in geo_points if abs(p['u'] - u_val) < 1e-9]
    if len(fiber_pts) > 1:
        ys = [p['v'] for p in fiber_pts]
        plt.plot([u_val, u_val], [min(ys), max(ys)], color='gray', linestyle=':', alpha=0.5)

for p in geo_points:
    if p['p'] == 0:
        plt.annotate(p['name'], (p['u'], p['v']), xytext=(5, 5), textcoords='offset points')

plt.title('Operator Geometry: Vertical Fibers')
plt.xlabel('Gain $u = \\ln(A)$')
plt.ylabel('Geometric Fixed Point $v = B/(A-1)$')
plt.legend()
plt.grid(True, alpha=0.3)
plt.savefig('operator_geometry.png')


# PLOT 3: Geometric Trap
plt.figure(figsize=(6, 6))
x = np.linspace(0, 4, 100)
y_map = (4.0/3.0) * x - (1.0/3.0)
y_ident = x

plt.plot(x, y_map, label=r'Inverse Map $\Psi_0$: $y = \frac{4}{3}x - \frac{1}{3}$', color='blue')
plt.plot(x, y_ident, label=r'Identity $y=x$', color='black', linestyle='--')
plt.scatter([1], [1], color='red', zorder=10, label='Fixed Point $v=1$')

plt.arrow(1.5, 1.5, 0, (4/3*1.5 - 1/3) - 1.5, head_width=0.1, head_length=0.1, fc='green', ec='green')
plt.arrow(0.5, 0.5, 0, (4/3*0.5 - 1/3) - 0.5, head_width=0.1, head_length=0.1, fc='green', ec='green')

plt.title('Geometric Trap: Repulsion at Fixed Point')
plt.xlabel('$x$')
plt.ylabel('$f(x)$')
plt.legend()
plt.grid(True, alpha=0.3)
plt.axis('equal')
plt.savefig('geometric_trap.png')
