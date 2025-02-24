# This file shows that the following system is always satisfiable:
# 1: ov * (ov - 1) = 0
# 2: (x + y) mod p = z mod p
# 3: (x + y - m * ov) mod m = z mod m
# 4: 0 < x < m
# 5: 0 < y < m
# 6: 0 < z < m
import cvc5
from cvc5 import Kind

# Parameters: a very large prime p and a small integer m such that 2*m < p.
p = 1321888242871839275222246405745257275088548364400416034343698204186575808495617  # a very large prime
m = 1 << 32

assert 2 * m < p, "Require 2*m < p."

# Create the solver instance.
solver = cvc5.Solver()
solver.setOption("produce-models", "true")
solver.setLogic("QF_NIA")

# Declare the integer sort.
IntSort = solver.getIntegerSort()

# Declare variables.
# 'ov' is the main variable, renamed from x.
ov = solver.mkConst(IntSort, "ov")
# 'x', 'y', 'z' are hidden auxiliary variables.
x = solver.mkConst(IntSort, "x")
y = solver.mkConst(IntSort, "y")
z = solver.mkConst(IntSort, "z")
# 'r' and 's' are auxiliary variables for the modular equations.
r = solver.mkConst(IntSort, "r")
s = solver.mkConst(IntSort, "s")

# Optional: restrict ov to the range [0, 1].
solver.assertFormula(solver.mkTerm(Kind.GEQ, ov, solver.mkInteger("0")))
solver.assertFormula(solver.mkTerm(Kind.LEQ, ov, solver.mkInteger("1")))

# Equation 1: ov * (ov - 1) = 0.
ov_minus_one = solver.mkTerm(Kind.SUB, ov, solver.mkInteger("1"))
eq1 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.MULT, ov, ov_minus_one), solver.mkInteger("0"))
solver.assertFormula(eq1)

# Equation 2: (x + y) mod p = z mod p.
# Equivalently, x + y - z = p * r.
sum_xy = solver.mkTerm(Kind.ADD, x, y)
lhs2 = solver.mkTerm(Kind.SUB, sum_xy, z)
eq2 = solver.mkTerm(Kind.EQUAL, lhs2,
                    solver.mkTerm(Kind.MULT, solver.mkInteger(str(p)), r))
solver.assertFormula(eq2)

# Equation 3: (x + y - m * ov) mod m = z mod m.
# Equivalently, x + y - m*ov - z = m * s.
m_times_ov = solver.mkTerm(Kind.MULT, solver.mkInteger(str(m)), ov)
lhs3 = solver.mkTerm(Kind.SUB,
                     solver.mkTerm(Kind.SUB, sum_xy, m_times_ov),
                     z)
eq3 = solver.mkTerm(Kind.EQUAL, lhs3,
                    solver.mkTerm(Kind.MULT, solver.mkInteger(str(m)), s))
solver.assertFormula(eq3)

# Check if the overall constraint system is satisfiable.
if solver.checkSat().isSat():
    print("SAT")
else:
    print("UNSAT")
