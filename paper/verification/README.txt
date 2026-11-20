Exact algebraic verification
============================

Requirements: Python 3 and SymPy (verified with SymPy 1.14.0).
Command: python verification/verify_certificates.py
Run this from the manuscript directory, or invoke the script by its full path.

The script uses exact integer/rational arithmetic. It checks:
1. The fourth-node polynomial identity.
2. The formulas for Q_3-Q_2 and Q_4-Q_3.
3. The polynomial obtained by differentiating B_{n,k}(c) C_k(c) at n=k-2.
4. The identity after substituting the comparison value z-hat.
5. Every coefficient of P(5+v,7+v+r), and the degree/minimum table in the appendix.
6. Every coefficient of P_4(6+r), including the displayed list in the appendix.

Generated output:
- verification_results.json: assertions and a concise exact summary.
- P_coefficients.csv: every rational coefficient of r^j v^i.
- P4_coefficients.csv: every rational coefficient of r^i.

The positivity checks prove the relevant polynomial inequalities for the
entire indicated nonnegative-variable ranges; they are not sampled numeric
checks. They verify the algebraic portions of the appendix, not every
analytical or combinatorial argument of the paper.
