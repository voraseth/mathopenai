Python 3 with mpmath. Run each script from this directory:

- `python3 check_surrogate_exact.py` (check 1 of Appendix B)
- `python3 check_entropy.py` (check 2, random matrices)
- `python3 check_discount_chains.py` (check 2, chains; it loads `check_pipeline.py` from the current directory)
- `python3 check_pipeline.py` (checks 3 and 4)

Each prints a final line reporting success. The Lean sources are in `lean/`; see `lean/README.md`.

## Details of the numerical checks (Appendix B of the paper, Table 2)

The paper's Appendix B gives one row per check. The run parameters that are not in the paper:

- Check 1 (`check_surrogate_exact.py`). The test of Proposition 5.5(c) is implemented with rationals
  for a two-state game; monotonicity of `floor(G)` and the identity
  `floor(G(t + N j 1)) = floor(G(t)) + (N - 1) j` are tested at 300 random integer points.
- Check 2, random matrices (`check_entropy.py`). 200 random matrices of order 2 to 5 with nonzero
  rows and entries in {0, 0.3, 1, 2, 5}, of which 150 are reducible and 50 irreducible, each with
  N = 50 and N = 400, in floating point. Omega is the right-hand side of Equation (5) of the paper,
  `v` is obtained by iterating the map Psi_M, and lambda_i is computed from the classes, the Perron
  roots being obtained by power iteration to a relative accuracy better than 1e-12. Largest observed
  ratio `|theta v_i - lambda_i| / (theta R)`: 0.042 on the reducible matrices, 0.026 on the
  irreducible ones.
- Check 2, chains (`check_discount_chains.py`). Chains of up to six classes with equal or nearly
  equal Perron roots and coupling weights between 1e-6 and 1e6, with N up to 2^40, in 80-digit
  arithmetic. R is evaluated with a value of Omega that is at most the right-hand side of
  Equation (5), so the ratio reported is an upper bound for the ratio with any admissible Omega.
  Largest observed ratio: 0.076.
- Check 3 (`check_pipeline.py`). 54 games with two or three Despot states (ties at the threshold,
  reducible chains with equal Perron roots, weights between 1e-6 and 1e6, and 40 random games). The
  algorithm of Section 8 is run with its true parameters; the procedure L is replaced by an oracle
  that returns arbitrary labels subject only to the two implications used in the proof of
  Proposition 4.3. The output is compared with an independent exact decision of `V_d >= r`
  (enumeration of policies; `rho_C >= 1` tested through the leading principal minors of
  `I - M_CC` in rational arithmetic). The fixed point `x` used to build the oracle is computed by
  Newton's method in 120-digit arithmetic, not exactly.
- Check 4 (`check_pipeline.py`). For one Despot state the procedure L is implemented literally,
  except for a shortcut in the width base case: for n = 1 the limit `t*` of the iteration (3.3) of
  the cited manuscript equals the clipping to the box of `max{t in Z : floor(G(t)) >= t}`, which is
  computed once, exactly, and reused in every width base case. `floor(G)` is evaluated in exact
  rational arithmetic. Five games; all outputs agree with the exact decision.

## Location of the cited manuscript

Reference [8] of the paper (OpenAI, "Turn-based stochastic mean-payoff games in deterministic
quasipolynomial time", manuscript dated October 5, 2026) is in the repository cited as [10], in the
directory
`preprints/Turn-Based-Stochastic-Mean-Payoff-Games-in-Deterministic-Quasipolynomial-Time-October-5-2026`.
