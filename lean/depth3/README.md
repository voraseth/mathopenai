# Lean sources

Ancillary files of the note "A remark on depth-three circuits and a homogeneous depth-five lower
bound for iterated matrix multiplication". Lean 4.32.0 with Mathlib v4.32.0 (see `lean-toolchain`,
`lakefile.toml`, `lake-manifest.json`).

    lake exe cache get                      # fetch prebuilt Mathlib
    lake build                              # builds the library Depth3Note
    lake env lean Depth3Note/Axioms.lean    # prints the axioms used by each theorem listed below

The last command should print `[propext, Classical.choice, Quot.sound]` for each of the seven
theorems. The library contains no `sorry`.

## What is proved

Numbers refer to the note. Every statement is a `def ... : Prop` in `Depth3Note/Statements.lean`;
the theorem proving it is named in the table.

| Note | Statement (`Statements.lean`) | Theorem | File |
|---|---|---|---|
| Hypothesis A | `HypothesisA n₀` | none: a hypothesis, never proved or assumed as an axiom | `Statements.lean` |
| Lemma 1, for the variables of `IMM_{N,N}` (`V = N³`) | `Lemma1Statement` | `lemma1` | `Lemma1.lean` |
| Lemma 2 | `Lemma2Statement` | `lemma2` | `Lemma2.lean` |
| Theorem 3(i) | `Theorem3iStatement` | `theorem3i` | `Theorem3.lean` |
| Theorem 3(ii), inequality | `Theorem3iiStatement` | `theorem3ii` | `Lemma2.lean` |
| Theorem 3(ii), printed equality (for `n ≥ 2`) | `Theorem3iiRewriteStatement` | `theorem3ii_rewrite` | `Theorem3ii.lean` |
| Lemma 4, determinant | `Lemma4DetStatement` | `lemma4_det` | `Lemma4.lean` |
| Corollary 5, determinant, with `c = 1/4800` | `Corollary5DetStatement` | `corollary5_det` | `Corollary5.lean` |

## What is not proved

* Hypothesis A. It is the statement of the cited manuscript and enters `theorem3i`, `theorem3ii`
  and `corollary5_det` as an explicit hypothesis.
* The permanent halves of Lemma 4 and Corollary 5. The full statements are written down as
  `Lemma4Statement` and `Corollary5Statement` in `Statements.lean`, but no theorem proves them.
* Lemma 1 for a general variable set, Proposition 6 (the upper bound), the bound `n^{Ω(log n)}`
  derived from the literature, and the remark in the proof of Corollary 5 that any `c < 1/800`
  will do.

## Files

    Depth3Note.lean               root module; imports everything below
    Depth3Note/ReleaseDefs.lean   definitions of the depth-five circuit model, its size and IMM,
                                  copied verbatim from the Lean development that accompanies the
                                  cited manuscript (Apache License 2.0, copyright OpenAI); that
                                  development's theorem and proof are not copied and not imported
    Depth3Note/Statements.lean    all statements, as `def ... : Prop`; depth-three circuits (`SPS`)
    Depth3Note/Newton.lean        elementary symmetric polynomials as linear combinations of
                                  products of power sums (existence of coefficients); homogeneous
                                  components
    Depth3Note/Typed.lean         layered circuits with typed gates and their conversion to the
                                  copied circuit structure
    Depth3Note/Lemma1.lean        Lemma 1
    Depth3Note/Theorem3.lean      IMM is homogeneous; substitution of zero; Theorem 3(i)
    Depth3Note/Theorem3ii.lean    Theorem 3(ii) from the partition bound; the printed equality
    Depth3Note/Lemma2.lean        Lemma 2; Theorem 3(ii)
    Depth3Note/Lemma4.lean        Lemma 4, determinant
    Depth3Note/Corollary5.lean    Corollary 5, determinant
    Depth3Note/Axioms.lean        `#print axioms` for the seven theorems

## Differences from the written proofs

The formal proofs establish the statements and do not follow the written proofs step by step.

* Lemma 1: the circuit is built without the normalisation step, and only the existence of the
  coefficients expressing `e_k` through products of power sums is proved (from Newton's
  recurrence); the closed form displayed in the note is not checked.
* Lemma 4: the determinant is computed by a block factorisation, not by the cycle-cover argument,
  and the formal statement does not say that the same matrix has permanent `IMM_{n,n}`.
* Depth-three circuits: the affine forms of an `SPS` are not required to be distinct. This only
  enlarges the class of circuits, so the lower bounds on `s + B` are at least as strong.
* This development and the Lean development of the cited manuscript have not been combined in one
  build.
