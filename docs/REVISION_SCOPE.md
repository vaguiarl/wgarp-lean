# REStat revision scope

The package distinguishes the post-editorial retained core from one explicit
author-requested extension. This prevents the repository from silently
certifying results that were removed from the planned REStat revision.

## Post-editorial retained core

The retained formal scope contains:

- the revealed-preference definitions, WGARP, GARP, and the finite global
  Afriat theorem used in the argument;
- Theorem 1 and all six of its equivalent statements;
- the main-text CMU results: continuity and monotonicity of finite and
  compact-parameter CMUs, asymmetry from rationalization, asymmetry from
  coherence, and the symmetric-matrix/simplex skew-symmetry result;
- Lemma 5 and its strict cross-affordability converse;
- Lemma 6 for the justifiable model, including its compact numeric
  representation and the demand/separation analysis needed by the proof; and
- the finite main-text examples for WGARP versus GARP, compensated demand,
  supermajority voting, the moods CMU, and the average-budget empty-demand
  counterexample.

The concrete average-budget result proves emptiness for one stated market and
one stated dataset. It is independent of, and should not be confused with,
the excluded general nonemptiness theorem.

## Explicit public-package extension

At the author's request, the package also formalizes Theorem 2 even though it
lies beyond the core retained after the editor meeting. The extension includes:

- the manuscript's exact fixed-length `k`-cycle convention, including repeated
  observations;
- the equivalence between `k`-acyclicity and GARP on every nonempty restriction
  containing at most `k` observations;
- the Nakamura lower-bound predicate and its threshold-three/coherence
  equivalence;
- both directions of Theorem 2 for arbitrary finite CMU witnesses with
  continuous, strictly increasing agents;
- the specialization at `k = 2`, recovering WGARP; and
- the exact four-observation example that is `3`-acyclic but not GARP.

The constructive proof is slightly stronger than the existential statement:
it selects continuous, concave, strictly increasing global Afriat utilities
on every nonempty subset of observations of size at most `k`. The theorem's
public witness type records continuity (implicit in the paper's use of
`C(X)`) and strict increase, but does not add concavity as an assumption.

## Excluded

The following remain outside the package:

- the global Varian-numbering clause quoted as classical Afriat background
  (Theorem 1's distinct pairwise Varian condition remains checked);
- former Theorem 3 and its Schofield/core-based nonemptiness conclusion;
- former Section 6 on preference maximization, core optimization,
  first-order conditions, expenditure minimization, and duality; and
- the separate WARP characterization and other online-appendix extensions.

These are editorial scope decisions, not placeholders or unfinished branches
inside the theorems exported by `WGARP.lean`.

## Formal-strengthening boundary

Several implementation choices make the checked statements more explicit or
stronger without changing their economic conclusions:

- Theorem 1(ii) uses a finite row/column coalition family, and Theorem 1(iii)
  uses two standard simplices and a symmetric matrix of pairwise utilities.
- Coherence yields the numerical inequality `r(x,y) + r(y,x) ≤ 0`, not only
  the two sign implications stated in prose.
- Lemma 6 is first proved for the relational sign content of a justifiable
  family, where compactness is unnecessary; compactness and payoff continuity
  are then used to identify that relation with an attained numerical maximum.
- Utilities are defined on all of `ℝ^L` and often satisfy continuity,
  concavity, and monotonicity there. Affordable alternatives remain restricted
  to the nonnegative orthant, as in the manuscript.
- Compact CMUs are represented through explicit compact parameter spaces. The
  package does not reconstruct the full compact-convergence topology on
  `C(X)` or the Hausdorff hyperspace of all abstract coalition families.

The root import reaches every module in this boundary, and the CI workflow is
configured to reject unfinished Lean proofs and project-defined axioms.
