# REStat revision scope

This formalization follows the division agreed after the editorial meeting.

## Included

- Theorem 1 and every lemma used by its retained proof.
- The preference-function necessity argument.
- The finite coherent-CMU construction.
- The symmetric-matrix/simplex CMU construction.
- Pairwise Afriat and Varian characterizations.
- Explicit compact-attainment lemmas addressing the editor's concern about
  strict monotonicity of nested extrema.

## Excluded

- The former Theorem 3 and the demand non-emptiness section.
- Later material removed from the REStat revision.
- The separate WARP project.

These exclusions are deliberate editorial scope decisions, not unproved
holes in the theorem stated by this package.  The root theorem imports every
module in the retained dependency graph, and CI rejects unfinished Lean
proofs.

## Formal strengthening

The existence directions use explicit witnesses:

- statement (ii) uses a finite row/column coalition family;
- statement (iii) uses two standard simplices and a symmetric matrix of
  pairwise utilities; and
- statements (v) and (vi) use closed-form pairwise certificates.

Thus the checked theorem proves the manuscript's existence claims through
the same constructive normal forms used in its proof, while avoiding an
unneeded formalization of every abstract Hausdorff hyperspace of coalitions.

The Lean utilities are defined on all of `ℝ^L` and satisfy their regularity
properties there.  Since the manuscript's commodity space is `ℝ^L_+`, this is
also a conservative strengthening; affordable alternatives remain explicitly
restricted to the nonnegative orthant.
