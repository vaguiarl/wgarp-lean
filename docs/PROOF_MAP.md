# Proof map

This table maps the retained paper argument to the Lean modules.  Declaration
names are finalized by the root import `WGARP.lean`.

| Paper item | Lean module | Checked content |
|---|---|---|
| Primitive dataset, budgets, WGARP | `WGARP.Data` | Positive prices, nonnegative/nonzero choices, paper-exact strict dominance, rationalization, binary-cycle form of WGARP |
| Theorem 1(iv) ⇔ (v) ⇔ (vi) | `WGARP.Pairwise` | Direct constructive pair scales, antisymmetric `R`/`V`, positive multipliers, both sign implications, singleton regression |
| Two-observation Afriat step | `WGARP.Afriat` | Symmetric two-plane utility, endpoint touching, budget rationalization, continuity, concavity, strict increase |
| Lemma 1(ii), finite case | `WGARP.FiniteCMU` | Attained inner/outer extrema, strict increase in the first argument and strict decrease in the second |
| Lemma 1(ii), compact case | `WGARP.CompactCMU` | Weierstrass attainment plus nested compact-extremum continuity; corrected witness directions |
| Coherence lemma | `WGARP.FiniteCMU`, `WGARP.CompactCMU` | Strong bound `r(x,y)+r(y,x)≤0`, hence weak and strict sign asymmetry |
| Finite minimax step | `WGARP.Minimax` | Compact/convex simplices, bilinear payoff, Sion saddle point, and negation of the value for symmetric games |
| Symmetric-matrix CMU lemma | `WGARP.MatrixCMU` | Simplex compactness/convexity, mixed agents, coherence, Sion minimax, numerical skew-symmetry |
| Theorem 1(i) ⇒ (iv) | `WGARP.Necessity` | Explicit positive-coordinate interior-budget perturbation and asymmetry contradiction |
| Theorem 1(iv) ⇒ (ii), (iii) | `WGARP.FiniteConstruction`, `WGARP.MatrixCMU` | Pairwise utilities assembled into the finite and mixed CMU witnesses, including `T = 1` |
| Six-way equivalence | `WGARP.TheoremOne` | Named iff theorems and the adjacent equivalence chain in paper order |

## Trust boundary

The project introduces definitions and proves theorems but declares no
axioms.  Its mathematical trust boundary is Lean's kernel plus the pinned
Mathlib dependency.  In particular, Sion's theorem is imported from
`Mathlib.Topology.Sion`; it is not assumed as a local hypothesis.

The repository's CI scans every project `.lean` file for unfinished proofs
or custom `axiom` declarations before building every module reachable from
`WGARP.lean`.

## Deliberate exclusions

The formalization does not include the non-emptiness results formerly stated
as Theorem 3, the removed later sections, or the separate WARP project.  This
matches the post-editorial meeting plan rather than silently certifying text
that is no longer part of the retained theorem.
