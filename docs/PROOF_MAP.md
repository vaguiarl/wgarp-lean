# Proof map

This map lists the paper-facing formal results exported by the root import
`WGARP.lean`. Theorem 1 and the accompanying main-text lemmas and examples are
the post-editorial retained core. Theorem 2 is included as a separately
identified, author-requested extension.

## Retained main-text core

| Paper item | Lean module and principal declarations | Checked content |
|---|---|---|
| Dataset, budgets, demand, and WGARP | `WGARP.Data`: `Dataset`, `Affordable`, `PreferenceRationalizes`, `WGARP`; `WGARP.Demand`: `InBudget`, `PreferenceDemand`, `UtilityDemand` | Positive prices, nonnegative/nonzero observations, paper-exact strict dominance, budget feasibility, rationalization, demand predicates that permit multiple or no maximizers, and the binary-cycle form of WGARP |
| Direct and indirect revealed preference; GARP | `WGARP.GARP`: `DirectRP`, `RevealedPref`, `GraphGARP`, `GARP` | Reflexive-transitive revealed preference, the strict closing edge in GARP, and basic closure/rank lemmas |
| Finite Afriat theorem | `WGARP.GARP`: `garp_iff_exists_afriatInequalities`; `WGARP.GlobalAfriat`: `garp_iff_hasRegularUtilityRationalization`, `garp_iff_exists_afriatCertificate_and_regularUtility` | GARP iff positive global Afriat multipliers exist; their finite lower envelope is continuous, concave, strictly increasing, and rationalizes the dataset; any strictly increasing utility rationalization implies GARP |
| Theorem 1(iv) ⇔ (v) ⇔ (vi) | `WGARP.Pairwise`: `wgarp_iff_pairwiseAfriat`, `wgarp_iff_pairwiseVarian` | Constructive pair scales, antisymmetric `R`/`V`, positive multipliers, and both weak and strict sign implications |
| Two-observation Afriat construction | `WGARP.Afriat`: `pairUtility` and its continuity, concavity, strict-increase, symmetry, and rationalization lemmas | A symmetric two-plane utility built directly from a pairwise certificate, including diagonal/singleton observations |
| Lemma 1, finite CMUs | `WGARP.FiniteCMU`: `finiteCMU_continuous`, `finiteCMU_strictlyIncreasingFirst`, `finiteCMU_strictlyDecreasingSecond` | Attained inner and outer extrema, joint continuity, and strict monotonicity in the two arguments with the correct witness directions |
| Lemma 1, compact CMUs | `WGARP.CompactCMU`: `compactCMU_continuous`, `compactCMU_strictlyIncreasingFirst`, `compactCMU_strictlyDecreasingSecond` | Weierstrass attainment and nested compact-extremum continuity for compact parameter spaces |
| Asymmetry necessity | `WGARP.Necessity`: `wgarp_of_asymmetric_strictlyIncreasing_rationalization` | An explicit positive-coordinate, interior-budget perturbation turns a binary revealed-preference cycle into an asymmetry contradiction |
| Coherence lemma | `WGARP.FiniteCMU`: `finiteCMU_add_swap_nonpos`; `WGARP.CompactCMU`: `compactCMU_add_swap_nonpos` | The stronger bound `r(x,y) + r(y,x) ≤ 0`, hence both weak and strict sign asymmetry |
| Symmetric-matrix CMU lemma | `WGARP.Minimax`: `exists_saddle`, `value_neg_of_transpose_eq`; `WGARP.MatrixCMU`: `matrixCMU_skewSymmetric`, `matrixCMU_add_swap_nonpos` | Compact/convex simplices, Sion minimax for the bilinear payoff, compact coherence, and numerical skew-symmetry of the CMU induced by a symmetric utility matrix |
| Theorem 1(iv) ⇒ (ii), (iii) | `WGARP.FiniteConstruction`: `hasFiniteCoherentCMURationalization_of_wgarp`; `WGARP.MatrixCMU`: `hasMatrixCMURationalization_of_wgarp` | Pairwise utilities assembled into finite row-coalition and mixed-simplex CMU witnesses, including the one-observation case |
| Theorem 1 | `WGARP.TheoremOne`: `statementI_iff_wgarp` through `statementVI_iff_wgarp`, `theorem_one` | The six conditions are each equivalent to WGARP and are exposed as the five adjacent equivalences in manuscript order |
| Singleton boundary case | `WGARP.Singleton`: `singleton_all_statements` | Every statement of Theorem 1 for a finite, nonempty subsingleton observation type |
| Lemma 5 and its converse | `WGARP.CompensatedDemand`: `compensated_law_of_demand`, `compensated_law_fails_of_cross_affordability` | Compensated price and demand changes have nonpositive dot product under asymmetric, strictly increasing preference demand; strict cross-affordability makes that dot product positive |
| Justifiable model identities | `WGARP.Justifiable`: `justifiablyStrictlyPreferred_iff`, `justifiablyPreferred_complete`, `utilityDemand_implies_justifiableDemand` | Weak preference is existential support, its strict part is unanimous strict preference, every nonempty family is complete, and component maximizers are justifiable maximizers |
| Lemma 6, relational form | `WGARP.JustifiableDichotomy`: `justifiableDemand_dichotomy` | Either all finite datasets rationalized by the justifiable relation satisfy GARP, or two positive-price, positive-wealth justifiable demands are each strictly affordable in the other market |
| Lemma 6, analytic gap | `WGARP.JustifiableDichotomy`: `utilityDemandSet_compact`, `utilityDemandSet_convex`, `utilityDemand_expenditure_eq_wealth`, `utilityDemand_upperHemicontinuousAt`, `crossStrictAffordableJustifiableDemands_of_demandDifference` | Compact and convex demand, Walras exhaustion, a specialized Berge upper-hemicontinuity result, Hahn–Banach separation, and a vanishing positive-price perturbation |
| Lemma 6, compact numeric form | `WGARP.JustifiableDichotomy`: `compactJustifiablePreference_nonnegative_iff`, `preferenceDemand_compactJustifiablePreference_iff`, `compactJustifiablePreference_dichotomy` | The attained maximum `max_i (u_i(x)-u_i(y))` has exactly the relational sign and demand; the full dichotomy transfers to numerical preference rationalization |
| Regularity of compact justifiable preferences | `WGARP.JustifiableDichotomy`: `compactJustifiablePreference_complete`, `compactJustifiablePreference_continuous`, `compactJustifiablePreference_strictlyIncreasingFirst` | Completeness, joint continuity, and strict increase of the compact attained representation |
| Supermajority example | `WGARP.Voting`: `thresholdCoalitions_coherent`, `thresholdFiniteCMU_nonneg_iff_majority`, `thresholdFiniteCMU_asymmetric` | Strict-majority coalitions intersect; the CMU sign is equivalent to a qualifying unanimous coalition; coherence yields asymmetry |
| Three-moods example | `WGARP.Moods`: `moodCoalitions_coherent`, `mood_cmu_strict_cycle`, `mood_cmu_incomplete_pair` | Literal shared agents prove coherence; the displayed `1/2`, `1/5`, and `3/10` bounds yield a strict three-cycle; a concrete bundle pair is incomparable |
| Finite numerical examples | `WGARP.Examples`: `threeObservation_wgarp`, `threeObservation_not_garp`, `compensatedExample_compensated_law_fails`, `threeObservation_average_demandSet_empty` | The three-observation data satisfy WGARP but have a strict GARP cycle; the two-observation data violate WGARP and the compensated law; every asymmetric, strictly increasing rationalizer has empty demand at the stated average budget |

## Author-requested Theorem 2 extension

| Paper item | Lean module and principal declarations | Checked content |
|---|---|---|
| Exact `k`-acyclicity | `WGARP.KAcyclicity`: `HasKCycle`, `KAcyclic` | A witness has exactly `k` entries, consecutive weak direct-revelation edges, and a strict final edge; observations may repeat |
| Restriction characterization | `WGARP.KAcyclicity`: `SmallRestrictionGARP`, `kAcyclic_iff_smallRestrictionGARP` | `k`-acyclicity iff every nonempty observation restriction of size at most `k` satisfies GARP; the proof explicitly erases directed loops and pads shorter cycles |
| Nakamura threshold | `WGARP.TheoremTwo`: `NakamuraAtLeast`, `nakamuraAtLeast_three_iff_coherent` | Every subfamily of fewer than `n` coalitions has a common agent; threshold `3` is exactly pairwise coherence |
| Finite CMU witness | `WGARP.TheoremTwo`: `FiniteCMURationalization`, `HasFiniteCMURationalizationWithNakamura` | The existential ranges over arbitrary finite agent and coalition types, nonempty coalitions, continuous and strictly increasing component utilities, CMU rationalization, and the Nakamura lower bound |
| Theorem 2 | `WGARP.TheoremTwo`: `theorem_two` | For a finite nonempty dataset and `k ≥ 2`, finite CMU rationalizability with `NakamuraAtLeast (k + 1)` is equivalent to exact `k`-acyclicity |
| `k = 2` regression | `WGARP.TheoremTwo`: `kAcyclic_two_iff_wgarp`, `theorem_two_at_two` | `2`-acyclicity is WGARP, and Theorem 2 specializes to finite coherent-CMU rationalizability iff WGARP |
| Four-observation example | `WGARP.AcyclicExample`: `fourObservation_three_acyclic`, `fourObservation_not_garp`, `fourObservation_has_four_cycle` | The exact-rational dataset is `3`-acyclic but violates GARP through its length-four cycle; repeated-observation length-three candidates are included in the check |

The constructive direction of Theorem 2 uses all nonempty observation subsets
of size at most `k`. Global Afriat utilities give those agents continuity and
concavity in addition to the continuity and strict increase required by the
theorem. The necessity direction uses only the public witness fields and proves
the theorem for any finite CMU of the stated form.

## Trust boundary

The project introduces definitions and theorems but no axioms. Its
mathematical trust boundary is Lean's kernel plus the pinned Mathlib
dependency. Sion's theorem and Hahn–Banach separation are imported from
Mathlib rather than postulated locally.

The CI workflow scans every project `.lean` file for unfinished proofs or
custom `axiom` declarations before building every module reachable from
`WGARP.lean`.

## Deliberate exclusions

The former Theorem 3/core-based nonemptiness result is not formalized. Neither
are the former Section 6 optimization, first-order-condition, and expenditure
duality results, or the separate WARP project. Theorem 2 and its companion
four-observation example form the sole author-requested extension from the
later section; their inclusion does not restore those excluded results.

The global Varian-numbering clause in the manuscript's quotation of the
classical Afriat theorem is treated as verified external background. This is
distinct from Theorem 1's pairwise Varian certificate, which the package does
check as one of its six equivalent conditions.
