import WGARP.KAcyclicity

set_option autoImplicit false

/-!
# The four-observation `3`-acyclicity example

This file formalizes the numerical example immediately following Theorem 2.
Its first three revealed-preference comparisons are weak equalities and its
closing comparison is strict.  Consequently the data contain a cycle of
length four and violate GARP, while an exhaustive exact-arithmetic check shows
that no paper-exact cycle of length three (including cycles with repeated
observations) exists.
-/

namespace WGARP

/-- The four price vectors in the example following Theorem 2. -/
noncomputable def fourObservationPrices : Fin 4 → Bundle 3 :=
  fun t ↦
    if t.val = 0 then ![1, 1, (1 : ℝ) / 2]
    else if t.val = 1 then ![1, 1, 1]
    else if t.val = 2 then ![1, (1 : ℝ) / 2, 1]
    else ![1, (21 : ℝ) / 10, 2]

/-- The four chosen bundles in the example following Theorem 2. -/
def fourObservationChoices : Fin 4 → Bundle 3 :=
  fun t ↦
    if t.val = 0 then ![8, 1, 8]
    else if t.val = 1 then ![5, 5, 6]
    else if t.val = 2 then ![5, 6, 5]
    else ![8, 8, 1]

/-- The paper's four-observation dataset, with all primitive regularity
conditions discharged from its exact rational coordinates. -/
noncomputable def fourObservationDataset : Dataset 3 (Fin 4) where
  price := fourObservationPrices
  choice := fourObservationChoices
  goods_two_le := by omega
  price_pos := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [fourObservationPrices]
  choice_nonneg := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [fourObservationChoices]
  choice_ne_zero := by
    intro t h
    have hzero := congrFun h (0 : Fin 3)
    fin_cases t <;> norm_num [fourObservationChoices] at hzero

/-- The complete expenditure table. Rows are prices and columns are chosen
bundles; decimal entries in the manuscript are represented by exact
rationals. -/
noncomputable def fourObservationExpenditureTable : Fin 4 → Fin 4 → ℝ :=
  ![![13, 13, (27 : ℝ) / 2, (33 : ℝ) / 2],
    ![17, 16, 16, 17],
    ![(33 : ℝ) / 2, (27 : ℝ) / 2, 13, 13],
    ![(261 : ℝ) / 10, (55 : ℝ) / 2, (138 : ℝ) / 5,
      (134 : ℝ) / 5]]

theorem fourObservation_expenditure_table (s t : Fin 4) :
    expenditure fourObservationDataset s (fourObservationDataset.choice t) =
      fourObservationExpenditureTable s t := by
  fin_cases s <;> fin_cases t <;>
    norm_num [expenditure, dot, fourObservationDataset, fourObservationPrices,
      fourObservationChoices, fourObservationExpenditureTable,
      Fin.sum_univ_succ]

/-- The complete weak direct-revelation graph: four loops and the displayed
four-cycle, with no other edges. -/
theorem fourObservation_directRevealed_iff (s t : Fin 4) :
    DirectRevealed fourObservationDataset s t ↔
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 2) ∨
        (s = 2 ∧ t = 3) ∨ (s = 3 ∧ t = 0) := by
  fin_cases s <;> fin_cases t <;>
    norm_num [DirectRevealed, expenditureGap, dot, fourObservationDataset,
      fourObservationPrices, fourObservationChoices, Fin.sum_univ_succ] <;>
    decide

/-- The closing edge `3 → 0` is the graph's unique strict direct edge. -/
theorem fourObservation_strictDirectRevealed_iff (s t : Fin 4) :
    StrictDirectRevealed fourObservationDataset s t ↔
      s = 3 ∧ t = 0 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [StrictDirectRevealed, expenditureGap, dot,
      fourObservationDataset, fourObservationPrices, fourObservationChoices,
      Fin.sum_univ_succ] <;>
    decide

/-- The displayed cycle has the paper's orientation
`0 → 1 → 2 → 3 → 0`; only its closing edge is strict. -/
theorem fourObservation_revealed_cycle :
    DirectRevealed fourObservationDataset 0 1 ∧
      DirectRevealed fourObservationDataset 1 2 ∧
      DirectRevealed fourObservationDataset 2 3 ∧
      StrictDirectRevealed fourObservationDataset 3 0 := by
  norm_num [DirectRevealed, StrictDirectRevealed, expenditureGap, dot,
    fourObservationDataset, fourObservationPrices, fourObservationChoices,
    Fin.sum_univ_succ]

/-- The displayed observations form an exact length-four cycle in the sense
used by `KAcyclic`. -/
theorem fourObservation_has_four_cycle :
    HasKCycle fourObservationDataset 4 := by
  refine ⟨[0, 1, 2, 3], by simp, by simp, ?_, ?_⟩
  · simpa using
      ⟨fourObservation_revealed_cycle.1,
        fourObservation_revealed_cycle.2.1,
        fourObservation_revealed_cycle.2.2.1⟩
  · simpa using fourObservation_revealed_cycle.2.2.2

/-- The length-four revealed-preference cycle violates GARP. -/
theorem fourObservation_not_garp :
    ¬ GARP fourObservationDataset := by
  intro hGARP
  have h01 : DirectRP fourObservationDataset.price
      fourObservationDataset.choice 0 1 :=
    (directRevealed_iff_directRP fourObservationDataset 0 1).mp
      fourObservation_revealed_cycle.1
  have h12 : DirectRP fourObservationDataset.price
      fourObservationDataset.choice 1 2 :=
    (directRevealed_iff_directRP fourObservationDataset 1 2).mp
      fourObservation_revealed_cycle.2.1
  have h23 : DirectRP fourObservationDataset.price
      fourObservationDataset.choice 2 3 :=
    (directRevealed_iff_directRP fourObservationDataset 2 3).mp
      fourObservation_revealed_cycle.2.2.1
  have hreach : RevealedPref fourObservationDataset.price
      fourObservationDataset.choice 0 3 :=
    ((directRP_revealedPref _ _ h01).trans
      (directRP_revealedPref _ _ h12)).trans
        (directRP_revealedPref _ _ h23)
  have hcheap : StrictlyCheaperAt fourObservationDataset.price
      fourObservationDataset.choice 3 0 :=
    (strictlyCheaperAt_dataset_iff fourObservationDataset 3 0).2
      fourObservation_revealed_cycle.2.2.2
  exact hGARP 0 3 hreach hcheap

/-- Every exact length-three candidate is ruled out by the expenditure table.
The finite check ranges over all `4^3` triples, so repeated observations are
included rather than silently assuming a simple cycle. -/
theorem fourObservation_three_acyclic :
    KAcyclic fourObservationDataset 3 := by
  rintro ⟨l, hlength, hne, hchain, hclose⟩
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlength
  simp only [List.isChain_cons] at hchain
  simp only [List.head_cons] at hclose
  rw [fourObservation_strictDirectRevealed_iff] at hclose
  rcases hclose with ⟨rfl, rfl⟩
  have hchain' :
      DirectRevealed fourObservationDataset 0 b ∧
        DirectRevealed fourObservationDataset b 3 := by
    simpa using hchain
  rw [fourObservation_directRevealed_iff,
    fourObservation_directRevealed_iff] at hchain'
  fin_cases b <;> simp at hchain'

end WGARP
