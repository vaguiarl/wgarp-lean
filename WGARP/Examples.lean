import WGARP.GARP
import WGARP.CompensatedDemand

set_option autoImplicit false

/-!
# Numerical examples from the main text

This file kernel-checks the two finite datasets used in the introductory
discussion and the average-budget calculation used in the retained
counterfactual-demand example.
-/

namespace WGARP

/-! ## Three observations that satisfy WGARP but violate GARP -/

/-- Prices in the three-good example of Keiding (2013). -/
def threeObservationPrices (t : Fin 3) : Bundle 3 :=
  if t = 0 then ![4, 1, 5]
  else if t = 1 then ![5, 4, 1]
  else ![1, 5, 4]

/-- Choices in the three-good example of Keiding (2013). -/
def threeObservationChoices (t : Fin 3) : Bundle 3 :=
  if t = 0 then ![4, 1, 1]
  else if t = 1 then ![1, 4, 1]
  else ![1, 1, 4]

/-- The paper's three-observation dataset, including all primitive
positivity and nontriviality conditions. -/
def threeObservationDataset : Dataset 3 (Fin 3) where
  price := threeObservationPrices
  choice := threeObservationChoices
  goods_two_le := by omega
  price_pos := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [threeObservationPrices]
  choice_nonneg := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [threeObservationChoices]
  choice_ne_zero := by
    intro t h
    have hzero := congrFun h (0 : Fin 3)
    fin_cases t <;> norm_num [threeObservationChoices] at hzero

/-- The full expenditure table displayed in the paper.  Rows index prices
and columns index choices. -/
def threeObservationExpenditureTable : Fin 3 → Fin 3 → ℝ :=
  ![![22, 13, 25], ![25, 22, 13], ![13, 25, 22]]

theorem threeObservation_expenditure_table (s t : Fin 3) :
    expenditure threeObservationDataset s (threeObservationDataset.choice t) =
      threeObservationExpenditureTable s t := by
  fin_cases s <;> fin_cases t <;>
    norm_num [expenditure, dot, threeObservationDataset, threeObservationPrices,
      threeObservationChoices, threeObservationExpenditureTable, Fin.sum_univ_succ]

/-- The example obeys every binary WGARP restriction. -/
theorem threeObservation_wgarp : WGARP threeObservationDataset := by
  intro s t hweak
  fin_cases s <;> fin_cases t <;>
    norm_num [expenditureGap, dot, threeObservationDataset, threeObservationPrices,
      threeObservationChoices, Fin.sum_univ_succ] at *

/-- The strict direct revealed-preference cycle `0 → 1 → 2 → 0`. -/
theorem threeObservation_strict_cycle :
    StrictDirectRevealed threeObservationDataset 0 1 ∧
      StrictDirectRevealed threeObservationDataset 1 2 ∧
      StrictDirectRevealed threeObservationDataset 2 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [StrictDirectRevealed, expenditureGap, dot, threeObservationDataset,
    threeObservationPrices, threeObservationChoices, Fin.sum_univ_succ, h20, h21]

/-- Although it satisfies WGARP, the three-observation example violates
GARP through its length-three revealed-preference cycle. -/
theorem threeObservation_not_garp : ¬ GARP threeObservationDataset := by
  intro hGARP
  have h01 : DirectRP threeObservationDataset.price threeObservationDataset.choice 0 1 :=
    (directRP_dataset_iff threeObservationDataset 0 1).2
      (le_of_lt threeObservation_strict_cycle.1)
  have h12 : DirectRP threeObservationDataset.price threeObservationDataset.choice 1 2 :=
    (directRP_dataset_iff threeObservationDataset 1 2).2
      (le_of_lt threeObservation_strict_cycle.2.1)
  have hreach :
      RevealedPref threeObservationDataset.price threeObservationDataset.choice 0 2 :=
    (directRP_revealedPref _ _ h01).trans (directRP_revealedPref _ _ h12)
  have hcheap :
      StrictlyCheaperAt threeObservationDataset.price threeObservationDataset.choice 2 0 :=
    (strictlyCheaperAt_dataset_iff threeObservationDataset 2 0).2
      threeObservation_strict_cycle.2.2
  exact hGARP 0 2 hreach hcheap

/-! ## A two-observation compensated-law failure -/

/-- Prices in the two-good compensated-law example. -/
def compensatedExamplePrices : Fin 2 → Bundle 2 :=
  ![![1, 2], ![1, 3]]

/-- Choices in the two-good compensated-law example. -/
def compensatedExampleChoices : Fin 2 → Bundle 2 :=
  ![![6, 0], ![0, 2]]

/-- The two-observation dataset from the compensated-law example. -/
def compensatedExampleDataset : Dataset 2 (Fin 2) where
  price := compensatedExamplePrices
  choice := compensatedExampleChoices
  goods_two_le := by omega
  price_pos := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [compensatedExamplePrices]
  choice_nonneg := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [compensatedExampleChoices]
  choice_ne_zero := by
    intro t h
    fin_cases t
    · have hzero := congrFun h (0 : Fin 2)
      norm_num [compensatedExampleChoices] at hzero
    · have hzero := congrFun h (1 : Fin 2)
      norm_num [compensatedExampleChoices] at hzero

/-- The two cross-expenditures are `p¹·x² = 4 < 6 = p¹·x¹` and
`p²·x¹ = 6 = p²·x²`. -/
theorem compensatedExample_cross_expenditures :
    dot (compensatedExamplePrices 0) (compensatedExampleChoices 1) = 4 ∧
      dot (compensatedExamplePrices 0) (compensatedExampleChoices 0) = 6 ∧
      dot (compensatedExamplePrices 1) (compensatedExampleChoices 0) = 6 ∧
      dot (compensatedExamplePrices 1) (compensatedExampleChoices 1) = 6 := by
  norm_num [dot, compensatedExamplePrices, compensatedExampleChoices, Fin.sum_univ_succ]

/-- The example violates WGARP: observation 1 weakly reveals its choice over
choice 0, while observation 0 strictly reveals its choice over choice 1. -/
theorem compensatedExample_not_wgarp : ¬ WGARP compensatedExampleDataset := by
  intro hWGARP
  have hbad := hWGARP (0 : Fin 2) (1 : Fin 2)
  norm_num [expenditureGap, dot, compensatedExampleDataset, compensatedExamplePrices,
    compensatedExampleChoices, Fin.sum_univ_succ] at hbad

/-- After compensating the second budget so that the original bundle remains
affordable, the price and choice changes have dot product `2`, contradicting
the nonpositive compensated law. -/
theorem compensatedExample_positive_change :
    dot (compensatedExamplePrices 1 - compensatedExamplePrices 0)
        (compensatedExampleChoices 1 - compensatedExampleChoices 0) = 2 := by
  norm_num [dot, compensatedExamplePrices, compensatedExampleChoices, Fin.sum_univ_succ]

theorem compensatedExample_compensated_law_fails :
    0 < dot (compensatedExamplePrices 1 - compensatedExamplePrices 0)
      (compensatedExampleChoices 1 - compensatedExampleChoices 0) := by
  rw [compensatedExample_positive_change]
  norm_num

/-! ## The average-budget cover in the retained demand example -/

/-- The average of the three observed price vectors. -/
noncomputable def threeObservationAveragePrice : Bundle 3 :=
  ![(10 : ℝ) / 3, 10 / 3, 10 / 3]

theorem threeObservation_average_price :
    threeObservationAveragePrice =
      (threeObservationPrices 0 + threeObservationPrices 1 + threeObservationPrices 2) / 3 := by
  funext i
  fin_cases i
  · change (10 : ℝ) / 3 = (4 + 5 + 1) / 3
    norm_num
  · change (10 : ℝ) / 3 = (1 + 4 + 5) / 3
    norm_num
  · change (10 : ℝ) / 3 = (5 + 1 + 4) / 3
    norm_num

/-- Every observed wealth is 22. -/
theorem threeObservation_observed_wealth (t : Fin 3) :
    expenditure threeObservationDataset t (threeObservationDataset.choice t) = 22 := by
  fin_cases t <;> norm_num [expenditure, dot, threeObservationDataset,
    threeObservationPrices, threeObservationChoices, Fin.sum_univ_succ]

/-- Any bundle affordable at the average price and average wealth is
affordable in at least one of the three original budgets. -/
theorem threeObservation_average_budget_cover (x : Bundle 3)
    (hx : dot threeObservationAveragePrice x ≤ 22) :
    ∃ t : Fin 3, expenditure threeObservationDataset t x ≤ 22 := by
  by_contra hcover
  have h0 : 22 < expenditure threeObservationDataset 0 x := by
    exact lt_of_not_ge fun h => hcover ⟨0, h⟩
  have h1 : 22 < expenditure threeObservationDataset 1 x := by
    exact lt_of_not_ge fun h => hcover ⟨1, h⟩
  have h2 : 22 < expenditure threeObservationDataset 2 x := by
    exact lt_of_not_ge fun h => hcover ⟨2, h⟩
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [expenditure, dot, threeObservationDataset, threeObservationPrices,
    threeObservationAveragePrice, Fin.sum_univ_succ, h20, h21] at hx h0 h1 h2
  linarith

/-- Each old choice costs 20 at the average price, strictly less than the
average wealth 22. -/
theorem threeObservation_choice_strictly_affordable_at_average (t : Fin 3) :
    dot threeObservationAveragePrice (threeObservationDataset.choice t) = 20 := by
  fin_cases t <;>
    norm_num [dot, threeObservationAveragePrice, threeObservationDataset,
      threeObservationChoices, Fin.sum_univ_succ]

/-- Numerical heart of the retained counterfactual-demand example.  Every
candidate from the average budget lies in an old budget, and the corresponding
old choice lies strictly inside the average budget. -/
theorem threeObservation_average_budget_cross_affordability (x : Bundle 3)
    (hx : dot threeObservationAveragePrice x ≤ 22) :
    ∃ t : Fin 3,
      expenditure threeObservationDataset t x ≤
          expenditure threeObservationDataset t (threeObservationDataset.choice t) ∧
        dot threeObservationAveragePrice (threeObservationDataset.choice t) < 22 := by
  obtain ⟨t, ht⟩ := threeObservation_average_budget_cover x hx
  refine ⟨t, ?_, ?_⟩
  · rw [threeObservation_observed_wealth]
    exact ht
  · rw [threeObservation_choice_strictly_affordable_at_average]
    norm_num

/-- The conclusion of the retained counterfactual-demand example: every
asymmetric, strictly increasing preference function rationalizing the three
observations has empty demand at the average price and wealth 22. -/
theorem threeObservation_no_average_demand
    (r : PreferenceFunction 3)
    (hasym : Asymmetric r)
    (hinc : StrictlyIncreasingFirst r)
    (hrat : PreferenceRationalizes threeObservationDataset r) :
    ∀ x : Bundle 3,
      ¬ PreferenceDemand r threeObservationAveragePrice 22 x := by
  intro x hx
  obtain ⟨t, hxt, htstrict⟩ :=
    threeObservation_average_budget_cross_affordability x hx.1.2
  have hp : PositivePrice threeObservationAveragePrice := by
    intro i
    fin_cases i <;> norm_num [threeObservationAveragePrice]
  have hstrict :
      StrictlyPreferred r x (threeObservationDataset.choice t) :=
    preferenceDemand_strictlyPreferred_of_strictlyAffordable
      r threeObservationAveragePrice 22 x
      (threeObservationDataset.choice t) hp (by omega) hasym hinc hx
      (threeObservationDataset.choice_nonneg t) htstrict
  have hweak : 0 ≤ r (threeObservationDataset.choice t) x :=
    hrat t x ⟨hx.1.1, hxt⟩
  exact (not_lt_of_ge hweak) hstrict.2

theorem threeObservation_average_demandSet_empty
    (r : PreferenceFunction 3)
    (hasym : Asymmetric r)
    (hinc : StrictlyIncreasingFirst r)
    (hrat : PreferenceRationalizes threeObservationDataset r) :
    preferenceDemandSet r threeObservationAveragePrice 22 = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  exact threeObservation_no_average_demand r hasym hinc hrat x

end WGARP
