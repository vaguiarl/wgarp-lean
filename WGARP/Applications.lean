/-
SPDX-License-Identifier: Apache-2.0
This Lean source file is licensed under the Apache License, Version 2.0.
See LICENSE-LEAN for the terms and NOTICE-LEAN for attribution.
-/

import WGARP.TheoremOne
import WGARP.GlobalAfriat
import WGARP.Examples

/-!
# Concrete applications of the Afriat and WGARP characterizations

These checked clients instantiate the public theorems on concrete datasets.
They are part of the downstream WGARP package, not an upstream MathEconLib port.
-/

namespace WGARP.Applications

open WGARP

/-- The new six-way theorem supplies a coherent-CMU rationalizer for the
checked three-observation example; classical Afriat rules out a regular
single-utility rationalizer for exactly the same data. -/
theorem cmu_but_not_regular_utility :
    StatementII threeObservationDataset ∧
      ¬ HasRegularUtilityRationalization threeObservationDataset := by
  have hnew := theorem_one threeObservationDataset
  refine ⟨hnew.2.1.mpr (hnew.2.2.1.mpr threeObservation_wgarp), ?_⟩
  intro hregular
  exact threeObservation_not_garp
    ((garp_iff_hasRegularUtilityRationalization threeObservationDataset).mpr hregular)

def twoPrices (t : Fin 2) : Bundle 2 :=
  if t = 0 then ![1, 2] else ![2, 1]

def twoChoices (t : Fin 2) : Bundle 2 :=
  if t = 0 then ![2, 0] else ![0, 2]

def twoDataset : Dataset 2 (Fin 2) where
  price := twoPrices
  choice := twoChoices
  goods_two_le := by omega
  price_pos := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [twoPrices]
  choice_nonneg := by
    intro t i
    fin_cases t <;> fin_cases i <;> norm_num [twoChoices]
  choice_ne_zero := by
    intro t h
    fin_cases t
    · have hz := congrFun h (0 : Fin 2)
      norm_num [twoChoices] at hz
    · have hz := congrFun h (1 : Fin 2)
      norm_num [twoChoices] at hz

def twoLevels (_t : Fin 2) : ℝ := 2

def twoMultipliers (_t : Fin 2) : ℝ := 1

theorem two_positive_multipliers : PositiveMultipliers twoMultipliers := by
  intro t
  norm_num [twoMultipliers]

theorem two_afriat_inequalities :
    AfriatInequalities twoLevels twoMultipliers twoDataset.price twoDataset.choice := by
  intro s t
  fin_cases s <;> fin_cases t <;>
    norm_num [AfriatInequalities, globalAfriatSupport, twoLevels, twoMultipliers,
      twoDataset, twoPrices, twoChoices, dot, Fin.sum_univ_succ]

/-- The named finite Afriat theorem converts the explicit numerical
certificate into a continuous, concave, strictly increasing rationalizer. -/
theorem two_has_regular_utility : HasRegularUtilityRationalization twoDataset := by
  apply (garp_iff_hasRegularUtilityRationalization twoDataset).mp
  apply (garp_iff_exists_afriatInequalities twoDataset).mpr
  exact ⟨twoLevels, twoMultipliers, two_positive_multipliers, two_afriat_inequalities⟩

end WGARP.Applications
