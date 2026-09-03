import WGARP.FiniteCMU
import Mathlib.Data.Fintype.OfMap

set_option autoImplicit false

/-!
# The three-moods CMU example

This file formalizes the stoic, hedonistic, and flexible coalition example
from the main text.  Utilities with identical coefficients are represented by
the same `MoodAgent`: in particular, `common` belongs to the stoic and
hedonistic coalitions, while the two members of the flexible coalition are
also members of the stoic and hedonistic coalitions respectively.  Thus the
claimed coherence is literal set intersection rather than equality of
extensionally identical, separately tagged functions.
-/

namespace WGARP

/-- The three coalitions (or moods) in the example. -/
inductive MoodCoalition
  | stoic
  | hedonistic
  | flexible
  deriving DecidableEq

instance : Fintype MoodCoalition :=
  Fintype.ofList [.stoic, .hedonistic, .flexible] (by
    intro c
    cases c <;> simp)

instance : Nonempty MoodCoalition := ⟨.stoic⟩

/-- The five distinct linear utilities occurring in the example.

The paper lists eight coalition memberships, but three pairs of entries are
the same utility function.  The constructors encode coefficient triples:
`common = (.5,.5,.5)`, `stoicFlexible = (.6,.5,.4)`,
`stoicSeven = (.7,.5,.3)`, `hedonisticFlexible = (.5,.6,.4)`, and
`hedonisticSeven = (.5,.7,.3)`.
-/
inductive MoodAgent
  | common
  | stoicFlexible
  | stoicSeven
  | hedonisticFlexible
  | hedonisticSeven
  deriving DecidableEq

instance : Fintype MoodAgent :=
  Fintype.ofList
    [.common, .stoicFlexible, .stoicSeven, .hedonisticFlexible,
      .hedonisticSeven] (by
        intro i
        cases i <;> simp)

/-- The agents participating in each mood. -/
def moodMembers : MoodCoalition → Finset MoodAgent
  | .stoic => {.common, .stoicFlexible, .stoicSeven}
  | .hedonistic => {.common, .hedonisticFlexible, .hedonisticSeven}
  | .flexible => {.stoicFlexible, .hedonisticFlexible}

/-- The finite coalition system of the example. -/
def moodCoalitions : FiniteCoalitionSystem MoodCoalition MoodAgent where
  members := moodMembers
  members_nonempty := by
    intro c
    cases c <;> simp [moodMembers]

/-- Coefficient vector of each distinct linear utility. -/
noncomputable def moodWeights : MoodAgent → Bundle 3
  | .common => ![(1 / 2 : ℝ), 1 / 2, 1 / 2]
  | .stoicFlexible => ![(3 / 5 : ℝ), 1 / 2, 2 / 5]
  | .stoicSeven => ![(7 / 10 : ℝ), 1 / 2, 3 / 10]
  | .hedonisticFlexible => ![(1 / 2 : ℝ), 3 / 5, 2 / 5]
  | .hedonisticSeven => ![(1 / 2 : ℝ), 7 / 10, 3 / 10]

/-- The five linear utility functions used by the moods CMU. -/
noncomputable def moodUtility (i : MoodAgent) : Utility 3 :=
  fun x => dot (moodWeights i) x

/-- The coalitions in the moods example are pairwise coherent. -/
theorem moodCoalitions_coherent : Coherent moodCoalitions := by
  intro c d
  cases c <;> cases d
  · exact ⟨.common, by simp [moodCoalitions, moodMembers], by simp [moodCoalitions, moodMembers]⟩
  · exact ⟨.common, by simp [moodCoalitions, moodMembers], by simp [moodCoalitions, moodMembers]⟩
  · exact ⟨.stoicFlexible, by simp [moodCoalitions, moodMembers], by simp [moodCoalitions, moodMembers]⟩
  · exact ⟨.common, by simp [moodCoalitions, moodMembers], by simp [moodCoalitions, moodMembers]⟩
  · exact ⟨.common, by simp [moodCoalitions, moodMembers], by simp [moodCoalitions, moodMembers]⟩
  · exact ⟨.hedonisticFlexible, by simp [moodCoalitions, moodMembers], by simp [moodCoalitions, moodMembers]⟩
  · exact ⟨.stoicFlexible, by simp [moodCoalitions, moodMembers], by simp [moodCoalitions, moodMembers]⟩
  · exact ⟨.hedonisticFlexible, by simp [moodCoalitions, moodMembers], by simp [moodCoalitions, moodMembers]⟩
  · exact ⟨.stoicFlexible, by simp [moodCoalitions, moodMembers], by simp [moodCoalitions, moodMembers]⟩

/-- The stoic bundle `x^s = (21,0,0)`. -/
def xStoic : Bundle 3 := ![(21 : ℝ), 0, 0]

/-- The hedonistic bundle `x^h = (0,10.8,10.8)`. -/
noncomputable def xHedonistic : Bundle 3 := ![(0 : ℝ), 54 / 5, 54 / 5]

/-- The flexible bundle `x^f = (10,10,0)`. -/
def xFlexible : Bundle 3 := ![(10 : ℝ), 10, 0]

/-- The bundle used to demonstrate incompleteness, `y = (14,0,7)`. -/
def yIncomplete : Bundle 3 := ![(14 : ℝ), 0, 7]

/-- The first displayed comparison in the paper: the stoic coalition secures
the exact lower bound `0.5`. -/
theorem mood_cmu_stoic_flexible_lower_bound :
    (1 / 2 : ℝ) ≤ finiteCMU moodCoalitions moodUtility xStoic xFlexible := by
  have hscore :
      coalitionScore moodCoalitions moodUtility .stoic xStoic xFlexible =
        (1 / 2 : ℝ) := by
    norm_num [coalitionScore, moodCoalitions, moodMembers, moodUtility,
      moodWeights, xStoic, xFlexible, dot, Fin.sum_univ_succ]
  unfold finiteCMU
  rw [← hscore]
  exact Finset.le_sup' (fun c ↦
    coalitionScore moodCoalitions moodUtility c xStoic xFlexible) (by simp)

/-- The second displayed comparison: the flexible coalition secures `0.2`. -/
theorem mood_cmu_flexible_hedonistic_lower_bound :
    (1 / 5 : ℝ) ≤ finiteCMU moodCoalitions moodUtility xFlexible xHedonistic := by
  have hscore :
      coalitionScore moodCoalitions moodUtility .flexible xFlexible xHedonistic =
        (1 / 5 : ℝ) := by
    norm_num [coalitionScore, moodCoalitions, moodMembers, moodUtility,
      moodWeights, xFlexible, xHedonistic, dot, Fin.sum_univ_succ,
      Matrix.cons_val_two]
  unfold finiteCMU
  rw [← hscore]
  exact Finset.le_sup' (fun c ↦
    coalitionScore moodCoalitions moodUtility c xFlexible xHedonistic) (by simp)

/-- The third displayed comparison: the hedonistic coalition secures `0.3`. -/
theorem mood_cmu_hedonistic_stoic_lower_bound :
    (3 / 10 : ℝ) ≤ finiteCMU moodCoalitions moodUtility xHedonistic xStoic := by
  have hscore :
      coalitionScore moodCoalitions moodUtility .hedonistic xHedonistic xStoic =
        (3 / 10 : ℝ) := by
    norm_num [coalitionScore, moodCoalitions, moodMembers, moodUtility,
      moodWeights, xHedonistic, xStoic, dot, Fin.sum_univ_succ,
      Matrix.cons_val_two]
  unfold finiteCMU
  rw [← hscore]
  exact Finset.le_sup' (fun c ↦
    coalitionScore moodCoalitions moodUtility c xHedonistic xStoic) (by simp)

/-- The three displayed inequalities generate a strict preference cycle. -/
theorem mood_cmu_strict_cycle :
    0 < finiteCMU moodCoalitions moodUtility xStoic xFlexible ∧
    0 < finiteCMU moodCoalitions moodUtility xFlexible xHedonistic ∧
    0 < finiteCMU moodCoalitions moodUtility xHedonistic xStoic := by
  constructor
  · linarith [mood_cmu_stoic_flexible_lower_bound]
  constructor
  · linarith [mood_cmu_flexible_hedonistic_lower_bound]
  · linarith [mood_cmu_hedonistic_stoic_lower_bound]

/-- `y` is not weakly preferred to `x^f` by the moods CMU. -/
theorem mood_cmu_y_not_preferred_to_flexible :
    finiteCMU moodCoalitions moodUtility yIncomplete xFlexible < 0 := by
  unfold finiteCMU
  apply lt_of_le_of_lt (Finset.sup'_le Finset.univ_nonempty _ (fun c _hc ↦ ?_))
    (show (-1 / 10 : ℝ) < 0 by norm_num)
  cases c <;>
    norm_num [coalitionScore, moodCoalitions, moodMembers, moodUtility,
      moodWeights, yIncomplete, xFlexible, dot, Fin.sum_univ_succ,
      Matrix.cons_val_two]

/-- `x^f` is not weakly preferred to `y` either.  Together with the previous
theorem, this is the paper's claimed incompleteness witness. -/
theorem mood_cmu_flexible_not_preferred_to_y :
    finiteCMU moodCoalitions moodUtility xFlexible yIncomplete < 0 := by
  unfold finiteCMU
  apply lt_of_le_of_lt (Finset.sup'_le Finset.univ_nonempty _ (fun c _hc ↦ ?_))
    (show (-1 / 10 : ℝ) < 0 by norm_num)
  cases c <;>
    norm_num [coalitionScore, moodCoalitions, moodMembers, moodUtility,
      moodWeights, xFlexible, yIncomplete, dot, Fin.sum_univ_succ,
      Matrix.cons_val_two]

/-- The exact sign-form statement that `y` and `x^f` are incomparable. -/
theorem mood_cmu_incomplete_pair :
    ¬ 0 ≤ finiteCMU moodCoalitions moodUtility yIncomplete xFlexible ∧
    ¬ 0 ≤ finiteCMU moodCoalitions moodUtility xFlexible yIncomplete := by
  exact ⟨not_le_of_gt mood_cmu_y_not_preferred_to_flexible,
    not_le_of_gt mood_cmu_flexible_not_preferred_to_y⟩

end WGARP
