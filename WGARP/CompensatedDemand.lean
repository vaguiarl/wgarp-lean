import WGARP.Demand

set_option autoImplicit false

/-!
# Lemma 5: the compensated law of demand

The main theorem formalizes Lemma 5 of the retained main text.  Its proof is
slightly stronger than the prose proof: it derives the needed revealed-price
inequality directly from the two demand conditions, without importing
Walras' law as a separate assumption.
-/

namespace WGARP

variable {L : ℕ}

/-- Two choices from compensated budgets cannot be strictly cross-affordable
at the original prices when the preference function is asymmetric and
strictly increasing. -/
theorem demand_cross_expenditure
    (r : PreferenceFunction L)
    (p p' : Bundle L) (w : ℝ) (x x' : Bundle L)
    (hp : PositivePrice p) (hL : 0 < L)
    (hasym : Asymmetric r) (hinc : StrictlyIncreasingFirst r)
    (hx : PreferenceDemand r p w x)
    (hx' : PreferenceDemand r p' (dot p' x) x') :
    dot p x ≤ dot p x' := by
  by_contra hnot
  have hcheap : dot p x' < dot p x := lt_of_not_ge hnot
  obtain ⟨z, hznonneg, hzdom, hzcost⟩ :=
    exists_strictDominating_below_expenditure p x x' hp hL hx'.1.1 hcheap
  have hzbudget : InBudget p w z :=
    ⟨hznonneg, hzcost.trans hx.1.2⟩
  have hxz : 0 ≤ r x z := hx.2 z hzbudget
  have hxbudget' : InBudget p' (dot p' x) x :=
    ⟨hx.1.1, le_rfl⟩
  have hx'x : 0 ≤ r x' x := hx'.2 x hxbudget'
  have hzx : 0 < r z x :=
    lt_of_le_of_lt hx'x (hinc x hzdom)
  have hxzneg : r x z < 0 := hasym.2 z x hzx
  exact (not_lt_of_ge hxz) hxzneg

/-- **Lemma 5 (compensated law of demand).**  If `x` is demanded at
`(p,w)` and `x'` is demanded after changing prices to `p'` while compensating
wealth to `p'·x`, then the price and demand changes have nonpositive dot
product. -/
theorem compensated_law_of_demand
    (r : PreferenceFunction L)
    (p p' : Bundle L) (w : ℝ) (x x' : Bundle L)
    (hp : PositivePrice p) (_hp' : PositivePrice p') (hL : 0 < L)
    (hasym : Asymmetric r) (hinc : StrictlyIncreasingFirst r)
    (hx : PreferenceDemand r p w x)
    (hx' : PreferenceDemand r p' (dot p' x) x') :
    dot (p' - p) (x' - x) ≤ 0 := by
  have hp_cross : dot p x ≤ dot p x' :=
    demand_cross_expenditure r p p' w x x' hp hL hasym hinc hx hx'
  have hp'_cross : dot p' x' ≤ dot p' x := hx'.1.2
  rw [dot_sub, dot_sub_left, dot_sub_left]
  linarith

/-- The converse calculation stated immediately after Lemma 5: a two-choice
WGARP violation makes the compensated-law expression strictly positive. -/
theorem compensated_law_fails_of_cross_affordability
    (p p' x x' : Bundle L)
    (hfirst : dot p x' ≤ dot p x)
    (hsecond : dot p' x < dot p' x') :
    0 < dot (p' - p) (x' - x) := by
  rw [dot_sub, dot_sub_left, dot_sub_left]
  linarith

end WGARP
