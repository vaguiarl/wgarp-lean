import WGARP.Data
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Budget sets and demand

This file records the demand notions used in the retained main-text results.
They are predicates rather than choice functions, so they faithfully allow
multiple demanded bundles and empty demand correspondences.
-/

namespace WGARP

open scoped BigOperators

variable {L : ℕ}

/-- A price vector is strictly positive in every coordinate. -/
def PositivePrice (p : Bundle L) : Prop :=
  ∀ i, 0 < p i

/-- The nonnegative budget set at prices `p` and wealth `w`. -/
def InBudget (p : Bundle L) (w : ℝ) (x : Bundle L) : Prop :=
  Nonnegative x ∧ dot p x ≤ w

/-- Demand induced by a numerical preference function.  A demanded bundle is
feasible and is weakly preferred, in the sign convention of the paper, to
every feasible alternative. -/
def PreferenceDemand (r : PreferenceFunction L)
    (p : Bundle L) (w : ℝ) (x : Bundle L) : Prop :=
  InBudget p w x ∧ ∀ y, InBudget p w y → 0 ≤ r x y

/-- The strict part of the sign-represented preference relation. -/
def StrictlyPreferred (r : PreferenceFunction L) (x y : Bundle L) : Prop :=
  0 ≤ r x y ∧ r y x < 0

/-- Ordinary utility-maximizing demand. -/
def UtilityDemand (u : Utility L)
    (p : Bundle L) (w : ℝ) (x : Bundle L) : Prop :=
  InBudget p w x ∧ ∀ y, InBudget p w y → u y ≤ u x

/-- The demand correspondence as a set, for statements that use the paper's
set-valued notation `x_r(p,w)`. -/
def preferenceDemandSet (r : PreferenceFunction L)
    (p : Bundle L) (w : ℝ) : Set (Bundle L) :=
  {x | PreferenceDemand r p w x}

/-- The ordinary utility-demand correspondence as a set. -/
def utilityDemandSet (u : Utility L)
    (p : Bundle L) (w : ℝ) : Set (Bundle L) :=
  {x | UtilityDemand u p w x}

@[simp]
theorem mem_preferenceDemandSet_iff
    (r : PreferenceFunction L) (p : Bundle L) (w : ℝ) (x : Bundle L) :
    x ∈ preferenceDemandSet r p w ↔ PreferenceDemand r p w x :=
  Iff.rfl

@[simp]
theorem mem_utilityDemandSet_iff
    (u : Utility L) (p : Bundle L) (w : ℝ) (x : Bundle L) :
    x ∈ utilityDemandSet u p w ↔ UtilityDemand u p w x :=
  Iff.rfl

theorem dot_sub_left (p q x : Bundle L) :
    dot (p - q) x = dot p x - dot q x := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem positive_price_sum
    (p : Bundle L) (hp : PositivePrice p) (hL : 0 < L) :
    0 < ∑ i : Fin L, p i := by
  apply Finset.sum_pos'
  · intro i _hi
    exact (hp i).le
  · let i₀ : Fin L := ⟨0, hL⟩
    exact ⟨i₀, Finset.mem_univ i₀, hp i₀⟩

private theorem dot_add_constant (p x : Bundle L) (ε : ℝ) :
    dot p (fun i ↦ x i + ε) = dot p x + ε * ∑ i, p i := by
  unfold dot
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    ∑ i : Fin L, p i * ε = ∑ i : Fin L, ε * p i := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = ε * ∑ i : Fin L, p i := by rw [Finset.mul_sum]

/-- If `y` costs strictly less than `x` at positive prices, `y` can be
strictly improved in every coordinate while remaining no more expensive
than `x`.  This is the reusable budget-interior step behind Lemma 5. -/
theorem exists_strictDominating_below_expenditure
    (p x y : Bundle L)
    (hp : PositivePrice p) (hL : 0 < L)
    (hy : Nonnegative y) (hcheap : dot p y < dot p x) :
    ∃ z : Bundle L,
      Nonnegative z ∧ StrictDominates z y ∧ dot p z ≤ dot p x := by
  let priceSum : ℝ := ∑ i : Fin L, p i
  have hsum : 0 < priceSum := by
    simpa [priceSum] using positive_price_sum p hp hL
  let ε : ℝ := (dot p x - dot p y) / (2 * priceSum)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  let z : Bundle L := fun i ↦ y i + ε
  have hznonneg : Nonnegative z := by
    intro i
    dsimp [z]
    exact add_nonneg (hy i) hε.le
  have hzdom : StrictDominates z y := by
    refine ⟨fun i ↦ by dsimp [z]; linarith, ?_⟩
    intro heq
    let i₀ : Fin L := ⟨0, hL⟩
    have hi := congr_fun heq i₀
    dsimp [z] at hi
    linarith
  have hεsum : ε * priceSum = (dot p x - dot p y) / 2 := by
    dsimp [ε]
    field_simp
  have hcost : dot p z = dot p y + ε * priceSum := by
    simpa [z, priceSum] using dot_add_constant p y ε
  refine ⟨z, hznonneg, hzdom, ?_⟩
  rw [hcost, hεsum]
  linarith

/-- A strictly affordable nonnegative bundle can be improved in every
coordinate while remaining in the same budget. -/
theorem exists_strictDominating_inBudget
    (p : Bundle L) (w : ℝ) (y : Bundle L)
    (hp : PositivePrice p) (hL : 0 < L)
    (hy : Nonnegative y) (hcheap : dot p y < w) :
    ∃ z : Bundle L,
      Nonnegative z ∧ StrictDominates z y ∧ dot p z ≤ w := by
  let priceSum : ℝ := ∑ i : Fin L, p i
  have hsum : 0 < priceSum := by
    simpa [priceSum] using positive_price_sum p hp hL
  let ε : ℝ := (w - dot p y) / (2 * priceSum)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  let z : Bundle L := fun i ↦ y i + ε
  have hznonneg : Nonnegative z := by
    intro i
    dsimp [z]
    exact add_nonneg (hy i) hε.le
  have hzdom : StrictDominates z y := by
    refine ⟨fun i ↦ by dsimp [z]; linarith, ?_⟩
    intro heq
    let i₀ : Fin L := ⟨0, hL⟩
    have hi := congr_fun heq i₀
    dsimp [z] at hi
    linarith
  have hεsum : ε * priceSum = (w - dot p y) / 2 := by
    dsimp [ε]
    field_simp
  have hcost : dot p z = dot p y + ε * priceSum := by
    simpa [z, priceSum] using dot_add_constant p y ε
  refine ⟨z, hznonneg, hzdom, ?_⟩
  rw [hcost, hεsum]
  linarith

/-- The paper's budget-interior claim in relational form.  A demanded bundle
is strictly preferred to every strictly affordable bundle. -/
theorem preferenceDemand_strictlyPreferred_of_strictlyAffordable
    (r : PreferenceFunction L)
    (p : Bundle L) (w : ℝ) (x y : Bundle L)
    (hp : PositivePrice p) (hL : 0 < L)
    (hasym : Asymmetric r) (hinc : StrictlyIncreasingFirst r)
    (hx : PreferenceDemand r p w x)
    (hy : Nonnegative y) (hcheap : dot p y < w) :
    StrictlyPreferred r x y := by
  obtain ⟨z, hznonneg, hzdom, hzcost⟩ :=
    exists_strictDominating_inBudget p w y hp hL hy hcheap
  have hxz : 0 ≤ r x z := hx.2 z ⟨hznonneg, hzcost⟩
  have hzx : r z x ≤ 0 := hasym.1 x z hxz
  have hyx : r y x < 0 := (hinc x hzdom).trans_le hzx
  exact ⟨hx.2 y ⟨hy, hcheap.le⟩, hyx⟩

/-- Numerical budget-interior claim for a preference function that is
strictly decreasing in its second bundle (in particular, a finite CMU with
strictly increasing components). -/
theorem preferenceDemand_pos_of_strictlyAffordable
    (r : PreferenceFunction L)
    (p : Bundle L) (w : ℝ) (x y : Bundle L)
    (hp : PositivePrice p) (hL : 0 < L)
    (hdec : ∀ ⦃a b c : Bundle L⦄,
      StrictDominates c b → r a c < r a b)
    (hx : PreferenceDemand r p w x)
    (hy : Nonnegative y) (hcheap : dot p y < w) :
    0 < r x y := by
  obtain ⟨z, hznonneg, hzdom, hzcost⟩ :=
    exists_strictDominating_inBudget p w y hp hL hy hcheap
  exact (hx.2 z ⟨hznonneg, hzcost⟩).trans_lt (hdec hzdom)

/-- Utility maximization is contained in demand for the corresponding
singleton (justifiable) preference function. -/
theorem utilityDemand_implies_preferenceDemand_difference
    (u : Utility L) (p : Bundle L) (w : ℝ) (x : Bundle L)
    (hx : UtilityDemand u p w x) :
    PreferenceDemand (fun a b ↦ u a - u b) p w x := by
  refine ⟨hx.1, ?_⟩
  intro y hy
  linarith [hx.2 y hy]

end WGARP
