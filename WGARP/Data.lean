import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Real.Lemmas

set_option linter.dupNamespace false

/-!
# Finite consumer datasets

This file formalizes the primitive objects used in Theorem 1 of
Aguiar--Hjertstrand--Serrano--Evren.  Commodity bundles are vectors in
`ℝ^L`.  The paper writes `x > z` for coordinatewise weak dominance with at
least one strict coordinate; `StrictDominates` records that convention
explicitly, avoiding Lean's (stronger) product strict order.
-/

open scoped BigOperators

set_option linter.dupNamespace false

namespace WGARP

/-- A bundle of `L` commodities. -/
abbrev Bundle (L : ℕ) := Fin L → ℝ

/-- A utility function on commodity bundles. -/
abbrev Utility (L : ℕ) := Bundle L → ℝ

/-- A real-valued preference function on ordered pairs of bundles. -/
abbrev PreferenceFunction (L : ℕ) := Bundle L → Bundle L → ℝ

/-- Euclidean dot product, written by juxtaposition in the paper. -/
def dot {L : ℕ} (p x : Bundle L) : ℝ := ∑ i, p i * x i

@[simp]
theorem dot_zero_right {L : ℕ} (p : Bundle L) : dot p 0 = 0 := by
  simp [dot]

@[simp]
theorem dot_zero_left {L : ℕ} (x : Bundle L) : dot 0 x = 0 := by
  simp [dot]

theorem dot_sub {L : ℕ} (p x y : Bundle L) : dot p (x - y) = dot p x - dot p y := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Coordinatewise nonnegativity of a commodity bundle. -/
def Nonnegative {L : ℕ} (x : Bundle L) : Prop := ∀ i, 0 ≤ x i

/--
The paper's strict commodity order: `x` weakly dominates `z` in every
coordinate and the two bundles are unequal.  In finite dimension this is
equivalent to weak dominance with a strict inequality in some coordinate.
-/
def StrictDominates {L : ℕ} (x z : Bundle L) : Prop :=
  (∀ i, z i ≤ x i) ∧ x ≠ z

/-- A utility is strictly increasing for the paper's commodity order. -/
def StrictlyIncreasing {L : ℕ} (u : Utility L) : Prop :=
  ∀ ⦃x z : Bundle L⦄, StrictDominates x z → u z < u x

/-- A preference function is strictly increasing in its first bundle. -/
def StrictlyIncreasingFirst {L : ℕ} (r : PreferenceFunction L) : Prop :=
  ∀ ⦃x z : Bundle L⦄ (y : Bundle L), StrictDominates x z → r z y < r x y

/-- The weak-sign half of asymmetry in Definition 4 of the paper. -/
def WeakSignAsymmetric {L : ℕ} (r : PreferenceFunction L) : Prop :=
  ∀ x y, 0 ≤ r x y → r y x ≤ 0

/-- The strict-sign half of asymmetry in Definition 4 of the paper. -/
def SignAsymmetric {L : ℕ} (r : PreferenceFunction L) : Prop :=
  ∀ x y, 0 < r x y → r y x < 0

/-- Paper-exact asymmetry: both its weak- and strict-sign implications. -/
def Asymmetric {L : ℕ} (r : PreferenceFunction L) : Prop :=
  WeakSignAsymmetric r ∧ SignAsymmetric r

/-- Skew symmetry of a preference function. -/
def SkewSymmetric {L : ℕ} (r : PreferenceFunction L) : Prop :=
  ∀ x y, r x y = -r y x

/-- Joint continuity in both bundle arguments. -/
def ContinuousPreference {L : ℕ} (r : PreferenceFunction L) : Prop :=
  Continuous (Function.uncurry r)

/--
A finite consumer dataset, indexed by `T`.  The two primitive restrictions
from the paper are stored with the data: at least two goods, strictly positive
prices, and nonzero nonnegative observed bundles.
-/
structure Dataset (L : ℕ) (T : Type*) where
  price : T → Bundle L
  choice : T → Bundle L
  goods_two_le : 2 ≤ L
  price_pos : ∀ t i, 0 < price t i
  choice_nonneg : ∀ t i, 0 ≤ choice t i
  choice_ne_zero : ∀ t, choice t ≠ 0

variable {L : ℕ} {T : Type*}

/-- Expenditure at prices from observation `s`. -/
def expenditure (D : Dataset L T) (s : T) (x : Bundle L) : ℝ :=
  dot (D.price s) x

/--
The signed expenditure gap `pˢ (xˢ - xᵗ)`.  A nonnegative gap says that
`xˢ` is directly revealed preferred to `xᵗ`; a positive gap says so strictly.
-/
def expenditureGap (D : Dataset L T) (s t : T) : ℝ :=
  dot (D.price s) (D.choice s - D.choice t)

theorem expenditureGap_eq (D : Dataset L T) (s t : T) :
    expenditureGap D s t = expenditure D s (D.choice s) - expenditure D s (D.choice t) := by
  exact dot_sub _ _ _

@[simp]
theorem expenditureGap_self (D : Dataset L T) (s : T) : expenditureGap D s s = 0 := by
  simp [expenditureGap]

/-- A nonnegative candidate bundle lying in observation `t`'s budget set. -/
def Affordable (D : Dataset L T) (t : T) (y : Bundle L) : Prop :=
  Nonnegative y ∧ expenditure D t y ≤ expenditure D t (D.choice t)

theorem affordable_choice (D : Dataset L T) (t : T) : Affordable D t (D.choice t) := by
  exact ⟨D.choice_nonneg t, le_rfl⟩

/-- Preference-function rationalization (Definition 6 in the paper). -/
def PreferenceRationalizes (D : Dataset L T) (r : PreferenceFunction L) : Prop :=
  ∀ t y, Affordable D t y → 0 ≤ r (D.choice t) y

/-- Ordinary utility rationalization (Definition 3 in the paper). -/
def UtilityRationalizes (D : Dataset L T) (u : Utility L) : Prop :=
  ∀ t y, Affordable D t y → u y ≤ u (D.choice t)

/--
The weak generalized axiom of revealed preference.  This is the paper's exact
two-observation condition: if `xᵗ` is weakly directly revealed preferred to
`xˢ`, then `xˢ` is not strictly directly revealed preferred to `xᵗ`.
-/
def SatisfiesWGARP (D : Dataset L T) : Prop :=
  ∀ s t, 0 ≤ expenditureGap D t s → expenditureGap D s t ≤ 0

/-- Short name used in theorem statements. -/
abbrev WGARP (D : Dataset L T) : Prop := SatisfiesWGARP D

theorem wgarp_no_binary_cycle (D : Dataset L T) :
    WGARP D ↔ ∀ s t, ¬(0 ≤ expenditureGap D t s ∧ 0 < expenditureGap D s t) := by
  constructor
  · intro h s t hcycle
    exact (not_lt_of_ge (h s t hcycle.1)) hcycle.2
  · intro h s t hweak
    exact le_of_not_gt fun hstrict => h s t ⟨hweak, hstrict⟩

end WGARP
