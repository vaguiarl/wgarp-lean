import WGARP.Pairwise
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Lattice

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Pairwise Afriat utilities

This file gives the constructive two-observation Afriat step used in
Theorem 1.  Given a pairwise Afriat certificate, the utility for the pair
`s,t` is the minimum of the two supporting affine functions

`R s t / 2 + λ s t * (p s · z - p s · x s)`

and its transpose.  The construction is symmetric in `s,t`, works without
an `s ≠ t` assumption, and therefore covers diagonal entries and a
one-observation dataset uniformly.
-/

open scoped BigOperators

namespace WGARP

variable {L : ℕ} {T : Type*} {D : Dataset L T}

/-- Wealth at an observed price-choice pair. -/
def wealth (D : Dataset L T) (s : T) : ℝ :=
  expenditure D s (D.choice s)

/-- A positive finite-dimensional price vector defines a strictly
increasing expenditure functional for the paper's weak-coordinate-plus-
inequality notion of strict dominance. -/
theorem dot_strictlyIncreasing_of_pos
    {p x z : Bundle L} (hp : ∀ i, 0 < p i)
    (hxz : StrictDominates x z) :
    dot p z < dot p x := by
  rcases hxz with ⟨hle, hne⟩
  have hexists : ∃ i, z i < x i := by
    by_contra hnone
    apply hne
    funext i
    have hxle : x i ≤ z i := by
      apply le_of_not_gt
      intro hstrict
      exact hnone ⟨i, hstrict⟩
    exact le_antisymm hxle (hle i)
  unfold dot
  apply Finset.sum_lt_sum
  · intro i _hi
    exact mul_le_mul_of_nonneg_left (hle i) (hp i).le
  · obtain ⟨i, hi⟩ := hexists
    exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hp i)⟩

/-- Observed expenditure is strictly increasing under strict dominance. -/
theorem expenditure_strictlyIncreasing
    (D : Dataset L T) (s : T) :
    StrictlyIncreasing (expenditure D s) := by
  intro x z hxz
  exact dot_strictlyIncreasing_of_pos (D.price_pos s) hxz

/-- The affine support associated with the ordered pair `s,t`. -/
noncomputable def pairAffine (certificate : PairwiseAfriat D)
    (s t : T) (z : Bundle L) : ℝ :=
  certificate.R s t / 2 +
    certificate.multiplier s t * (expenditure D s z - wealth D s)

/-- The symmetric two-observation Afriat utility. -/
noncomputable def pairUtility (certificate : PairwiseAfriat D)
    (s t : T) (z : Bundle L) : ℝ :=
  min (pairAffine certificate s t z) (pairAffine certificate t s z)

@[simp]
theorem pairAffine_choice_first
    (certificate : PairwiseAfriat D) (s t : T) :
    pairAffine certificate s t (D.choice s) = certificate.R s t / 2 := by
  simp [pairAffine, wealth]

/-- At `xˢ`, the transposed plane lies weakly above the `s,t` plane.
This is exactly one of the two pairwise Afriat inequalities. -/
theorem half_R_le_pairAffine_swap_choice
    (certificate : PairwiseAfriat D) (s t : T) :
    certificate.R s t / 2 ≤ pairAffine certificate t s (D.choice s) := by
  have hineq := certificate.inequality t s
  rw [expenditureGap_eq] at hineq
  rw [certificate.R_skew t s] at hineq
  unfold pairAffine wealth
  rw [certificate.R_skew t s]
  nlinarith

/-- The pair utility touches its `s` endpoint at `R s t / 2`. -/
@[simp]
theorem pairUtility_choice_first
    (certificate : PairwiseAfriat D) (s t : T) :
    pairUtility certificate s t (D.choice s) = certificate.R s t / 2 := by
  rw [pairUtility, pairAffine_choice_first]
  exact min_eq_left (half_R_le_pairAffine_swap_choice certificate s t)

/-- The pair utility touches its `t` endpoint at the opposite value. -/
@[simp]
theorem pairUtility_choice_second
    (certificate : PairwiseAfriat D) (s t : T) :
    pairUtility certificate s t (D.choice t) = certificate.R t s / 2 := by
  rw [pairUtility, pairAffine_choice_first]
  exact min_eq_right (half_R_le_pairAffine_swap_choice certificate t s)

/-- On the diagonal the construction touches the observed choice at zero.
This explicitly records the `T = 1` case omitted by the paper's original
`T ≥ 2` reduction. -/
@[simp]
theorem pairUtility_choice_self
    (certificate : PairwiseAfriat D) (s : T) :
    pairUtility certificate s s (D.choice s) = 0 := by
  rw [pairUtility_choice_first]
  simp

/-- Swapping the observation indices leaves the pair utility unchanged. -/
theorem pairUtility_swap
    (certificate : PairwiseAfriat D) (s t : T) (z : Bundle L) :
    pairUtility certificate s t z = pairUtility certificate t s z := by
  simp [pairUtility, min_comm]

/-- Function-valued form of symmetry, convenient when building the matrix
of pair utilities in Theorem 1(iii). -/
theorem pairUtility_symm
    (certificate : PairwiseAfriat D) (s t : T) :
    pairUtility certificate s t = pairUtility certificate t s := by
  funext z
  exact pairUtility_swap certificate s t z

/-- The pair utility rationalizes observation `s`. -/
theorem pairUtility_rationalizes_first
    (certificate : PairwiseAfriat D) (s t : T)
    {y : Bundle L} (hy : Affordable D s y) :
    pairUtility certificate s t y ≤
      pairUtility certificate s t (D.choice s) := by
  have hdiff : expenditure D s y - wealth D s ≤ 0 := by
    exact sub_nonpos.mpr hy.2
  have hscaled :
      certificate.multiplier s t * (expenditure D s y - wealth D s) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (certificate.multiplier_pos s t).le hdiff
  calc
    pairUtility certificate s t y ≤ pairAffine certificate s t y := min_le_left _ _
    _ ≤ certificate.R s t / 2 := by
      unfold pairAffine
      linarith
    _ = pairUtility certificate s t (D.choice s) :=
      (pairUtility_choice_first certificate s t).symm

/-- The same symmetric pair utility rationalizes observation `t`. -/
theorem pairUtility_rationalizes_second
    (certificate : PairwiseAfriat D) (s t : T)
    {y : Bundle L} (hy : Affordable D t y) :
    pairUtility certificate s t y ≤
      pairUtility certificate s t (D.choice t) := by
  have hdiff : expenditure D t y - wealth D t ≤ 0 := by
    exact sub_nonpos.mpr hy.2
  have hscaled :
      certificate.multiplier t s * (expenditure D t y - wealth D t) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (certificate.multiplier_pos t s).le hdiff
  calc
    pairUtility certificate s t y ≤ pairAffine certificate t s y := min_le_right _ _
    _ ≤ certificate.R t s / 2 := by
      unfold pairAffine
      linarith
    _ = pairUtility certificate s t (D.choice t) :=
      (pairUtility_choice_second certificate s t).symm

/-- Both endpoint rationalization properties, packaged together. -/
theorem pairUtility_rationalizes_pair
    (certificate : PairwiseAfriat D) (s t : T) :
    (∀ ⦃y⦄, Affordable D s y →
      pairUtility certificate s t y ≤
        pairUtility certificate s t (D.choice s)) ∧
    (∀ ⦃y⦄, Affordable D t y →
      pairUtility certificate s t y ≤
        pairUtility certificate s t (D.choice t)) := by
  constructor
  · intro y hy
    exact pairUtility_rationalizes_first certificate s t hy
  · intro y hy
    exact pairUtility_rationalizes_second certificate s t hy

/-- The finite-dimensional dot product is continuous in its second
argument. -/
theorem continuous_dot (p : Bundle L) : Continuous (dot p) := by
  unfold dot
  apply continuous_finsetSum Finset.univ
  intro i _hi
  exact continuous_const.mul (continuous_apply i)

/-- Each supporting affine function is continuous. -/
theorem pairAffine_continuous
    (certificate : PairwiseAfriat D) (s t : T) :
    Continuous (pairAffine certificate s t) := by
  unfold pairAffine wealth expenditure
  exact continuous_const.add
    (continuous_const.mul ((continuous_dot (D.price s)).sub continuous_const))

/-- A pair utility is continuous as the pointwise minimum of its two
continuous supporting planes. -/
theorem pairUtility_continuous
    (certificate : PairwiseAfriat D) (s t : T) :
    Continuous (pairUtility certificate s t) := by
  exact (pairAffine_continuous certificate s t).min
    (pairAffine_continuous certificate t s)

/-- Linear functional represented by the package's finite dot product. -/
def dotLinear (p : Bundle L) : Bundle L →ₗ[ℝ] ℝ where
  toFun x := dot p x
  map_add' x y := by
    simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    calc
      dot p (a • x) = ∑ i : Fin L, a * (p i * x i) := by
        unfold dot
        apply Finset.sum_congr rfl
        intro i _hi
        simp
        ring
      _ = a * dot p x := by
        simp [dot, Finset.mul_sum]

@[simp]
theorem dotLinear_apply (p x : Bundle L) : dotLinear p x = dot p x := rfl

/-- Dot products preserve affine combinations. -/
theorem dot_add_smul (p x y : Bundle L) (a b : ℝ) :
    dot p (a • x + b • y) = a * dot p x + b * dot p y := by
  change dotLinear p (a • x + b • y) =
    a * dotLinear p x + b * dotLinear p y
  rw [map_add, map_smul, map_smul]
  simp only [smul_eq_mul]

/-- Exact affine-combination identity for a pair support plane. -/
theorem pairAffine_add_smul
    (certificate : PairwiseAfriat D) (s t : T)
    (x y : Bundle L) (a b : ℝ) (hab : a + b = 1) :
    pairAffine certificate s t (a • x + b • y) =
      a * pairAffine certificate s t x +
        b * pairAffine certificate s t y := by
  unfold pairAffine expenditure
  rw [dot_add_smul]
  calc
    certificate.R s t / 2 +
          certificate.multiplier s t *
            (a * dot (D.price s) x + b * dot (D.price s) y - wealth D s) =
        (a + b) * (certificate.R s t / 2) +
          certificate.multiplier s t *
            (a * dot (D.price s) x + b * dot (D.price s) y -
              (a + b) * wealth D s) := by
      rw [hab]
      ring
    _ = a *
          (certificate.R s t / 2 +
            certificate.multiplier s t * (dot (D.price s) x - wealth D s)) +
        b *
          (certificate.R s t / 2 +
            certificate.multiplier s t * (dot (D.price s) y - wealth D s)) := by
      ring

/-- Each supporting plane is affine and hence concave. -/
theorem pairAffine_concaveOn
    (certificate : PairwiseAfriat D) (s t : T) :
    ConcaveOn ℝ Set.univ (pairAffine certificate s t) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b _ha _hb hab
  rw [pairAffine_add_smul certificate s t x y a b hab]
  simp only [smul_eq_mul]
  exact le_rfl

/-- A pair utility is concave as the pointwise minimum of two concave
affine functions. -/
theorem pairUtility_concaveOn
    (certificate : PairwiseAfriat D) (s t : T) :
    ConcaveOn ℝ Set.univ (pairUtility certificate s t) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b ha hb hab
  unfold pairUtility
  apply le_min
  · calc
      a • min (pairAffine certificate s t x) (pairAffine certificate t s x) +
            b • min (pairAffine certificate s t y) (pairAffine certificate t s y) ≤
          a • pairAffine certificate s t x +
            b • pairAffine certificate s t y := by
        exact add_le_add
          (smul_le_smul_of_nonneg_left (min_le_left _ _) ha)
          (smul_le_smul_of_nonneg_left (min_le_left _ _) hb)
      _ ≤ pairAffine certificate s t (a • x + b • y) :=
        (pairAffine_concaveOn certificate s t).2
          (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  · calc
      a • min (pairAffine certificate s t x) (pairAffine certificate t s x) +
            b • min (pairAffine certificate s t y) (pairAffine certificate t s y) ≤
          a • pairAffine certificate t s x +
            b • pairAffine certificate t s y := by
        exact add_le_add
          (smul_le_smul_of_nonneg_left (min_le_right _ _) ha)
          (smul_le_smul_of_nonneg_left (min_le_right _ _) hb)
      _ ≤ pairAffine certificate t s (a • x + b • y) :=
        (pairAffine_concaveOn certificate t s).2
          (Set.mem_univ x) (Set.mem_univ y) ha hb hab

/-- Every supporting plane is strictly increasing because its multiplier
and the corresponding observed price coordinates are positive. -/
theorem pairAffine_strictlyIncreasing
    (certificate : PairwiseAfriat D) (s t : T) :
    StrictlyIncreasing (pairAffine certificate s t) := by
  intro x z hxz
  have hdot : expenditure D s z < expenditure D s x :=
    expenditure_strictlyIncreasing D s hxz
  have hscaled :
      certificate.multiplier s t *
          (expenditure D s z - wealth D s) <
        certificate.multiplier s t *
          (expenditure D s x - wealth D s) := by
    apply mul_lt_mul_of_pos_left _ (certificate.multiplier_pos s t)
    linarith
  unfold pairAffine
  linarith

/-- The minimum of the two strictly increasing support planes remains
strictly increasing. -/
theorem pairUtility_strictlyIncreasing
    (certificate : PairwiseAfriat D) (s t : T) :
    StrictlyIncreasing (pairUtility certificate s t) := by
  intro x z hxz
  have hst := pairAffine_strictlyIncreasing certificate s t hxz
  have hts := pairAffine_strictlyIncreasing certificate t s hxz
  unfold pairUtility
  rcases le_total (pairAffine certificate s t x)
      (pairAffine certificate t s x) with hright | hright
  · rw [min_eq_left hright]
    exact (min_le_left _ _).trans_lt hst
  · rw [min_eq_right hright]
    exact (min_le_right _ _).trans_lt hts

end WGARP
