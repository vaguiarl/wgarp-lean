import WGARP.Data
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Necessity of WGARP

This file checks the economic argument from an asymmetric, strictly
increasing dominant-choice rationalization to WGARP.  The proof makes the
paper's interior-budget perturbation explicit.
-/

namespace WGARP

open scoped BigOperators

variable {L : ℕ} {T : Type*}

theorem weakSignAsymmetric_of_skewSymmetric
    {r : PreferenceFunction L} (hskew : SkewSymmetric r) :
    WeakSignAsymmetric r := by
  intro x y hxy
  rw [hskew y x]
  linarith

theorem signAsymmetric_of_skewSymmetric
    {r : PreferenceFunction L} (hskew : SkewSymmetric r) :
    SignAsymmetric r := by
  intro x y hxy
  rw [hskew y x]
  linarith

theorem asymmetric_of_skewSymmetric
    {r : PreferenceFunction L} (hskew : SkewSymmetric r) :
    Asymmetric r :=
  ⟨weakSignAsymmetric_of_skewSymmetric hskew,
    signAsymmetric_of_skewSymmetric hskew⟩

private theorem positive_price_sum (D : Dataset L T) (s : T) :
    0 < ∑ k : Fin L, D.price s k := by
  have hL : 0 < L := lt_of_lt_of_le (by decide : 0 < 2) D.goods_two_le
  apply Finset.sum_pos'
  · intro k _hk
    exact (D.price_pos s k).le
  · let k₀ : Fin L := ⟨0, hL⟩
    exact ⟨k₀, Finset.mem_univ k₀, D.price_pos s k₀⟩

private theorem dot_add_constant (p x : Bundle L) (ε : ℝ) :
    dot p (fun k => x k + ε) = dot p x + ε * ∑ k, p k := by
  unfold dot
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    ∑ k : Fin L, p k * ε = ∑ k : Fin L, ε * p k := by
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = ε * ∑ k : Fin L, p k := by rw [Finset.mul_sum]

/-- A strictly cheaper nonnegative bundle can be improved in every
coordinate while remaining within the budget. -/
theorem exists_strictDominating_affordable
    (D : Dataset L T) (s t : T)
    (hcheap : 0 < expenditureGap D s t) :
    ∃ z : Bundle L,
      StrictDominates z (D.choice t) ∧ Affordable D s z := by
  let priceSum : ℝ := ∑ k : Fin L, D.price s k
  have hsum : 0 < priceSum := by
    simpa [priceSum] using positive_price_sum D s
  let ε : ℝ := expenditureGap D s t / (2 * priceSum)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  let z : Bundle L := fun k => D.choice t k + ε
  have hdom : StrictDominates z (D.choice t) := by
    refine ⟨fun k => by dsimp [z]; linarith, ?_⟩
    intro heq
    have hk := congr_fun heq ⟨0, lt_of_lt_of_le (by decide : 0 < 2) D.goods_two_le⟩
    dsimp [z] at hk
    linarith
  have hnonneg : Nonnegative z := by
    intro k
    dsimp [z]
    exact add_nonneg (D.choice_nonneg t k) hε.le
  have hεsum : ε * priceSum = expenditureGap D s t / 2 := by
    dsimp [ε]
    field_simp
  have hdot :
      expenditure D s z = expenditure D s (D.choice t) + ε * priceSum := by
    simpa [expenditure, z, priceSum] using
      dot_add_constant (D.price s) (D.choice t) ε
  refine ⟨z, hdom, hnonneg, ?_⟩
  rw [hdot, hεsum, expenditureGap_eq]
  rw [expenditureGap_eq] at hcheap
  linarith

/-- Lemma 2 of the paper: dominant-choice rationalization by an
asymmetric, strictly increasing preference function forces WGARP. -/
theorem wgarp_of_asymmetric_strictlyIncreasing_rationalization
    (D : Dataset L T)
    (r : PreferenceFunction L)
    (hasym : Asymmetric r)
    (hinc : StrictlyIncreasingFirst r)
    (hrat : PreferenceRationalizes D r) :
    WGARP D := by
  intro s t hts
  by_contra hnot
  have hst : 0 < expenditureGap D s t := lt_of_not_ge hnot
  have hxt_affordable : Affordable D t (D.choice s) := by
    refine ⟨D.choice_nonneg s, ?_⟩
    rw [expenditureGap_eq] at hts
    linarith
  have hweak : 0 ≤ r (D.choice t) (D.choice s) :=
    hrat t (D.choice s) hxt_affordable
  obtain ⟨z, hzdom, hzbudget⟩ :=
    exists_strictDominating_affordable D s t hst
  have hsweak : 0 ≤ r (D.choice s) z := hrat s z hzbudget
  have hzpos : 0 < r z (D.choice s) :=
    lt_of_le_of_lt hweak (hinc (D.choice s) hzdom)
  have hsneg : r (D.choice s) z < 0 := hasym.2 z (D.choice s) hzpos
  exact (not_lt_of_ge hsweak) hsneg

end WGARP
