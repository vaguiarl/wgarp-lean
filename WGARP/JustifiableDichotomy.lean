import WGARP.Justifiable
import WGARP.CompactCMU
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.Sequences
import Mathlib.Tactic

set_option autoImplicit false

/-!
# The justifiable-demand dichotomy

This file formalizes the second branch of Lemma 6.  If two component
utilities have different Marshallian demand at a positive price--wealth
pair, a separating functional and a vanishing price perturbation produce
two demanded bundles, each strictly affordable at the other market.

The proof is deliberately phrased for the relational definition
`JustifiablyPreferred`.  Compactness of the family of utility functions is
needed to replace an attained maximum by that relation, but is not needed
for the demand-theoretic dichotomy itself.
-/

namespace WGARP

open Filter Set
open scoped BigOperators Topology

variable {L : ℕ} {I T : Type*}

private theorem inBudgetSet_closed' (p : Bundle L) (w : ℝ) :
    IsClosed {x : Bundle L | InBudget p w x} := by
  have hnonnegative : IsClosed {x : Bundle L | Nonnegative x} := by
    have heq :
        {x : Bundle L | Nonnegative x} =
          ⋂ i : Fin L, {x : Bundle L | x i ∈ Set.Ici 0} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Ici, Nonnegative]
    rw [heq]
    exact isClosed_iInter fun i ↦ isClosed_Ici.preimage (continuous_apply i)
  have hcost : IsClosed {x : Bundle L | dot p x ≤ w} :=
    isClosed_Iic.preimage (continuous_dot p)
  simpa only [InBudget, setOf_and] using hnonnegative.inter hcost

/-- The ordinary demand set is closed when utility is continuous. -/
theorem utilityDemandSet_closed
    (u : Utility L) (p : Bundle L) (w : ℝ) (hu : Continuous u) :
    IsClosed (utilityDemandSet u p w) := by
  have hoptimal :
      IsClosed (⋂ y : Bundle L,
        {x : Bundle L | InBudget p w y → u y ≤ u x}) := by
    apply isClosed_iInter
    intro y
    by_cases hy : InBudget p w y
    · simpa [hy] using isClosed_le continuous_const hu
    · simp [hy]
  have heq :
      utilityDemandSet u p w =
        {x : Bundle L | InBudget p w x} ∩
          ⋂ y : Bundle L, {x : Bundle L | InBudget p w y → u y ≤ u x} := by
    ext x
    simp [utilityDemandSet, UtilityDemand]
  rw [heq]
  exact (inBudgetSet_closed' p w).inter hoptimal

/-- The ordinary demand set is compact at a positive-price market. -/
theorem utilityDemandSet_compact
    (u : Utility L) (p : Bundle L) (w : ℝ)
    (hu : Continuous u) (hp : PositivePrice p) (hw : 0 ≤ w) :
    IsCompact (utilityDemandSet u p w) := by
  apply (inBudgetSet_compact p w hp hw).of_isClosed_subset
  · exact utilityDemandSet_closed u p w hu
  · intro x hx
    exact hx.1

private theorem inBudget_convex (p : Bundle L) (w : ℝ) :
    Convex ℝ {x : Bundle L | InBudget p w x} := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · rw [dot_add_smul]
    calc
      a * dot p x + b * dot p y ≤ a * w + b * w :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = w := by rw [← add_mul, hab, one_mul]

/-- Quasiconcavity on the nonnegative orthant makes every ordinary demand
set convex. -/
theorem utilityDemandSet_convex
    (u : Utility L) (p : Bundle L) (w : ℝ)
    (hu : QuasiconcaveOn ℝ {x : Bundle L | Nonnegative x} u) :
    Convex ℝ (utilityDemandSet u p w) := by
  intro x hx y hy a b ha hb hab
  have hbudget := inBudget_convex p w hx.1 hy.1 ha hb hab
  refine ⟨hbudget, ?_⟩
  intro z hz
  have hxlevel : x ∈ {v ∈ {v : Bundle L | Nonnegative v} | u z ≤ u v} :=
    ⟨hx.1.1, hx.2 z hz⟩
  have hylevel : y ∈ {v ∈ {v : Bundle L | Nonnegative v} | u z ≤ u v} :=
    ⟨hy.1.1, hy.2 z hz⟩
  exact (hu (u z) hxlevel hylevel ha hb hab).2

private theorem positive_price_sum'
    (p : Bundle L) (hp : PositivePrice p) (hL : 0 < L) :
    0 < ∑ i : Fin L, p i := by
  apply Finset.sum_pos'
  · intro i _hi
    exact (hp i).le
  · let i₀ : Fin L := ⟨0, hL⟩
    exact ⟨i₀, Finset.mem_univ i₀, hp i₀⟩

private theorem dot_add_constant'
    (p x : Bundle L) (ε : ℝ) :
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

/-- A demanded bundle exhausts a strictly positive budget when utility is
strictly increasing and there is at least one commodity. -/
theorem utilityDemand_expenditure_eq_wealth
    (u : Utility L) (p : Bundle L) (w : ℝ) (x : Bundle L)
    (hL : 0 < L) (hp : PositivePrice p) (hu : StrictlyIncreasing u)
    (hx : UtilityDemand u p w x) :
    dot p x = w := by
  apply le_antisymm hx.1.2
  by_contra hnot
  have hcheap : dot p x < w := lt_of_not_ge hnot
  let priceSum : ℝ := ∑ i : Fin L, p i
  have hsum : 0 < priceSum := by
    simpa [priceSum] using positive_price_sum' p hp hL
  let ε : ℝ := (w - dot p x) / (2 * priceSum)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  let z : Bundle L := fun i ↦ x i + ε
  have hznonnegative : Nonnegative z := by
    intro i
    dsimp [z]
    exact add_nonneg (hx.1.1 i) hε.le
  have hzdom : StrictDominates z x := by
    refine ⟨fun i ↦ by dsimp [z]; linarith, ?_⟩
    · intro heq
      let i₀ : Fin L := ⟨0, hL⟩
      have hi := congr_fun heq i₀
      dsimp [z] at hi
      linarith
  have hcost : dot p z = dot p x + ε * priceSum := by
    simpa [z, priceSum] using dot_add_constant' p x ε
  have hεsum : ε * priceSum = (w - dot p x) / 2 := by
    dsimp [ε]
    field_simp
  have hzbudget : InBudget p w z := by
    refine ⟨hznonnegative, ?_⟩
    rw [hcost, hεsum]
    linarith
  exact (not_lt_of_ge (hx.2 z hzbudget)) (hu hzdom)

private noncomputable def dualPriceVector
    (f : StrongDual ℝ (Bundle L)) : Bundle L :=
  fun i ↦ f (Pi.single i 1)

private theorem dual_eq_dot (f : StrongDual ℝ (Bundle L)) (x : Bundle L) :
    f x = dot (dualPriceVector f) x := by
  classical
  conv_lhs => rw [pi_eq_sum_univ' x]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dualPriceVector, dot]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

private theorem continuous_dot_pair :
    Continuous (fun px : Bundle L × Bundle L ↦ dot px.1 px.2) := by
  unfold dot
  fun_prop

private theorem dot_add_left' (p q x : Bundle L) :
    dot (p + q) x = dot p x + dot q x := by
  unfold dot
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem dot_smul_left' (a : ℝ) (p x : Bundle L) :
    dot (a • p) x = a * dot p x := by
  unfold dot
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Strict positivity is an open condition on a finite price vector. -/
theorem positivePrice_isOpen :
    IsOpen {p : Bundle L | PositivePrice p} := by
  have heq :
      {p : Bundle L | PositivePrice p} =
        ⋂ i : Fin L, (fun p : Bundle L ↦ p i) ⁻¹' Set.Ioi 0 := by
    ext p
    simp [PositivePrice]
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_Ioi.preimage (continuous_apply i)

/-- Marshallian utility demand is upper hemicontinuous at every positive
price and positive wealth.  This specialized finite-dimensional form of
Berge's maximum theorem is the stability input used below. -/
theorem utilityDemand_upperHemicontinuousAt
    (u : Utility L) (p : Bundle L) (w : ℝ)
    (hu : Continuous u) (hp : PositivePrice p) (hw : 0 < w) :
    UpperHemicontinuousAt
      (fun pw : Bundle L × ℝ ↦ utilityDemandSet u pw.1 pw.2) (p, w) := by
  let pHalf : Bundle L := fun i ↦ p i / 2
  let K : Set (Bundle L) := {x | InBudget pHalf (2 * w) x}
  have hpHalf : PositivePrice pHalf := by
    intro i
    dsimp [pHalf]
    exact div_pos (hp i) zero_lt_two
  have hKcompact : IsCompact K := by
    simpa [K] using
      inBudgetSet_compact pHalf (2 * w) hpHalf (mul_nonneg zero_le_two hw.le)
  have hlocalPrice :
      ∀ᶠ pw : Bundle L × ℝ in nhds (p, w), ∀ i, pHalf i < pw.1 i := by
    rw [Filter.eventually_all]
    intro i
    apply ContinuousAt.eventually_lt continuousAt_const
      (((continuous_apply i).comp continuous_fst).continuousAt)
    dsimp [pHalf]
    linarith [hp i]
  have hlocalWealth :
      ∀ᶠ pw : Bundle L × ℝ in nhds (p, w), pw.2 < 2 * w := by
    apply ContinuousAt.eventually_lt continuous_snd.continuousAt continuousAt_const
    linarith
  have hlocalCompact :
      ∀ᶠ pw : Bundle L × ℝ in nhds (p, w),
        utilityDemandSet u pw.1 pw.2 ⊆ K := by
    filter_upwards [hlocalPrice, hlocalWealth] with pw hpw hww x hx
    refine ⟨hx.1.1, ?_⟩
    calc
      dot pHalf x ≤ dot pw.1 x := by
        unfold dot
        apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul_of_nonneg_right (hpw i).le (hx.1.1 i)
      _ ≤ pw.2 := hx.1.2
      _ ≤ 2 * w := hww.le
  apply UpperHemicontinuousAt.of_sequences hKcompact.isSeqCompact hlocalCompact
  intro market hmarket x hx x₀ hx₀
  have hprice : Tendsto (fun n ↦ (market n).1) atTop (nhds p) :=
    (continuous_fst.tendsto (p, w)).comp hmarket
  have hwealth : Tendsto (fun n ↦ (market n).2) atTop (nhds w) :=
    (continuous_snd.tendsto (p, w)).comp hmarket
  have hxnonnegative : Nonnegative x₀ := by
    have hclosed : IsClosed {z : Bundle L | Nonnegative z} := by
      have heq :
          {z : Bundle L | Nonnegative z} =
            ⋂ i : Fin L, {z : Bundle L | z i ∈ Set.Ici 0} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Ici, Nonnegative]
      rw [heq]
      exact isClosed_iInter fun i ↦
        isClosed_Ici.preimage (continuous_apply i)
    exact hclosed.mem_of_tendsto hx₀
      (Eventually.of_forall fun n ↦ (hx n).1.1)
  have hcostTendsto :
      Tendsto (fun n ↦ dot (market n).1 (x n)) atTop (nhds (dot p x₀)) := by
    exact continuous_dot_pair.continuousAt.tendsto.comp (hprice.prodMk_nhds hx₀)
  have hcost : dot p x₀ ≤ w :=
    le_of_tendsto_of_tendsto' hcostTendsto hwealth fun n ↦ (hx n).1.2
  refine ⟨⟨hxnonnegative, hcost⟩, ?_⟩
  intro z hz
  let a : ℕ → ℝ := fun k ↦ 1 - 1 / ((k : ℝ) + 1)
  have ha_nonnegative (k : ℕ) : 0 ≤ a k := by
    dsimp [a]
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk : 1 ≤ (k : ℝ) + 1 := by linarith
    have hdiv : 1 / ((k : ℝ) + 1) ≤ 1 := by
      exact (div_le_one (by positivity)).2 hk
    linarith
  have ha_lt_one (k : ℕ) : a k < 1 := by
    dsimp [a]
    have : 0 < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hzscaled_nonnegative (k : ℕ) : Nonnegative (a k • z) := by
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (ha_nonnegative k) (hz.1 i)
  have hdot_smul (k : ℕ) : dot p (a k • z) = a k * dot p z := by
    unfold dot
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hscaledInterior (k : ℕ) : dot p (a k • z) < w := by
    have hdot_nonnegative : 0 ≤ dot p z := by
      unfold dot
      exact Finset.sum_nonneg fun i _hi ↦ mul_nonneg (hp i).le (hz.1 i)
    rw [hdot_smul]
    have haw : a k * dot p z ≤ a k * w :=
      mul_le_mul_of_nonneg_left hz.2 (ha_nonnegative k)
    nlinarith [mul_lt_mul_of_pos_right (ha_lt_one k) hw]
  have hscaledOptimal (k : ℕ) : u (a k • z) ≤ u x₀ := by
    have hinteriorMarket :
        ∀ᶠ pw : Bundle L × ℝ in nhds (p, w),
          dot pw.1 (a k • z) < pw.2 := by
      apply ContinuousAt.eventually_lt
        (continuous_dot_pair.comp
          (continuous_fst.prodMk continuous_const)).continuousAt
        continuous_snd.continuousAt
      exact hscaledInterior k
    have hinteriorSequence :
        ∀ᶠ n in atTop, InBudget (market n).1 (market n).2 (a k • z) := by
      filter_upwards [hmarket.eventually hinteriorMarket] with n hn
      exact ⟨hzscaled_nonnegative k, hn.le⟩
    have hopt : ∀ᶠ n in atTop, u (a k • z) ≤ u (x n) := by
      filter_upwards [hinteriorSequence] with n hn
      exact (hx n).2 _ hn
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      (hu.continuousAt.tendsto.comp hx₀) hopt
  have haTendsto : Tendsto a atTop (nhds 1) := by
    dsimp [a]
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub
      tendsto_one_div_add_atTop_nhds_zero_nat)
  have hzscaledTendsto : Tendsto (fun k ↦ a k • z) atTop (nhds z) := by
    simpa using (haTendsto.smul_const z)
  exact le_of_tendsto
    (hu.continuousAt.tendsto.comp hzscaledTendsto)
    (Eventually.of_forall hscaledOptimal)

/-- Two component utilities agree on every economically relevant market. -/
def ComponentDemandsAgreeOnMarkets (u : I → Utility L) : Prop :=
  ∀ i j p w, PositivePrice p → 0 < w →
    ∀ x, UtilityDemand (u i) p w x ↔ UtilityDemand (u j) p w x

/-- The demand-side second alternative in Lemma 6. -/
def CrossStrictAffordableJustifiableDemands (u : I → Utility L) : Prop :=
  ∃ p₁ p₂ : Bundle L, ∃ w₁ w₂ : ℝ, ∃ x₁ x₂ : Bundle L,
    PositivePrice p₁ ∧ PositivePrice p₂ ∧ 0 < w₁ ∧ 0 < w₂ ∧
    JustifiableDemand u p₁ w₁ x₁ ∧
    JustifiableDemand u p₂ w₂ x₂ ∧
    dot p₁ x₂ < w₁ ∧ dot p₂ x₁ < w₂

/-! ## Separation and price perturbation -/

/-- The analytic core of the second branch of Lemma 6.  An oriented
difference between two component demand sets produces the two markets in
the lemma. -/
theorem crossStrictAffordableJustifiableDemands_of_demandDifference
    [Nonempty I]
    (u : I → Utility L) (i₁ i₂ : I)
    (p : Bundle L) (w : ℝ) (y₁ : Bundle L)
    (hL : 0 < L)
    (hcontinuous : ∀ i, Continuous (u i))
    (hquasiconcave :
      ∀ i, QuasiconcaveOn ℝ {x : Bundle L | Nonnegative x} (u i))
    (hincreasing : ∀ i, StrictlyIncreasing (u i))
    (hp : PositivePrice p) (hw : 0 < w)
    (hy₁ : UtilityDemand (u i₁) p w y₁)
    (hy₁not : ¬ UtilityDemand (u i₂) p w y₁) :
    CrossStrictAffordableJustifiableDemands u := by
  let K₂ : Set (Bundle L) := utilityDemandSet (u i₂) p w
  have hK₂closed : IsClosed K₂ := by
    simpa [K₂] using utilityDemandSet_closed (u i₂) p w (hcontinuous i₂)
  have hK₂convex : Convex ℝ K₂ := by
    simpa [K₂] using utilityDemandSet_convex (u i₂) p w (hquasiconcave i₂)
  have hy₁notK₂ : y₁ ∉ K₂ := by
    simpa [K₂] using hy₁not
  obtain ⟨f, c, hysep, hKsep⟩ :=
    geometric_hahn_banach_point_closed hK₂convex hK₂closed hy₁notK₂
  let q : Bundle L := dualPriceVector f
  have hqy₁ : dot q y₁ < c := by
    rw [← dual_eq_dot f y₁]
    exact hysep
  have hqK₂ : ∀ z, UtilityDemand (u i₂) p w z → c < dot q z := by
    intro z hz
    rw [← dual_eq_dot f z]
    exact hKsep z (by simpa [K₂] using hz)
  let m : ℝ := (c + dot q y₁) / 2
  have hqy₁m : dot q y₁ < m := by
    dsimp [m]
    linarith
  have hmc : m < c := by
    dsimp [m]
    linarith
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let p' : ℕ → Bundle L := fun n ↦ p + ε n • q
  let w' : ℕ → ℝ := fun n ↦ w + ε n * m
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hεzero : Tendsto ε atTop (nhds 0) := by
    simpa [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  have hp'tendsto : Tendsto p' atTop (nhds p) := by
    dsimp [p']
    simpa using (tendsto_const_nhds.add (hεzero.smul_const q))
  have hw'tendsto : Tendsto w' atTop (nhds w) := by
    dsimp [w']
    simpa using (tendsto_const_nhds.add (hεzero.mul_const m))
  have hmarketTendsto :
      Tendsto (fun n ↦ (p' n, w' n)) atTop (nhds (p, w)) :=
    hp'tendsto.prodMk_nhds hw'tendsto
  let O : Set (Bundle L) := {z | c < dot q z}
  have hOopen : IsOpen O := by
    simpa [O] using isOpen_lt continuous_const (continuous_dot q)
  have hK₂O : utilityDemandSet (u i₂) p w ⊆ O := by
    intro z hz
    exact hqK₂ z hz
  have hDemandEventually :
      ∀ᶠ n in atTop, utilityDemandSet (u i₂) (p' n) (w' n) ⊆ O := by
    exact hmarketTendsto.eventually
      ((utilityDemand_upperHemicontinuousAt
        (u i₂) p w (hcontinuous i₂) hp hw).forall_isOpen O hOopen hK₂O)
  have hp'Eventually : ∀ᶠ n in atTop, PositivePrice (p' n) := by
    exact hp'tendsto.eventually (positivePrice_isOpen.mem_nhds hp)
  have hw'Eventually : ∀ᶠ n in atTop, 0 < w' n := by
    exact hw'tendsto.eventually (isOpen_Ioi.mem_nhds hw)
  obtain ⟨n, hDemandO, hp'n, hw'n⟩ :=
    (hDemandEventually.and (hp'Eventually.and hw'Eventually)).exists
  obtain ⟨y₂, hy₂⟩ :=
    exists_utilityDemand (u i₂) (p' n) (w' n)
      (hcontinuous i₂) hp'n hw'n.le
  have hqy₂ : c < dot q y₂ := hDemandO hy₂
  have hy₁wealth : dot p y₁ = w :=
    utilityDemand_expenditure_eq_wealth (u i₁) p w y₁
      hL hp (hincreasing i₁) hy₁
  have hp'y₁ : dot (p' n) y₁ < w' n := by
    have hmul : ε n * dot q y₁ < ε n * m :=
      mul_lt_mul_of_pos_left hqy₁m (hεpos n)
    rw [show dot (p' n) y₁ = dot p y₁ + ε n * dot q y₁ by
      simp only [p', dot_add_left', dot_smul_left']]
    dsimp [w']
    linarith
  have hpy₂ : dot p y₂ < w := by
    have hqm : m < dot q y₂ := hmc.trans hqy₂
    have hmul : ε n * m < ε n * dot q y₂ :=
      mul_lt_mul_of_pos_left hqm (hεpos n)
    have hfeasible := hy₂.1.2
    rw [show dot (p' n) y₂ = dot p y₂ + ε n * dot q y₂ by
      simp only [p', dot_add_left', dot_smul_left']] at hfeasible
    dsimp [w'] at hfeasible
    linarith
  refine ⟨p, p' n, w, w' n, y₁, y₂, hp, hp'n, hw, hw'n, ?_, ?_, hpy₂, hp'y₁⟩
  · exact utilityDemand_implies_justifiableDemand u i₁ p w y₁ hy₁
  · exact utilityDemand_implies_justifiableDemand u i₂ (p' n) (w' n) y₂ hy₂

/-- Failure of market-by-market component-demand agreement entails the
cross-affordability alternative. -/
theorem crossStrictAffordableJustifiableDemands_of_not_agreeOnMarkets
    [Nonempty I]
    (u : I → Utility L)
    (hL : 0 < L)
    (hcontinuous : ∀ i, Continuous (u i))
    (hquasiconcave :
      ∀ i, QuasiconcaveOn ℝ {x : Bundle L | Nonnegative x} (u i))
    (hincreasing : ∀ i, StrictlyIncreasing (u i))
    (hnot : ¬ ComponentDemandsAgreeOnMarkets u) :
    CrossStrictAffordableJustifiableDemands u := by
  rw [ComponentDemandsAgreeOnMarkets] at hnot
  push Not at hnot
  obtain ⟨i, j, p, w, hp, hw, x, hdiff⟩ := hnot
  rcases hdiff with ⟨hxi, hxnotj⟩ | ⟨hxnoti, hxj⟩
  ·
    exact crossStrictAffordableJustifiableDemands_of_demandDifference
      u i j p w x hL hcontinuous hquasiconcave hincreasing hp hw hxi hxnotj
  ·
    exact crossStrictAffordableJustifiableDemands_of_demandDifference
      u j i p w x hL hcontinuous hquasiconcave hincreasing hp hw hxj hxnoti

/-! ## The common-demand branch and the full either/or -/

/-- Market-specific agreement suffices for the ordinary/justifiable demand
identity at that market. -/
theorem justifiableDemand_iff_of_agreeOnMarkets
    [Nonempty I]
    (u : I → Utility L)
    (hcontinuous : ∀ i, Continuous (u i))
    (hagree : ComponentDemandsAgreeOnMarkets u)
    (p : Bundle L) (w : ℝ) (hp : PositivePrice p) (hw : 0 < w)
    (i₀ : I) (x : Bundle L) :
    JustifiableDemand u p w x ↔ UtilityDemand (u i₀) p w x := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ :=
      exists_utilityDemand (u i₀) p w (hcontinuous i₀) hp hw.le
    refine ⟨hx.1, ?_⟩
    intro y hy
    by_contra hnot
    have hygt : u i₀ x < u i₀ y := lt_of_not_ge hnot
    have hx_not : ¬ UtilityDemand (u i₀) p w x := by
      intro hxd
      exact (not_lt_of_ge (hxd.2 y hy)) hygt
    have hz_all : ∀ i, UtilityDemand (u i) p w z := by
      intro i
      exact (hagree i₀ i p w hp hw z).mp hz
    have hx_not_all : ∀ i, ¬ UtilityDemand (u i) p w x := by
      intro i hxi
      exact hx_not ((hagree i i₀ p w hp hw x).mp hxi)
    have hstrict_all : ∀ i, u i x < u i z := by
      intro i
      have hle : u i x ≤ u i z := (hz_all i).2 x hx.1
      exact lt_of_le_of_ne hle fun heq ↦ by
        apply hx_not_all i
        refine ⟨hx.1, ?_⟩
        intro a ha
        calc
          u i a ≤ u i z := (hz_all i).2 a ha
          _ = u i x := heq.symm
    obtain ⟨i, hi⟩ := hx.2 z hz.1
    exact (not_lt_of_ge hi) (hstrict_all i)
  · exact utilityDemand_implies_justifiableDemand u i₀ p w x

private theorem observed_wealth_pos (D : Dataset L T) (t : T) :
    0 < expenditure D t (D.choice t) := by
  have hdom : StrictDominates (D.choice t) 0 := by
    exact ⟨D.choice_nonneg t, D.choice_ne_zero t⟩
  have h := dot_strictlyIncreasing_of_pos (D.price_pos t) hdom
  simpa [expenditure] using h

/-- Under agreement on positive markets, every finite dataset rationalized
by the justifiable relation satisfies GARP. -/
theorem garp_of_justifiableRationalization_of_agreeOnMarkets
    [Nonempty I] [Fintype T] [Nonempty T]
    (D : Dataset L T) (u : I → Utility L)
    (hcontinuous : ∀ i, Continuous (u i))
    (hincreasing : ∀ i, StrictlyIncreasing (u i))
    (hagree : ComponentDemandsAgreeOnMarkets u)
    (hrat : JustifiableRationalizes D u) :
    GARP D := by
  let i₀ : I := Classical.choice inferInstance
  have hutility : UtilityRationalizes D (u i₀) := by
    intro t y hy
    have hp : PositivePrice (D.price t) := D.price_pos t
    have hw : 0 < expenditure D t (D.choice t) := observed_wealth_pos D t
    have hjust : JustifiableDemand u (D.price t)
        (expenditure D t (D.choice t)) (D.choice t) := by
      refine ⟨⟨D.choice_nonneg t, le_rfl⟩, ?_⟩
      intro z hz
      exact hrat t z hz
    have hord :=
      (justifiableDemand_iff_of_agreeOnMarkets
        u hcontinuous hagree (D.price t)
        (expenditure D t (D.choice t)) hp hw i₀ (D.choice t)).mp hjust
    exact hord.2 y hy
  exact garp_of_strictlyIncreasing_utilityRationalization D (u i₀)
    (hincreasing i₀) hutility

/-- **Lemma 6 (justifiable-demand dichotomy).**  Either every finite
dataset rationalized by the justifiable relation satisfies GARP, or there
are two justifiable demands for which each chosen bundle is strictly
affordable at the other market.

The paper assumes a nonempty compact utility family in order to write the
relation as an attained numerical maximum.  At the relational level used
here, nonemptiness is sufficient and compactness is not consumed. -/
theorem justifiableDemand_dichotomy
    [Nonempty I]
    (u : I → Utility L)
    (hL : 0 < L)
    (hcontinuous : ∀ i, Continuous (u i))
    (hquasiconcave :
      ∀ i, QuasiconcaveOn ℝ {x : Bundle L | Nonnegative x} (u i))
    (hincreasing : ∀ i, StrictlyIncreasing (u i)) :
    (∀ {T : Type} [Fintype T] [Nonempty T],
      ∀ D : Dataset L T, JustifiableRationalizes D u → GARP D) ∨
      CrossStrictAffordableJustifiableDemands u := by
  classical
  by_cases hagree : ComponentDemandsAgreeOnMarkets u
  · left
    intro T _ _ D hrat
    exact garp_of_justifiableRationalization_of_agreeOnMarkets
      D u hcontinuous hincreasing hagree hrat
  · right
    exact crossStrictAffordableJustifiableDemands_of_not_agreeOnMarkets
      u hL hcontinuous hquasiconcave hincreasing hagree

/-! ## The compact numerical representation -/

/-- The paper's numerical justifiable preference
`max i, (u i x - u i y)`, expressed as a compact CMU with a singleton
inner parameter. -/
noncomputable def compactJustifiablePreference
    [TopologicalSpace I] (u : I → Utility L) : PreferenceFunction L :=
  compactCMU (Set.univ : Set I) ({PUnit.unit} : Set PUnit.{1})
    (fun i (_ : PUnit.{1}) ↦ u i)

/-- Joint continuity of the utility evaluation differences, in exactly the
parameter order expected by `compactCMU`. -/
def CompactJustifiablePayoffContinuous
    [TopologicalSpace I] (u : I → Utility L) : Prop :=
  CompactPayoffContinuous (fun i (_ : PUnit.{1}) ↦ u i)

private theorem compactCoalitionScore_punit
    [TopologicalSpace I] (u : I → Utility L)
    (i : I) (x y : Bundle L) :
    compactCoalitionScore ({PUnit.unit} : Set PUnit.{1})
      (fun i (_ : PUnit.{1}) ↦ u i) i x y = u i x - u i y := by
  simp [compactCoalitionScore]

/-- On a nonempty compact utility family, the sign of the attained numeric
maximum is exactly weak justifiability. -/
theorem compactJustifiablePreference_nonnegative_iff
    [TopologicalSpace I] [CompactSpace I] [Nonempty I]
    (u : I → Utility L)
    (hu : CompactJustifiablePayoffContinuous u)
    (x y : Bundle L) :
    0 ≤ compactJustifiablePreference u x y ↔
      JustifiablyPreferred u x y := by
  constructor
  · intro h
    obtain ⟨i, _hi, hattain⟩ :=
      compactCMU_attains (J := ({PUnit.unit} : Set PUnit.{1}))
        isCompact_univ Set.univ_nonempty
        isCompact_singleton hu x y
    refine ⟨i, ?_⟩
    rw [compactJustifiablePreference, hattain,
      compactCoalitionScore_punit] at h
    linarith
  · rintro ⟨i, hi⟩
    have hle := compactCoalitionScore_le_compactCMU
      (J := ({PUnit.unit} : Set PUnit.{1}))
      isCompact_univ Set.univ_nonempty isCompact_singleton hu
      i (Set.mem_univ i) x y
    rw [compactCoalitionScore_punit] at hle
    change u i x - u i y ≤ compactJustifiablePreference u x y at hle
    linarith

/-- Numerical demand for the compact maximum representation is exactly
the relational justifiable-demand predicate used by Lemma 6. -/
theorem preferenceDemand_compactJustifiablePreference_iff
    [TopologicalSpace I] [CompactSpace I] [Nonempty I]
    (u : I → Utility L)
    (hu : CompactJustifiablePayoffContinuous u)
    (p : Bundle L) (w : ℝ) (x : Bundle L) :
    PreferenceDemand (compactJustifiablePreference u) p w x ↔
      JustifiableDemand u p w x := by
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, ?_⟩
    intro y hy
    exact (compactJustifiablePreference_nonnegative_iff u hu x y).mp
      (hmax y hy)
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, ?_⟩
    intro y hy
    exact (compactJustifiablePreference_nonnegative_iff u hu x y).mpr
      (hmax y hy)

/-- Dataset rationalization by the attained numerical maximum is exactly
rationalization by weak justifiability. -/
theorem preferenceRationalizes_compactJustifiablePreference_iff
    [TopologicalSpace I] [CompactSpace I] [Nonempty I]
    (D : Dataset L T) (u : I → Utility L)
    (hu : CompactJustifiablePayoffContinuous u) :
    PreferenceRationalizes D (compactJustifiablePreference u) ↔
      JustifiableRationalizes D u := by
  constructor
  · intro h t y hy
    exact (compactJustifiablePreference_nonnegative_iff
      u hu (D.choice t) y).mp (h t y hy)
  · intro h t y hy
    exact (compactJustifiablePreference_nonnegative_iff
      u hu (D.choice t) y).mpr (h t y hy)

/-- The second alternative of Lemma 6 stated for an arbitrary numerical
preference function. -/
def CrossStrictAffordablePreferenceDemands
    (r : PreferenceFunction L) : Prop :=
  ∃ p₁ p₂ : Bundle L, ∃ w₁ w₂ : ℝ, ∃ x₁ x₂ : Bundle L,
    PositivePrice p₁ ∧ PositivePrice p₂ ∧ 0 < w₁ ∧ 0 < w₂ ∧
    PreferenceDemand r p₁ w₁ x₁ ∧
    PreferenceDemand r p₂ w₂ x₂ ∧
    dot p₁ x₂ < w₁ ∧ dot p₂ x₁ < w₂

/-- A compact attained justifiable preference is complete in sign: for
every pair, one of the two directions is weakly preferred. -/
theorem compactJustifiablePreference_complete
    [TopologicalSpace I] [CompactSpace I] [Nonempty I]
    (u : I → Utility L)
    (hu : CompactJustifiablePayoffContinuous u)
    (x y : Bundle L) :
    0 ≤ compactJustifiablePreference u x y ∨
      0 ≤ compactJustifiablePreference u y x := by
  let i₀ : I := Classical.choice inferInstance
  rcases le_total (u i₀ y) (u i₀ x) with hxy | hyx
  · left
    exact (compactJustifiablePreference_nonnegative_iff u hu x y).mpr ⟨i₀, hxy⟩
  · right
    exact (compactJustifiablePreference_nonnegative_iff u hu y x).mpr ⟨i₀, hyx⟩

/-- Compact attainment preserves joint continuity of the numerical
justifiable preference. -/
theorem compactJustifiablePreference_continuous
    [TopologicalSpace I] [CompactSpace I]
    (u : I → Utility L)
    (hu : CompactJustifiablePayoffContinuous u) :
    ContinuousPreference (compactJustifiablePreference u) := by
  exact compactCMU_continuous isCompact_univ isCompact_singleton hu

/-- If all utilities in the compact family are strictly increasing, so is
the attained numerical justifiable preference in its first argument. -/
theorem compactJustifiablePreference_strictlyIncreasingFirst
    [TopologicalSpace I] [CompactSpace I] [Nonempty I]
    (u : I → Utility L)
    (hucont : CompactJustifiablePayoffContinuous u)
    (huinc : ∀ i, StrictlyIncreasing (u i)) :
    StrictlyIncreasingFirst (compactJustifiablePreference u) := by
  exact compactCMU_strictlyIncreasingFirst
    isCompact_univ Set.univ_nonempty
    isCompact_singleton (Set.singleton_nonempty PUnit.unit)
    hucont (fun i _ ↦ huinc i)

/-- **Lemma 6, numerical form.**  For the paper's attained compact maximum
representation, either all rationalized finite datasets satisfy GARP or
two positive-price, positive-wealth demand observations strictly cross
each other's budgets. -/
theorem compactJustifiablePreference_dichotomy
    [TopologicalSpace I] [CompactSpace I] [Nonempty I]
    (u : I → Utility L)
    (hL : 0 < L)
    (hpayoff : CompactJustifiablePayoffContinuous u)
    (hcontinuous : ∀ i, Continuous (u i))
    (hquasiconcave :
      ∀ i, QuasiconcaveOn ℝ {x : Bundle L | Nonnegative x} (u i))
    (hincreasing : ∀ i, StrictlyIncreasing (u i)) :
    (∀ {T : Type} [Fintype T] [Nonempty T],
      ∀ D : Dataset L T,
        PreferenceRationalizes D (compactJustifiablePreference u) → GARP D) ∨
      CrossStrictAffordablePreferenceDemands
        (compactJustifiablePreference u) := by
  rcases justifiableDemand_dichotomy
      u hL hcontinuous hquasiconcave hincreasing with hgarp | hcross
  · left
    intro T _ _ D hrat
    exact hgarp D
      ((preferenceRationalizes_compactJustifiablePreference_iff
        D u hpayoff).mp hrat)
  · right
    rcases hcross with
      ⟨p₁, p₂, w₁, w₂, x₁, x₂, hp₁, hp₂, hw₁, hw₂,
        hx₁, hx₂, hcross₁, hcross₂⟩
    refine ⟨p₁, p₂, w₁, w₂, x₁, x₂,
      hp₁, hp₂, hw₁, hw₂, ?_, ?_, hcross₁, hcross₂⟩
    · exact (preferenceDemand_compactJustifiablePreference_iff
        u hpayoff p₁ w₁ x₁).mpr hx₁
    · exact (preferenceDemand_compactJustifiablePreference_iff
        u hpayoff p₂ w₂ x₂).mpr hx₂

end WGARP
