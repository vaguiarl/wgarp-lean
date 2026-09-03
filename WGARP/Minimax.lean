import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sion

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Finite zero-sum games

A small reusable layer for the minimax step in Theorem 1.  Strategies are
probability vectors in the standard simplex and payoffs are the bilinear
extension of a finite real matrix.  The game value is defined literally as
the outer supremum of inner infima.  Compactness supplies actual optimizers,
and Sion's theorem supplies a saddle point.
-/

open scoped BigOperators
open Set

namespace WGARP.FiniteGame

variable {T : Type*} [Fintype T]

/-- A mixed strategy on the finite action type `T`. -/
abbrev Strategy (T : Type*) := T → ℝ

/-- Probability vectors on `T`. -/
def simplex (T : Type*) [Fintype T] : Set (Strategy T) :=
  stdSimplex ℝ T

theorem simplex_compact : IsCompact (simplex T) := by
  simpa [simplex] using isCompact_stdSimplex ℝ T

theorem simplex_convex : Convex ℝ (simplex T) := by
  simpa [simplex] using convex_stdSimplex ℝ T

theorem simplex_nonempty [Nonempty T] : (simplex T).Nonempty := by
  classical
  let i : T := Classical.choice inferInstance
  exact ⟨Pi.single i 1, by simpa [simplex] using single_mem_stdSimplex ℝ i⟩

/-- Bilinear payoff of a finite real matrix.  The row player chooses `p`
and the column player chooses `q`. -/
def payoff (A : Matrix T T ℝ) (p q : Strategy T) : ℝ :=
  ∑ i, ∑ j, p i * q j * A i j

theorem payoff_eq_sum (A : Matrix T T ℝ) (p q : Strategy T) :
    payoff A p q = ∑ i, ∑ j, p i * q j * A i j := rfl

/-- The payoff is jointly continuous in the two mixed strategies. -/
theorem payoff_continuous (A : Matrix T T ℝ) :
    Continuous (fun z : Strategy T × Strategy T ↦ payoff A z.1 z.2) := by
  unfold payoff
  apply continuous_finsetSum
  intro i _hi
  apply continuous_finsetSum
  intro j _hj
  exact ((((continuous_apply i).comp continuous_fst).mul
    ((continuous_apply j).comp continuous_snd)).mul continuous_const)

theorem payoff_continuous_first (A : Matrix T T ℝ) (q : Strategy T) :
    Continuous (fun p ↦ payoff A p q) := by
  exact (payoff_continuous A).comp (continuous_id.prodMk continuous_const)

theorem payoff_continuous_second (A : Matrix T T ℝ) (p : Strategy T) :
    Continuous (payoff A p) := by
  exact (payoff_continuous A).comp (continuous_const.prodMk continuous_id)

/-- Payoff as a linear functional of the row strategy. -/
def payoffLeftLinear (A : Matrix T T ℝ) (q : Strategy T) :
    Strategy T →ₗ[ℝ] ℝ where
  toFun p := payoff A p q
  map_add' p r := by
    unfold payoff
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [Pi.add_apply]
    ring
  map_smul' a p := by
    unfold payoff
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [RingHom.id_apply]
    ring

/-- Payoff as a linear functional of the column strategy. -/
def payoffRightLinear (A : Matrix T T ℝ) (p : Strategy T) :
    Strategy T →ₗ[ℝ] ℝ where
  toFun q := payoff A p q
  map_add' q r := by
    unfold payoff
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [Pi.add_apply]
    ring
  map_smul' a q := by
    unfold payoff
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [RingHom.id_apply]
    ring

@[simp]
theorem payoffLeftLinear_apply (A : Matrix T T ℝ)
    (q p : Strategy T) : payoffLeftLinear A q p = payoff A p q := rfl

@[simp]
theorem payoffRightLinear_apply (A : Matrix T T ℝ)
    (p q : Strategy T) : payoffRightLinear A p q = payoff A p q := rfl

theorem payoff_convexOn_first (A : Matrix T T ℝ) (q : Strategy T) :
    ConvexOn ℝ (simplex T) (fun p ↦ payoff A p q) := by
  exact LinearMap.convexOn (payoffLeftLinear A q) simplex_convex

theorem payoff_concaveOn_first (A : Matrix T T ℝ) (q : Strategy T) :
    ConcaveOn ℝ (simplex T) (fun p ↦ payoff A p q) := by
  exact LinearMap.concaveOn (payoffLeftLinear A q) simplex_convex

theorem payoff_convexOn_second (A : Matrix T T ℝ) (p : Strategy T) :
    ConvexOn ℝ (simplex T) (payoff A p) := by
  exact LinearMap.convexOn (payoffRightLinear A p) simplex_convex

theorem payoff_concaveOn_second (A : Matrix T T ℝ) (p : Strategy T) :
    ConcaveOn ℝ (simplex T) (payoff A p) := by
  exact LinearMap.concaveOn (payoffRightLinear A p) simplex_convex

/-- The inner, column-player minimum against row strategy `p`. -/
noncomputable def lower (A : Matrix T T ℝ) (p : Strategy T) : ℝ :=
  sInf (payoff A p '' simplex T)

/-- The row player's max--min value. -/
noncomputable def value (A : Matrix T T ℝ) : ℝ :=
  sSup (lower A '' simplex T)

theorem lower_continuous (A : Matrix T T ℝ) : Continuous (lower A) := by
  change Continuous (fun p => sInf (payoff A p '' simplex T))
  exact simplex_compact.continuous_sInf (payoff_continuous A)

/-- Compactness makes the inner infimum an attained minimum. -/
theorem lower_attains [Nonempty T] (A : Matrix T T ℝ) (p : Strategy T) :
    ∃ q ∈ simplex T,
      lower A p = payoff A p q ∧
      ∀ q' ∈ simplex T, payoff A p q ≤ payoff A p q' := by
  obtain ⟨q, hq, heq, hmin⟩ :=
    simplex_compact.exists_sInf_image_eq_and_le simplex_nonempty
      (payoff_continuous_second A p).continuousOn
  exact ⟨q, hq, by simpa only [lower] using heq, hmin⟩

/-- Compactness makes the outer supremum an attained maximum. -/
theorem value_attains [Nonempty T] (A : Matrix T T ℝ) :
    ∃ p ∈ simplex T,
      value A = lower A p ∧
      ∀ p' ∈ simplex T, lower A p' ≤ lower A p := by
  obtain ⟨p, hp, heq, hmax⟩ :=
    simplex_compact.exists_sSup_image_eq_and_ge simplex_nonempty
      (lower_continuous A).continuousOn
  exact ⟨p, hp, by simpa only [value] using heq, hmax⟩

theorem lower_le_payoff [Nonempty T]
    (A : Matrix T T ℝ) (p : Strategy T)
    {q : Strategy T} (hq : q ∈ simplex T) :
    lower A p ≤ payoff A p q := by
  obtain ⟨q₀, _hq₀, heq, hmin⟩ := lower_attains A p
  rw [heq]
  exact hmin q hq

theorem lower_le_value [Nonempty T]
    (A : Matrix T T ℝ) {p : Strategy T} (hp : p ∈ simplex T) :
    lower A p ≤ value A := by
  obtain ⟨p₀, _hp₀, heq, hmax⟩ := value_attains A
  rw [heq]
  exact hmax p hp

/-- Sion's theorem supplies a saddle point.  Its first coordinate is the
minimizing column strategy and its second coordinate is the maximizing row
strategy, hence the argument reversal in the displayed payoff. -/
theorem exists_saddle [Nonempty T] (A : Matrix T T ℝ) :
    ∃ q ∈ simplex T, ∃ p ∈ simplex T,
      IsSaddlePointOn (simplex T) (simplex T)
        (fun q p ↦ payoff A p q) q p := by
  apply Sion.exists_isSaddlePointOn
      (X := simplex T) (Y := simplex T)
      (f := fun q p ↦ payoff A p q)
      simplex_nonempty simplex_convex simplex_compact
  · intro p _hp
    exact (payoff_continuous_second A p).continuousOn.lowerSemicontinuousOn
  · intro p _hp
    exact (payoff_convexOn_second A p).quasiconvexOn
  · exact simplex_convex
  · exact simplex_nonempty
  · exact simplex_compact
  · intro q _hq
    exact (payoff_continuous_first A q).continuousOn.upperSemicontinuousOn
  · intro q _hq
    exact (payoff_concaveOn_first A q).quasiconcaveOn

/-- Any saddle payoff is the literal `sSup`/`sInf` max--min value. -/
theorem value_eq_of_saddle [Nonempty T]
    (A : Matrix T T ℝ) {q p : Strategy T}
    (hq : q ∈ simplex T) (hp : p ∈ simplex T)
    (hsaddle : IsSaddlePointOn (simplex T) (simplex T)
      (fun q p ↦ payoff A p q) q p) :
    value A = payoff A p q := by
  obtain ⟨q₀, hq₀, hlower, _hmin⟩ := lower_attains A p
  have hlower_eq : lower A p = payoff A p q := by
    apply le_antisymm
    · exact lower_le_payoff A p hq
    · rw [hlower]
      exact hsaddle q₀ hq₀ p hp
  obtain ⟨p₀, hp₀, hvalue, hmax⟩ := value_attains A
  apply le_antisymm
  · rw [hvalue]
    calc
      lower A p₀ ≤ payoff A p₀ q := lower_le_payoff A p₀ hq
      _ ≤ payoff A p q := hsaddle q hq p₀ hp₀
  · rw [hvalue, ← hlower_eq]
    exact hmax p hp

theorem payoff_neg (A : Matrix T T ℝ) (p q : Strategy T) :
    payoff (-A) p q = -payoff A p q := by
  rw [payoff_eq_sum, payoff_eq_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  simp

theorem payoff_swap_of_transpose_eq
    {A : Matrix T T ℝ} (hA : A.transpose = A)
    (p q : Strategy T) :
    payoff A p q = payoff A q p := by
  rw [payoff_eq_sum, payoff_eq_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  have hij : A j i = A i j := congrFun (congrFun hA i) j
  rw [hij]
  ring

/-- A saddle point of a symmetric game becomes a saddle point of the
negated game after swapping the players. -/
theorem saddle_neg_swap_of_transpose_eq
    {A : Matrix T T ℝ} (hA : A.transpose = A)
    {q p : Strategy T}
    (hsaddle : IsSaddlePointOn (simplex T) (simplex T)
      (fun q p ↦ payoff A p q) q p) :
    IsSaddlePointOn (simplex T) (simplex T)
      (fun q p ↦ payoff (-A) p q) p q := by
  intro x hx y hy
  have hold : payoff A x q ≤ payoff A p y := hsaddle y hy x hx
  change payoff (-A) y p ≤ payoff (-A) q x
  rw [payoff_neg, payoff_neg,
    payoff_swap_of_transpose_eq hA y p,
    payoff_swap_of_transpose_eq hA q x]
  exact neg_le_neg hold

/-- For a symmetric payoff matrix, negating every entry negates the
max--min value. -/
theorem value_neg_of_transpose_eq [Nonempty T]
    {A : Matrix T T ℝ} (hA : A.transpose = A) :
    value (-A) = -value A := by
  obtain ⟨q, hq, p, hp, hsaddle⟩ := exists_saddle A
  have hvalue := value_eq_of_saddle A hq hp hsaddle
  have hnegSaddle :=
    saddle_neg_swap_of_transpose_eq hA hsaddle
  calc
    value (-A) = payoff (-A) q p :=
      value_eq_of_saddle (-A) hp hq hnegSaddle
    _ = -payoff A q p := payoff_neg A q p
    _ = -payoff A p q := by
      rw [payoff_swap_of_transpose_eq hA q p]
    _ = -value A := by rw [hvalue]

end WGARP.FiniteGame
