import WGARP.CompactCMU
import WGARP.Afriat
import WGARP.Minimax
import WGARP.Necessity
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Topology.Sion

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Matrix coalitional multi-utilities

This file implements the mixed-strategy construction used in the retained
part of Theorem 1.  A finite matrix of ordinary utilities is extended
bilinearly to the standard simplex.  The resulting preference is the compact
max--min CMU from `WGARP.CompactCMU`.

The final skew-symmetry theorem is numerical, not merely sign asymmetry.  Its
proof applies Sion's minimax theorem to the finite simplex and swaps a saddle
point for the transposed difference matrix.
-/

open scoped BigOperators
open Set

namespace WGARP

variable {L : ℕ} {T : Type*} [Fintype T]

/-- Mixed strategies over the finite type `T`. -/
abbrev MixedStrategy (T : Type*) := T → ℝ

/-- The common strategy set used by the outer and inner agents. -/
def strategySimplex (T : Type*) [Fintype T] : Set (MixedStrategy T) :=
  stdSimplex ℝ T

theorem strategySimplex_compact : IsCompact (strategySimplex T) := by
  simpa [strategySimplex] using isCompact_stdSimplex ℝ T

theorem strategySimplex_convex : Convex ℝ (strategySimplex T) := by
  simpa [strategySimplex] using convex_stdSimplex ℝ T

theorem strategySimplex_nonempty [Nonempty T] :
    (strategySimplex T).Nonempty := by
  classical
  let t : T := Classical.choice inferInstance
  exact ⟨Pi.single t 1, by simpa [strategySimplex] using single_mem_stdSimplex ℝ t⟩

/-- The matrix obtained by evaluating every component utility at a bundle. -/
def utilityMatrix (u : T → T → Utility L) (x : Bundle L) : Matrix T T ℝ :=
  fun i j ↦ u i j x

/-- The bilinear payoff of a real matrix at two mixed strategies. -/
def matrixPayoff (A : Matrix T T ℝ)
    (p q : MixedStrategy T) : ℝ :=
  ∑ i, ∑ j, p i * q j * A i j

theorem matrixPayoff_eq_sum
    (A : Matrix T T ℝ) (p q : MixedStrategy T) :
    matrixPayoff A p q = ∑ i, ∑ j, p i * q j * A i j := by
  rfl

/-- Bilinear extension of a matrix of component utilities. -/
def mixedUtility (u : T → T → Utility L)
    (p q : MixedStrategy T) : Utility L :=
  fun x ↦ matrixPayoff (utilityMatrix u x) p q

theorem mixedUtility_eq_sum
    (u : T → T → Utility L) (p q : MixedStrategy T) (x : Bundle L) :
    mixedUtility u p q x = ∑ i, ∑ j, p i * q j * u i j x := by
  exact matrixPayoff_eq_sum (utilityMatrix u x) p q

/-- The matrix CMU: the compact max--min value over two copies of the finite
standard simplex. -/
noncomputable def matrixCMU (u : T → T → Utility L) : PreferenceFunction L :=
  compactCMU (strategySimplex T) (strategySimplex T) (mixedUtility u)

/-- The zero-sum payoff matrix associated with a pair of bundles. -/
def utilityDifferenceMatrix (u : T → T → Utility L)
    (x y : Bundle L) : Matrix T T ℝ :=
  fun i j ↦ u i j x - u i j y

/-- The payoff difference of a mixed utility is the bilinear payoff of the
pointwise difference matrix. -/
theorem mixedUtility_sub_eq_matrixPayoff
    (u : T → T → Utility L) (p q : MixedStrategy T) (x y : Bundle L) :
    mixedUtility u p q x - mixedUtility u p q y =
      matrixPayoff (fun i j ↦ u i j x - u i j y) p q := by
  rw [mixedUtility_eq_sum, mixedUtility_eq_sum, matrixPayoff_eq_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

theorem mixedUtility_sub_eq_differencePayoff
    (u : T → T → Utility L) (p q : MixedStrategy T) (x y : Bundle L) :
    mixedUtility u p q x - mixedUtility u p q y =
      matrixPayoff (utilityDifferenceMatrix u x y) p q := by
  change mixedUtility u p q x - mixedUtility u p q y =
    matrixPayoff (fun i j ↦ u i j x - u i j y) p q
  exact mixedUtility_sub_eq_matrixPayoff u p q x y

@[simp]
theorem utilityDifferenceMatrix_swap
    (u : T → T → Utility L) (x y : Bundle L) :
    utilityDifferenceMatrix u y x = -utilityDifferenceMatrix u x y := by
  ext i j
  simp [utilityDifferenceMatrix]

theorem matrixPayoff_neg
    (A : Matrix T T ℝ) (p q : MixedStrategy T) :
    matrixPayoff (-A) p q = -matrixPayoff A p q := by
  rw [matrixPayoff_eq_sum, matrixPayoff_eq_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  simp

theorem matrixPayoff_swap_of_transpose_eq
    {A : Matrix T T ℝ} (hA : A.transpose = A) (p q : MixedStrategy T) :
    matrixPayoff A p q = matrixPayoff A q p := by
  rw [matrixPayoff_eq_sum, matrixPayoff_eq_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  have hij : A j i = A i j := congrFun (congrFun hA i) j
  rw [hij]
  ring

/-- Symmetry of the underlying utility matrix, as equality of utility
functions rather than only equality at observed bundles. -/
def SymmetricUtilityMatrix (u : T → T → Utility L) : Prop :=
  ∀ i j, u i j = u j i

theorem utilityMatrix_transpose_eq
    {u : T → T → Utility L} (hsym : SymmetricUtilityMatrix u)
    (x : Bundle L) :
    (utilityMatrix u x).transpose = utilityMatrix u x := by
  ext i j
  exact congrFun (hsym j i) x

theorem utilityDifferenceMatrix_transpose_eq
    {u : T → T → Utility L} (hsym : SymmetricUtilityMatrix u)
    (x y : Bundle L) :
    (utilityDifferenceMatrix u x y).transpose = utilityDifferenceMatrix u x y := by
  ext i j
  change u j i x - u j i y = u i j x - u i j y
  rw [hsym j i]

theorem mixedUtility_swap
    {u : T → T → Utility L} (hsym : SymmetricUtilityMatrix u)
    (p q : MixedStrategy T) :
    mixedUtility u p q = mixedUtility u q p := by
  funext x
  exact matrixPayoff_swap_of_transpose_eq (utilityMatrix_transpose_eq hsym x) p q

/-! ## Identification with the finite zero-sum game -/

theorem matrixPayoff_eq_finiteGame_payoff
    (A : Matrix T T ℝ) (p q : MixedStrategy T) :
    matrixPayoff A p q = FiniteGame.payoff A p q := rfl

theorem compactCoalitionScore_mixedUtility_eq_gameLower
    (u : T → T → Utility L) (p : MixedStrategy T) (x y : Bundle L) :
    compactCoalitionScore (strategySimplex T) (mixedUtility u) p x y =
      FiniteGame.lower (utilityDifferenceMatrix u x y) p := by
  unfold compactCoalitionScore FiniteGame.lower
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q, by simpa [strategySimplex, FiniteGame.simplex] using hq, ?_⟩
    calc
      FiniteGame.payoff (utilityDifferenceMatrix u x y) p q =
          matrixPayoff (utilityDifferenceMatrix u x y) p q := rfl
      _ = mixedUtility u p q x - mixedUtility u p q y :=
        (mixedUtility_sub_eq_differencePayoff u p q x y).symm
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q, by simpa [strategySimplex, FiniteGame.simplex] using hq, ?_⟩
    calc
      mixedUtility u p q x - mixedUtility u p q y =
          matrixPayoff (utilityDifferenceMatrix u x y) p q :=
        mixedUtility_sub_eq_differencePayoff u p q x y
      _ = FiniteGame.payoff (utilityDifferenceMatrix u x y) p q := rfl

theorem matrixCMU_eq_finiteGame_value
    (u : T → T → Utility L) (x y : Bundle L) :
    matrixCMU u x y = FiniteGame.value (utilityDifferenceMatrix u x y) := by
  unfold matrixCMU compactCMU FiniteGame.value
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p, by simpa [strategySimplex, FiniteGame.simplex] using hp, ?_⟩
    exact (compactCoalitionScore_mixedUtility_eq_gameLower u p x y).symm
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p, by simpa [strategySimplex, FiniteGame.simplex] using hp, ?_⟩
    exact compactCoalitionScore_mixedUtility_eq_gameLower u p x y

/-- Sion's theorem, through `FiniteGame.value_neg_of_transpose_eq`, gives
the exact numerical skew symmetry of the matrix CMU. -/
theorem matrixCMU_skewSymmetric [Nonempty T]
    {u : T → T → Utility L} (hsym : SymmetricUtilityMatrix u) :
    SkewSymmetric (matrixCMU u) := by
  intro x y
  rw [matrixCMU_eq_finiteGame_value, matrixCMU_eq_finiteGame_value]
  rw [show utilityDifferenceMatrix u y x = -utilityDifferenceMatrix u x y from
    utilityDifferenceMatrix_swap u x y]
  rw [FiniteGame.value_neg_of_transpose_eq
    (utilityDifferenceMatrix_transpose_eq hsym x y)]
  ring

/-! ## Continuity -/

theorem mixedUtility_continuous
    {u : T → T → Utility L} (hu : ∀ i j, Continuous (u i j))
    (p q : MixedStrategy T) :
    Continuous (mixedUtility u p q) := by
  unfold mixedUtility matrixPayoff utilityMatrix
  apply continuous_finsetSum
  intro i _hi
  apply continuous_finsetSum
  intro j _hj
  exact continuous_const.mul (hu i j)

theorem mixedUtility_payoffContinuous
    {u : T → T → Utility L} (hu : ∀ i j, Continuous (u i j)) :
    CompactPayoffContinuous (mixedUtility u) := by
  unfold CompactPayoffContinuous compactPayoff
  simp only [mixedUtility_eq_sum]
  apply Continuous.sub
  · apply continuous_finsetSum
    intro i _hi
    apply continuous_finsetSum
    intro j _hj
    have hp : Continuous (fun z : ((Bundle L × Bundle L) × MixedStrategy T) ×
        MixedStrategy T ↦ z.1.2 i) := by fun_prop
    have hq : Continuous (fun z : ((Bundle L × Bundle L) × MixedStrategy T) ×
        MixedStrategy T ↦ z.2 j) := by fun_prop
    have hx : Continuous (fun z : ((Bundle L × Bundle L) × MixedStrategy T) ×
        MixedStrategy T ↦ u i j z.1.1.1) :=
      (hu i j).comp (by fun_prop)
    exact (hp.mul hq).mul hx
  · apply continuous_finsetSum
    intro i _hi
    apply continuous_finsetSum
    intro j _hj
    have hp : Continuous (fun z : ((Bundle L × Bundle L) × MixedStrategy T) ×
        MixedStrategy T ↦ z.1.2 i) := by fun_prop
    have hq : Continuous (fun z : ((Bundle L × Bundle L) × MixedStrategy T) ×
        MixedStrategy T ↦ z.2 j) := by fun_prop
    have hy : Continuous (fun z : ((Bundle L × Bundle L) × MixedStrategy T) ×
        MixedStrategy T ↦ u i j z.1.1.2) :=
      (hu i j).comp (by fun_prop)
    exact (hp.mul hq).mul hy

theorem matrixCMU_continuous
    {u : T → T → Utility L} (hu : ∀ i j, Continuous (u i j)) :
    ContinuousPreference (matrixCMU u) := by
  exact compactCMU_continuous strategySimplex_compact strategySimplex_compact
    (mixedUtility_payoffContinuous hu)

/-! ## Strict monotonicity -/

theorem exists_pos_coord_of_mem_strategySimplex [Nonempty T]
    {p : MixedStrategy T} (hp : p ∈ strategySimplex T) :
    ∃ i, 0 < p i := by
  have hpos : 0 < ∑ i, p i := by
    rw [hp.2]
    norm_num
  obtain ⟨i, _hi, hpi⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun i _hi ↦ hp.1 i)).mp hpos
  exact ⟨i, hpi⟩

theorem mixedUtility_strictlyIncreasing [Nonempty T]
    {u : T → T → Utility L}
    (hu : ∀ i j, StrictlyIncreasing (u i j))
    {p q : MixedStrategy T}
    (hp : p ∈ strategySimplex T) (hq : q ∈ strategySimplex T) :
    StrictlyIncreasing (mixedUtility u p q) := by
  intro x z hxz
  obtain ⟨i₀, hi₀⟩ := exists_pos_coord_of_mem_strategySimplex hp
  obtain ⟨j₀, hj₀⟩ := exists_pos_coord_of_mem_strategySimplex hq
  have hterm_nonneg : ∀ i j, 0 ≤ p i * q j * (u i j x - u i j z) := by
    intro i j
    exact mul_nonneg (mul_nonneg (hp.1 i) (hq.1 j))
      (sub_nonneg.mpr (le_of_lt (hu i j hxz)))
  have hinner_nonneg : ∀ i, 0 ≤ ∑ j, p i * q j * (u i j x - u i j z) := by
    intro i
    exact Finset.sum_nonneg fun j _hj ↦ hterm_nonneg i j
  have hinner_pos : 0 < ∑ j, p i₀ * q j * (u i₀ j x - u i₀ j z) := by
    apply (Finset.sum_pos_iff_of_nonneg (fun j _hj ↦ hterm_nonneg i₀ j)).2
    refine ⟨j₀, Finset.mem_univ j₀, ?_⟩
    exact mul_pos (mul_pos hi₀ hj₀) (sub_pos.mpr (hu i₀ j₀ hxz))
  have hsum_pos : 0 < ∑ i, ∑ j, p i * q j * (u i j x - u i j z) := by
    apply (Finset.sum_pos_iff_of_nonneg (fun i _hi ↦ hinner_nonneg i)).2
    exact ⟨i₀, Finset.mem_univ i₀, hinner_pos⟩
  have hdiff :
      mixedUtility u p q x - mixedUtility u p q z =
        ∑ i, ∑ j, p i * q j * (u i j x - u i j z) := by
    rw [mixedUtility_sub_eq_matrixPayoff, matrixPayoff_eq_sum]
  linarith

theorem matrixCMU_strictlyIncreasingFirst [Nonempty T]
    {u : T → T → Utility L}
    (hucont : ∀ i j, Continuous (u i j))
    (huinc : ∀ i j, StrictlyIncreasing (u i j)) :
    StrictlyIncreasingFirst (matrixCMU u) := by
  intro x z y hxz
  let S : Set (MixedStrategy T) := strategySimplex T
  have hScompact : IsCompact S := strategySimplex_compact
  have hSne : S.Nonempty := strategySimplex_nonempty
  have hmcont : CompactPayoffContinuous (mixedUtility u) :=
    mixedUtility_payoffContinuous hucont
  have hinner : ∀ p, p ∈ S →
      compactCoalitionScore S (mixedUtility u) p z y <
        compactCoalitionScore S (mixedUtility u) p x y := by
    intro p hp
    obtain ⟨q, hq, hqx⟩ :=
      compactCoalitionScore_attains hScompact hSne hmcont p x y
    calc
      compactCoalitionScore S (mixedUtility u) p z y ≤
          mixedUtility u p q z - mixedUtility u p q y :=
        compactCoalitionScore_le hScompact hSne hmcont p q hq z y
      _ < mixedUtility u p q x - mixedUtility u p q y :=
        sub_lt_sub_right (mixedUtility_strictlyIncreasing huinc hp hq hxz) _
      _ = compactCoalitionScore S (mixedUtility u) p x y := hqx.symm
  obtain ⟨p, hp, hpz⟩ :=
    compactCMU_attains hScompact hSne hScompact hmcont z y
  change compactCMU S S (mixedUtility u) z y <
    compactCMU S S (mixedUtility u) x y
  calc
    compactCMU S S (mixedUtility u) z y =
        compactCoalitionScore S (mixedUtility u) p z y := hpz
    _ < compactCoalitionScore S (mixedUtility u) p x y := hinner p hp
    _ ≤ compactCMU S S (mixedUtility u) x y :=
      compactCoalitionScore_le_compactCMU hScompact hSne hScompact hmcont p hp x y

theorem matrixCMU_strictlyDecreasingSecond [Nonempty T]
    {u : T → T → Utility L}
    (hucont : ∀ i j, Continuous (u i j))
    (huinc : ∀ i j, StrictlyIncreasing (u i j)) :
    ∀ ⦃x y z : Bundle L⦄, StrictDominates y z →
      matrixCMU u x y < matrixCMU u x z := by
  intro x y z hyz
  let S : Set (MixedStrategy T) := strategySimplex T
  have hScompact : IsCompact S := strategySimplex_compact
  have hSne : S.Nonempty := strategySimplex_nonempty
  have hmcont : CompactPayoffContinuous (mixedUtility u) :=
    mixedUtility_payoffContinuous hucont
  have hinner : ∀ p, p ∈ S →
      compactCoalitionScore S (mixedUtility u) p x y <
        compactCoalitionScore S (mixedUtility u) p x z := by
    intro p hp
    obtain ⟨q, hq, hqz⟩ :=
      compactCoalitionScore_attains hScompact hSne hmcont p x z
    calc
      compactCoalitionScore S (mixedUtility u) p x y ≤
          mixedUtility u p q x - mixedUtility u p q y :=
        compactCoalitionScore_le hScompact hSne hmcont p q hq x y
      _ < mixedUtility u p q x - mixedUtility u p q z :=
        sub_lt_sub_left (mixedUtility_strictlyIncreasing huinc hp hq hyz) _
      _ = compactCoalitionScore S (mixedUtility u) p x z := hqz.symm
  obtain ⟨p, hp, hpy⟩ :=
    compactCMU_attains hScompact hSne hScompact hmcont x y
  change compactCMU S S (mixedUtility u) x y <
    compactCMU S S (mixedUtility u) x z
  calc
    compactCMU S S (mixedUtility u) x y =
        compactCoalitionScore S (mixedUtility u) p x y := hpy
    _ < compactCoalitionScore S (mixedUtility u) p x z := hinner p hp
    _ ≤ compactCMU S S (mixedUtility u) x z :=
      compactCoalitionScore_le_compactCMU hScompact hSne hScompact hmcont p hp x z

/-! ## Concavity of mixed agents -/

/-- Every entry in a utility matrix is concave on the whole commodity
space. -/
def ConcaveUtilityMatrix (u : T → T → Utility L) : Prop :=
  ∀ i j, ConcaveOn ℝ Set.univ (u i j)

theorem mixedUtility_concave
    {u : T → T → Utility L} (hu : ConcaveUtilityMatrix u)
    {p q : MixedStrategy T}
    (hp : p ∈ strategySimplex T) (hq : q ∈ strategySimplex T) :
    ConcaveOn ℝ Set.univ (mixedUtility u p q) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b ha hb hab
  have hcomponent : ∀ i j,
      p i * q j * (a * u i j x + b * u i j y) ≤
        p i * q j * u i j (a • x + b • y) := by
    intro i j
    have hij := (hu i j).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    rw [smul_eq_mul, smul_eq_mul] at hij
    exact mul_le_mul_of_nonneg_left hij (mul_nonneg (hp.1 i) (hq.1 j))
  have hsum :
      (∑ i, ∑ j, p i * q j * (a * u i j x + b * u i j y)) ≤
        ∑ i, ∑ j, p i * q j * u i j (a • x + b • y) := by
    apply Finset.sum_le_sum
    intro i _hi
    apply Finset.sum_le_sum
    intro j _hj
    exact hcomponent i j
  unfold mixedUtility matrixPayoff utilityMatrix
  rw [smul_eq_mul, smul_eq_mul]
  calc
    a * (∑ i, ∑ j, p i * q j * u i j x) +
          b * (∑ i, ∑ j, p i * q j * u i j y) =
        ∑ i, (a * (∑ j, p i * q j * u i j x) +
          b * (∑ j, p i * q j * u i j y)) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, p i * q j * (a * u i j x + b * u i j y) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ ≤ ∑ i, ∑ j, p i * q j * u i j (a • x + b • y) := hsum

/-! ## Coherence and rationalization -/

theorem mixedUtility_compactCoherent
    {u : T → T → Utility L} (hsym : SymmetricUtilityMatrix u) :
    CompactCoherent (strategySimplex T) (strategySimplex T) (mixedUtility u) := by
  intro p hp p' hp'
  exact ⟨p', hp', p, hp, mixedUtility_swap hsym p p'⟩

theorem matrixCMU_add_swap_nonpos [Nonempty T]
    {u : T → T → Utility L}
    (hucont : ∀ i j, Continuous (u i j))
    (hsym : SymmetricUtilityMatrix u) (x y : Bundle L) :
    matrixCMU u x y + matrixCMU u y x ≤ 0 := by
  exact compactCMU_add_swap_nonpos strategySimplex_compact strategySimplex_nonempty
    strategySimplex_compact strategySimplex_nonempty
    (mixedUtility_payoffContinuous hucont) (mixedUtility_compactCoherent hsym) x y

theorem matrixCMU_weakSignAsymmetric [Nonempty T]
    {u : T → T → Utility L}
    (hucont : ∀ i j, Continuous (u i j))
    (hsym : SymmetricUtilityMatrix u) :
    WeakSignAsymmetric (matrixCMU u) := by
  exact compactCMU_weakSignAsymmetric strategySimplex_compact strategySimplex_nonempty
    strategySimplex_compact strategySimplex_nonempty
    (mixedUtility_payoffContinuous hucont) (mixedUtility_compactCoherent hsym)

theorem matrixCMU_signAsymmetric [Nonempty T]
    {u : T → T → Utility L}
    (hucont : ∀ i j, Continuous (u i j))
    (hsym : SymmetricUtilityMatrix u) :
    SignAsymmetric (matrixCMU u) := by
  exact compactCMU_signAsymmetric strategySimplex_compact strategySimplex_nonempty
    strategySimplex_compact strategySimplex_nonempty
    (mixedUtility_payoffContinuous hucont) (mixedUtility_compactCoherent hsym)

theorem matrixCMU_asymmetric [Nonempty T]
    {u : T → T → Utility L}
    (hucont : ∀ i j, Continuous (u i j))
    (hsym : SymmetricUtilityMatrix u) :
    Asymmetric (matrixCMU u) :=
  ⟨matrixCMU_weakSignAsymmetric hucont hsym,
    matrixCMU_signAsymmetric hucont hsym⟩

/-- Row-wise utility rationalization: every entry in row `t` selects the
observed bundle at observation `t` from that observation's budget. -/
def UtilityMatrixRowRationalizes (D : Dataset L T)
    (u : T → T → Utility L) : Prop :=
  ∀ t j y, Affordable D t y → u t j y ≤ u t j (D.choice t)

@[simp]
theorem mixedUtility_single_left [DecidableEq T]
    (u : T → T → Utility L) (t : T)
    (q : MixedStrategy T) (x : Bundle L) :
    mixedUtility u (Pi.single t 1) q x = ∑ j, q j * u t j x := by
  classical
  rw [mixedUtility_eq_sum]
  rw [Fintype.sum_eq_single t]
  · simp
  · intro i hit
    simp [Pi.single_eq_of_ne hit]

theorem matrixCMU_rationalizes [Nonempty T]
    (D : Dataset L T) {u : T → T → Utility L}
    (hucont : ∀ i j, Continuous (u i j))
    (hrat : UtilityMatrixRowRationalizes D u) :
    PreferenceRationalizes D (matrixCMU u) := by
  intro t y hy
  classical
  let S : Set (MixedStrategy T) := strategySimplex T
  let e : MixedStrategy T := Pi.single t 1
  have he : e ∈ S := by
    simpa [S, strategySimplex, e] using single_mem_stdSimplex ℝ t
  have hScompact : IsCompact S := strategySimplex_compact
  have hSne : S.Nonempty := strategySimplex_nonempty
  have hmcont : CompactPayoffContinuous (mixedUtility u) :=
    mixedUtility_payoffContinuous hucont
  obtain ⟨q, hq, hscore⟩ :=
    compactCoalitionScore_attains hScompact hSne hmcont e (D.choice t) y
  have hdiff_nonneg :
      0 ≤ mixedUtility u e q (D.choice t) - mixedUtility u e q y := by
    rw [show e = Pi.single t 1 from rfl,
      mixedUtility_single_left (T := T) u t q (D.choice t),
      mixedUtility_single_left (T := T) u t q y,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro j _hj
    rw [← mul_sub]
    exact mul_nonneg (hq.1 j) (sub_nonneg.mpr (hrat t j y hy))
  have hscore_nonneg :
      0 ≤ compactCoalitionScore S (mixedUtility u) e (D.choice t) y := by
    rw [hscore]
    exact hdiff_nonneg
  have hle := compactCoalitionScore_le_compactCMU
    hScompact hSne hScompact hmcont e he (D.choice t) y
  change 0 ≤ compactCMU S S (mixedUtility u) (D.choice t) y
  exact hscore_nonneg.trans hle

/-! ## The matrix-CMU statement in Theorem 1 -/

/-- A fully certified matrix-CMU rationalization.  The first five fields
record the matrix representation itself; the remaining fields record the
properties of the induced compact max--min preference. -/
structure MatrixCMURationalization (D : Dataset L T) where
  utilities : T → T → Utility L
  symmetric : SymmetricUtilityMatrix utilities
  entry_continuous : ∀ i j, Continuous (utilities i j)
  entry_strictlyIncreasing : ∀ i j, StrictlyIncreasing (utilities i j)
  entry_concave : ConcaveUtilityMatrix utilities
  coherent : CompactCoherent (strategySimplex T) (strategySimplex T)
    (mixedUtility utilities)
  preference_continuous : ContinuousPreference (matrixCMU utilities)
  preference_strictlyIncreasing : StrictlyIncreasingFirst (matrixCMU utilities)
  preference_skewSymmetric : SkewSymmetric (matrixCMU utilities)
  rationalizes : PreferenceRationalizes D (matrixCMU utilities)

/-- Existence form used as statement (iii) in the theorem equivalence. -/
abbrev HasMatrixCMURationalization (D : Dataset L T) : Prop :=
  Nonempty (MatrixCMURationalization D)

variable {D : Dataset L T}

/-- The symmetric matrix supplied by the constructive pairwise Afriat
utilities. -/
noncomputable def pairUtilityMatrix (certificate : PairwiseAfriat D) :
    T → T → Utility L :=
  fun s t ↦ pairUtility certificate s t

theorem pairUtilityMatrix_symmetric (certificate : PairwiseAfriat D) :
    SymmetricUtilityMatrix (pairUtilityMatrix certificate) := by
  intro s t
  exact pairUtility_symm certificate s t

theorem pairUtilityMatrix_continuous (certificate : PairwiseAfriat D) :
    ∀ s t, Continuous (pairUtilityMatrix certificate s t) := by
  intro s t
  exact pairUtility_continuous certificate s t

theorem pairUtilityMatrix_strictlyIncreasing (certificate : PairwiseAfriat D) :
    ∀ s t, StrictlyIncreasing (pairUtilityMatrix certificate s t) := by
  intro s t
  exact pairUtility_strictlyIncreasing certificate s t

theorem pairUtilityMatrix_concave (certificate : PairwiseAfriat D) :
    ConcaveUtilityMatrix (pairUtilityMatrix certificate) := by
  intro s t
  exact pairUtility_concaveOn certificate s t

theorem pairUtilityMatrix_rowRationalizes (certificate : PairwiseAfriat D) :
    UtilityMatrixRowRationalizes D (pairUtilityMatrix certificate) := by
  intro s t y hy
  exact pairUtility_rationalizes_first certificate s t hy

/-- A pairwise Afriat certificate produces all fields of the matrix-CMU
rationalization. -/
noncomputable def matrixCMURationalizationOfPairwiseAfriat [Nonempty T]
    (D : Dataset L T) (certificate : PairwiseAfriat D) :
    MatrixCMURationalization D where
  utilities := pairUtilityMatrix certificate
  symmetric := pairUtilityMatrix_symmetric certificate
  entry_continuous := pairUtilityMatrix_continuous certificate
  entry_strictlyIncreasing := pairUtilityMatrix_strictlyIncreasing certificate
  entry_concave := pairUtilityMatrix_concave certificate
  coherent := mixedUtility_compactCoherent (pairUtilityMatrix_symmetric certificate)
  preference_continuous := matrixCMU_continuous (pairUtilityMatrix_continuous certificate)
  preference_strictlyIncreasing := matrixCMU_strictlyIncreasingFirst
    (pairUtilityMatrix_continuous certificate)
    (pairUtilityMatrix_strictlyIncreasing certificate)
  preference_skewSymmetric := matrixCMU_skewSymmetric
    (pairUtilityMatrix_symmetric certificate)
  rationalizes := matrixCMU_rationalizes D
    (pairUtilityMatrix_continuous certificate)
    (pairUtilityMatrix_rowRationalizes certificate)

/-- WGARP constructively yields the symmetric matrix rationalization in
statement (iii). -/
theorem hasMatrixCMURationalization_of_wgarp [Nonempty T]
    (D : Dataset L T) (h : WGARP D) :
    HasMatrixCMURationalization D :=
  ⟨matrixCMURationalizationOfPairwiseAfriat D (pairwiseAfriatOfWGARP D h)⟩

/-- A matrix witness immediately supplies the preference in statement (i). -/
theorem exists_statementOne_preference_of_matrixCMU [Nonempty T]
    (D : Dataset L T) (h : HasMatrixCMURationalization D) :
    ∃ r : PreferenceFunction L,
      ContinuousPreference r ∧
      StrictlyIncreasingFirst r ∧
      Asymmetric r ∧
      PreferenceRationalizes D r := by
  let witness := Classical.choice h
  exact ⟨matrixCMU witness.utilities,
    witness.preference_continuous,
    witness.preference_strictlyIncreasing,
    asymmetric_of_skewSymmetric witness.preference_skewSymmetric,
    witness.rationalizes⟩

/-- Necessity for the matrix formulation follows from the paper's
asymmetric-preference necessity lemma. -/
theorem wgarp_of_matrixCMURationalization [Nonempty T]
    (D : Dataset L T) (h : HasMatrixCMURationalization D) : WGARP D := by
  obtain ⟨r, _hcontinuous, hincreasing, hasymmetric, hrationalizes⟩ :=
    exists_statementOne_preference_of_matrixCMU D h
  exact wgarp_of_asymmetric_strictlyIncreasing_rationalization
    D r hasymmetric hincreasing hrationalizes

/-- The retained matrix-CMU statement is exactly equivalent to WGARP. -/
theorem wgarp_iff_hasMatrixCMURationalization [Nonempty T]
    (D : Dataset L T) :
    WGARP D ↔ HasMatrixCMURationalization D :=
  ⟨hasMatrixCMURationalization_of_wgarp D,
    wgarp_of_matrixCMURationalization D⟩

end WGARP
