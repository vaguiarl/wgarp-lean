import WGARP.Data
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

/-!
# Compactly parameterized coalitional multi-utilities

This file isolates the point raised in the REStat report about Lemma 1(ii).
Pointwise infima and suprema of strictly increasing functions need not be
strictly increasing merely because they are finite-valued.  What makes the
CMU argument valid is **attainment** of both extrema.  The proofs below choose
the inner minimizer at the improved bundle and the outer maximizer at the
original bundle; compactness and continuity supply those witnesses.

The fixed compact parameter sets are exactly the form needed by the
mixed-strategy construction in `WGARP.MatrixCMU`.
-/

namespace WGARP

open Set

section AttainedEnvelopes

variable {X A : Type*} {f : A → X → ℝ} {lo hi : X → ℝ}
variable {R : X → X → Prop}

/-- An attained pointwise minimum of functions that all strictly increase
along `R` strictly increases along `R`.  The minimizer is chosen at the
larger point. -/
theorem strictlyIncreasing_attainedInf
    (hf : ∀ a, ∀ ⦃x z⦄, R x z → f a x < f a z)
    (hle : ∀ a x, lo x ≤ f a x)
    (hattain : ∀ x, ∃ a, lo x = f a x) :
    ∀ ⦃x z⦄, R x z → lo x < lo z := by
  intro x z hxz
  obtain ⟨a, ha⟩ := hattain z
  calc
    lo x ≤ f a x := hle a x
    _ < f a z := hf a hxz
    _ = lo z := ha.symm

/-- An attained pointwise maximum of functions that all strictly increase
along `R` strictly increases along `R`.  The maximizer is chosen at the
smaller point. -/
theorem strictlyIncreasing_attainedSup
    (hf : ∀ a, ∀ ⦃x z⦄, R x z → f a x < f a z)
    (hle : ∀ a x, f a x ≤ hi x)
    (hattain : ∀ x, ∃ a, hi x = f a x) :
    ∀ ⦃x z⦄, R x z → hi x < hi z := by
  intro x z hxz
  obtain ⟨a, ha⟩ := hattain x
  calc
    hi x = f a x := ha
    _ < f a z := hf a hxz
    _ ≤ hi z := hle a z

end AttainedEnvelopes

section CompactCMU

variable {L : ℕ}
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

/-- Difference delivered by the agent with inner parameter `b` in the
coalition with outer parameter `a`. -/
def compactPayoff (u : A → B → Bundle L → ℝ)
    (q : Bundle L × Bundle L) (a : A) (b : B) : ℝ :=
  u a b q.1 - u a b q.2

/-- The unanimous score of one compactly parameterized coalition. -/
noncomputable def compactCoalitionScore
    (J : Set B) (u : A → B → Bundle L → ℝ)
    (a : A) (x y : Bundle L) : ℝ :=
  sInf ((fun b => u a b x - u a b y) '' J)

/-- The compact max--min CMU value. -/
noncomputable def compactCMU
    (K : Set A) (J : Set B) (u : A → B → Bundle L → ℝ)
    (x y : Bundle L) : ℝ :=
  sSup ((fun a => compactCoalitionScore J u a x y) '' K)

/-- Joint continuity assumption in the parameter order used by the nested
compact-extremum theorems. -/
def CompactPayoffContinuous
    (u : A → B → Bundle L → ℝ) : Prop :=
  Continuous (fun z : ((Bundle L × Bundle L) × A) × B =>
    compactPayoff u z.1.1 z.1.2 z.2)

theorem compactPayoff_continuous_inner
    {u : A → B → Bundle L → ℝ}
    (hu : CompactPayoffContinuous u)
    (q : Bundle L × Bundle L) (a : A) :
    Continuous (fun b => compactPayoff u q a b) := by
  unfold CompactPayoffContinuous at hu
  have hmap : Continuous (fun b : B => ((q, a), b)) :=
    continuous_const.prodMk continuous_id
  exact hu.comp hmap

/-- Compactness makes every inner infimum an attained minimum. -/
theorem compactCoalitionScore_attains
    {J : Set B} (hJ : IsCompact J) (hneJ : J.Nonempty)
    {u : A → B → Bundle L → ℝ}
    (hu : CompactPayoffContinuous u)
    (a : A) (x y : Bundle L) :
    ∃ b ∈ J, compactCoalitionScore J u a x y = u a b x - u a b y := by
  have hcont : Continuous (fun b => compactPayoff u (x, y) a b) :=
    compactPayoff_continuous_inner hu (x, y) a
  obtain ⟨b, hb, heq⟩ :=
    hJ.exists_sInf_image_eq hneJ hcont.continuousOn
  exact ⟨b, hb, by simpa [compactCoalitionScore, compactPayoff] using heq⟩

theorem compactCoalitionScore_le
    {J : Set B} (hJ : IsCompact J) (_hneJ : J.Nonempty)
    {u : A → B → Bundle L → ℝ}
    (hu : CompactPayoffContinuous u)
    (a : A) (b : B) (hb : b ∈ J) (x y : Bundle L) :
    compactCoalitionScore J u a x y ≤ u a b x - u a b y := by
  have hcont : Continuous (fun c => compactPayoff u (x, y) a c) :=
    compactPayoff_continuous_inner hu (x, y) a
  exact csInf_le
    ((hJ.image_of_continuousOn hcont.continuousOn).bddBelow)
    (mem_image_of_mem _ hb)

/-- Berge's value-continuity conclusion for the fixed compact inner
parameter set. -/
theorem compactCoalitionScore_continuous
    {J : Set B} (hJ : IsCompact J)
    {u : A → B → Bundle L → ℝ}
    (hu : CompactPayoffContinuous u) :
    Continuous (fun z : (Bundle L × Bundle L) × A =>
      compactCoalitionScore J u z.2 z.1.1 z.1.2) := by
  unfold CompactPayoffContinuous at hu
  simpa only [compactCoalitionScore, compactPayoff] using
    hJ.continuous_sInf hu

theorem compactCoalitionScore_continuous_outer
    {J : Set B} (hJ : IsCompact J)
    {u : A → B → Bundle L → ℝ}
    (hu : CompactPayoffContinuous u)
    (q : Bundle L × Bundle L) :
    Continuous (fun a => compactCoalitionScore J u a q.1 q.2) := by
  exact (compactCoalitionScore_continuous hJ hu).comp
    (continuous_const.prodMk continuous_id)

/-- Compactness makes every outer supremum an attained maximum. -/
theorem compactCMU_attains
    {K : Set A} (hK : IsCompact K) (hneK : K.Nonempty)
    {J : Set B} (hJ : IsCompact J)
    {u : A → B → Bundle L → ℝ}
    (hu : CompactPayoffContinuous u)
    (x y : Bundle L) :
    ∃ a ∈ K, compactCMU K J u x y = compactCoalitionScore J u a x y := by
  obtain ⟨a, ha, heq⟩ := hK.exists_sSup_image_eq hneK
    (compactCoalitionScore_continuous_outer hJ hu (x, y)).continuousOn
  exact ⟨a, ha, by simpa [compactCMU] using heq⟩

theorem compactCoalitionScore_le_compactCMU
    {K : Set A} (hK : IsCompact K) (_hneK : K.Nonempty)
    {J : Set B} (hJ : IsCompact J)
    {u : A → B → Bundle L → ℝ}
    (hu : CompactPayoffContinuous u)
    (a : A) (ha : a ∈ K) (x y : Bundle L) :
    compactCoalitionScore J u a x y ≤ compactCMU K J u x y := by
  have hcont := compactCoalitionScore_continuous_outer hJ hu (x, y)
  exact le_csSup
    ((hK.image_of_continuousOn hcont.continuousOn).bddAbove)
    (mem_image_of_mem _ ha)

/-- A compactly parameterized CMU is jointly continuous. -/
theorem compactCMU_continuous
    {K : Set A} (hK : IsCompact K)
    {J : Set B} (hJ : IsCompact J)
    {u : A → B → Bundle L → ℝ}
    (hu : CompactPayoffContinuous u) :
    Continuous (fun q : Bundle L × Bundle L => compactCMU K J u q.1 q.2) := by
  simpa only [compactCMU] using
    hK.continuous_sSup (compactCoalitionScore_continuous hJ hu)

/-- The corrected REStat Lemma 1(ii), first argument.  Both extrema are
attained, and the proof uses the minimizing/maximizing witnesses on the
correct sides of the strict comparison. -/
theorem compactCMU_strictlyIncreasingFirst
    {K : Set A} (hK : IsCompact K) (hneK : K.Nonempty)
    {J : Set B} (hJ : IsCompact J) (hneJ : J.Nonempty)
    {u : A → B → Bundle L → ℝ}
    (hucont : CompactPayoffContinuous u)
    (huinc : ∀ a b, StrictlyIncreasing (u a b)) :
    StrictlyIncreasingFirst (compactCMU K J u) := by
  intro x z y hxz
  have hinner : ∀ a,
      compactCoalitionScore J u a z y < compactCoalitionScore J u a x y := by
    intro a
    obtain ⟨b, _hb, hbz⟩ :=
      compactCoalitionScore_attains hJ hneJ hucont a x y
    calc
      compactCoalitionScore J u a z y ≤ u a b z - u a b y :=
        compactCoalitionScore_le hJ hneJ hucont a b _hb z y
      _ < u a b x - u a b y := sub_lt_sub_right (huinc a b hxz) _
      _ = compactCoalitionScore J u a x y := hbz.symm
  obtain ⟨a, ha, haz⟩ := compactCMU_attains hK hneK hJ hucont z y
  calc
    compactCMU K J u z y = compactCoalitionScore J u a z y := haz
    _ < compactCoalitionScore J u a x y := hinner a
    _ ≤ compactCMU K J u x y :=
      compactCoalitionScore_le_compactCMU hK hneK hJ hucont a ha x y

/-- The dual attained-extrema argument for the comparison argument. -/
theorem compactCMU_strictlyDecreasingSecond
    {K : Set A} (hK : IsCompact K) (hneK : K.Nonempty)
    {J : Set B} (hJ : IsCompact J) (hneJ : J.Nonempty)
    {u : A → B → Bundle L → ℝ}
    (hucont : CompactPayoffContinuous u)
    (huinc : ∀ a b, StrictlyIncreasing (u a b)) :
    ∀ ⦃x y z⦄, StrictDominates y z →
      compactCMU K J u x y < compactCMU K J u x z := by
  intro x y z hyz
  have hinner : ∀ a,
      compactCoalitionScore J u a x y < compactCoalitionScore J u a x z := by
    intro a
    obtain ⟨b, _hb, hbz⟩ :=
      compactCoalitionScore_attains hJ hneJ hucont a x z
    calc
      compactCoalitionScore J u a x y ≤ u a b x - u a b y :=
        compactCoalitionScore_le hJ hneJ hucont a b _hb x y
      _ < u a b x - u a b z := sub_lt_sub_left (huinc a b hyz) _
      _ = compactCoalitionScore J u a x z := hbz.symm
  obtain ⟨a, ha, hay⟩ := compactCMU_attains hK hneK hJ hucont x y
  calc
    compactCMU K J u x y = compactCoalitionScore J u a x y := hay
    _ < compactCoalitionScore J u a x z := hinner a
    _ ≤ compactCMU K J u x z :=
      compactCoalitionScore_le_compactCMU hK hneK hJ hucont a ha x z

/-- Parametric form of pairwise coalition coherence. -/
def CompactCoherent (K : Set A) (J : Set B)
    (u : A → B → Bundle L → ℝ) : Prop :=
  ∀ ⦃a⦄, a ∈ K → ∀ ⦃a'⦄, a' ∈ K →
    ∃ b ∈ J, ∃ b' ∈ J, u a b = u a' b'

/-- The strengthened coherence conclusion.  It simultaneously handles the
weak and strict clauses of the paper's asymmetry definition and explicitly
uses attainment of the outer maximum. -/
theorem compactCMU_add_swap_nonpos
    {K : Set A} (hK : IsCompact K) (hneK : K.Nonempty)
    {J : Set B} (hJ : IsCompact J) (hneJ : J.Nonempty)
    {u : A → B → Bundle L → ℝ}
    (hucont : CompactPayoffContinuous u)
    (hcoh : CompactCoherent K J u)
    (x y : Bundle L) :
    compactCMU K J u x y + compactCMU K J u y x ≤ 0 := by
  obtain ⟨a, ha, haxy⟩ := compactCMU_attains hK hneK hJ hucont x y
  obtain ⟨a', ha', hayx⟩ := compactCMU_attains hK hneK hJ hucont y x
  obtain ⟨b, hb, b', hb', hab⟩ := hcoh ha ha'
  have h₁ := compactCoalitionScore_le hJ hneJ hucont a b hb x y
  have h₂ := compactCoalitionScore_le hJ hneJ hucont a' b' hb' y x
  rw [haxy, hayx]
  rw [← hab] at h₂
  linarith

theorem compactCMU_weakSignAsymmetric
    {K : Set A} (hK : IsCompact K) (hneK : K.Nonempty)
    {J : Set B} (hJ : IsCompact J) (hneJ : J.Nonempty)
    {u : A → B → Bundle L → ℝ}
    (hucont : CompactPayoffContinuous u)
    (hcoh : CompactCoherent K J u) :
    WeakSignAsymmetric (compactCMU K J u) := by
  intro x y hxy
  linarith [compactCMU_add_swap_nonpos hK hneK hJ hneJ hucont hcoh x y]

theorem compactCMU_signAsymmetric
    {K : Set A} (hK : IsCompact K) (hneK : K.Nonempty)
    {J : Set B} (hJ : IsCompact J) (hneJ : J.Nonempty)
    {u : A → B → Bundle L → ℝ}
    (hucont : CompactPayoffContinuous u)
    (hcoh : CompactCoherent K J u) :
    SignAsymmetric (compactCMU K J u) := by
  intro x y hxy
  linarith [compactCMU_add_swap_nonpos hK hneK hJ hneJ hucont hcoh x y]

end CompactCMU

end WGARP
