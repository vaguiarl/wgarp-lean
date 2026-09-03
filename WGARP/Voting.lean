import WGARP.FiniteCMU

set_option autoImplicit false

/-!
# Supermajority coalition systems

This file formalizes the voting example in the retained main text.  Given a
finite type of agents and a threshold `m`, the admissible coalitions are all
finite sets containing at least `m` agents.  A strict-majority threshold makes
this coalition system coherent, and the sign of its finite CMU has the stated
voting interpretation: a bundle is weakly preferred exactly when some
qualifying coalition unanimously weakly prefers it.
-/

namespace WGARP

/-- A qualifying coalition at threshold `m` is a finite set with at least
`m` members. -/
def ThresholdCoalition (I : Type*) (m : ℕ) :=
  {S : Finset I // m ≤ S.card}

namespace ThresholdCoalition

variable {I : Type*} {m : ℕ}

/-- The underlying finite set of agents in a qualifying coalition. -/
def members (c : ThresholdCoalition I m) : Finset I := c.1

@[simp]
theorem card_members_le (c : ThresholdCoalition I m) :
    m ≤ c.members.card :=
  c.2

end ThresholdCoalition

/-- There are finitely many threshold coalitions over a finite agent type. -/
noncomputable instance thresholdCoalitionFintype
    {I : Type*} [Fintype I] (m : ℕ) :
    Fintype (ThresholdCoalition I m) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun S : Finset I ↦ m ≤ S.card) (by simp)

/-- If the threshold does not exceed the number of agents, the grand
coalition is a qualifying coalition. -/
theorem thresholdCoalition_nonempty
    {I : Type*} [Fintype I] {m : ℕ}
    (hm : m ≤ Fintype.card I) :
    Nonempty (ThresholdCoalition I m) := by
  classical
  exact ⟨⟨Finset.univ, by simpa using hm⟩⟩

/-- All coalitions containing at least `m > 0` agents, regarded as a finite
coalition system in the sense used by the CMU construction. -/
noncomputable def thresholdCoalitions
    (I : Type*) [Fintype I] (m : ℕ) (hm : 0 < m) :
    FiniteCoalitionSystem (ThresholdCoalition I m) I := by
  classical
  exact
    { members := fun c ↦ c.members
      members_nonempty := fun c ↦
        Finset.card_pos.mp (hm.trans_le c.card_members_le) }

@[simp]
theorem thresholdCoalitions_members
    {I : Type*} [Fintype I] {m : ℕ} (hm : 0 < m)
    (c : ThresholdCoalition I m) :
    (thresholdCoalitions I m hm).members c = c.members :=
  rfl

/-- Two coalitions whose common threshold is strictly greater than half the
number of agents must intersect.  Thus every strict-supermajority coalition
system is coherent. -/
theorem thresholdCoalitions_coherent
    {I : Type*} [Fintype I] {m : ℕ} (hm : 0 < m)
    (hmajority : Fintype.card I < 2 * m) :
    Coherent (thresholdCoalitions I m hm) := by
  classical
  intro c d
  have hintersect : ¬ Disjoint c.members d.members := by
    intro hdisjoint
    have hunion :
        (c.members ∪ d.members).card ≤ Fintype.card I :=
      Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisjoint] at hunion
    have hc : m ≤ c.members.card := c.card_members_le
    have hd : m ≤ d.members.card := d.card_members_le
    omega
  obtain ⟨i, hic, hid⟩ := Finset.not_disjoint_iff.mp hintersect
  exact ⟨i, hic, hid⟩

/-- The sign of a coalition's minimum score is nonnegative exactly when every
member of that coalition weakly prefers `x` to `y`. -/
theorem coalitionScore_nonneg_iff_unanimous
    {C I X : Type*} (coalitions : FiniteCoalitionSystem C I)
    (u : I → X → ℝ) (c : C) (x y : X) :
    0 ≤ coalitionScore coalitions u c x y ↔
      ∀ i ∈ coalitions.members c, u i y ≤ u i x := by
  unfold coalitionScore
  rw [Finset.le_inf'_iff]
  simp only [sub_nonneg]

/-- A finite CMU is nonnegative exactly when one of its coalitions unanimously
weakly prefers `x` to `y`. -/
theorem finiteCMU_nonneg_iff_exists_unanimous
    {C I X : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I)
    (u : I → X → ℝ) (x y : X) :
    0 ≤ finiteCMU coalitions u x y ↔
      ∃ c, ∀ i ∈ coalitions.members c, u i y ≤ u i x := by
  unfold finiteCMU
  rw [Finset.le_sup'_iff]
  simp only [Finset.mem_univ, true_and]
  apply exists_congr
  intro c
  exact coalitionScore_nonneg_iff_unanimous coalitions u c x y

/-- The CMU induced by all threshold-qualifying coalitions.  The bound
`m ≤ |I|` ensures that the grand coalition qualifies, so the outer finite
maximum is over a nonempty family. -/
noncomputable def thresholdFiniteCMU
    {I X : Type*} [Fintype I] (m : ℕ)
    (hm : 0 < m) (hmI : m ≤ Fintype.card I)
    (u : I → X → ℝ) : X → X → ℝ := by
  letI : Nonempty (ThresholdCoalition I m) :=
    thresholdCoalition_nonempty hmI
  exact finiteCMU (thresholdCoalitions I m hm) u

/-- Majority-rule interpretation of the threshold CMU: its value at `(x,y)`
is nonnegative iff at least `m` agents unanimously rank `x` weakly above `y`.

The upper-bound hypothesis supplies a qualifying grand coalition, as required
by the finite maximum in `finiteCMU`. -/
theorem thresholdFiniteCMU_nonneg_iff_majority
    {I X : Type*} [Fintype I] {m : ℕ}
    (hm : 0 < m) (hmI : m ≤ Fintype.card I)
    (u : I → X → ℝ) (x y : X) :
    0 ≤ thresholdFiniteCMU m hm hmI u x y ↔
      ∃ S : Finset I, m ≤ S.card ∧ ∀ i ∈ S, u i y ≤ u i x := by
  letI : Nonempty (ThresholdCoalition I m) :=
    thresholdCoalition_nonempty hmI
  unfold thresholdFiniteCMU
  rw [finiteCMU_nonneg_iff_exists_unanimous]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.members, c.card_members_le, hc⟩
  · rintro ⟨S, hcard, hS⟩
    exact ⟨⟨S, hcard⟩, hS⟩

/-- Under a strict-majority threshold, the associated finite CMU is
asymmetric in the paper's two sign senses. -/
theorem thresholdFiniteCMU_asymmetric
    {I : Type*} [Fintype I] {L m : ℕ}
    (hm : 0 < m) (hmI : m ≤ Fintype.card I)
    (hmajority : Fintype.card I < 2 * m)
    (u : I → Bundle L → ℝ) :
    Asymmetric (thresholdFiniteCMU m hm hmI u) := by
  letI : Nonempty (ThresholdCoalition I m) :=
    thresholdCoalition_nonempty hmI
  have hcoherent : Coherent (thresholdCoalitions I m hm) :=
    thresholdCoalitions_coherent hm hmajority
  unfold thresholdFiniteCMU
  exact ⟨
    fun _x _y hxy ↦
      finiteCMU_weakSignAsymmetry (thresholdCoalitions I m hm) u hcoherent hxy,
    fun _x _y hxy ↦
      finiteCMU_signAsymmetry (thresholdCoalitions I m hm) u hcoherent hxy⟩

end WGARP
