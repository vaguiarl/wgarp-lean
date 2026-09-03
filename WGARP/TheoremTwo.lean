import WGARP.KAcyclicity
import WGARP.GlobalAfriat
import WGARP.FiniteCMU
import WGARP.Demand

set_option autoImplicit false

/-!
# Theorem 2: k-acyclicity and the Nakamura number

For a finite dataset and `k ≥ 2`, this file proves the equivalence between
the paper's exact `k`-acyclicity axiom and rationalization by a finite CMU
whose coalition system has Nakamura number at least `k + 1` and whose agents
are continuous and strictly increasing.

The construction indexes agents by all nonempty observation sets of size at
most `k`.  This slightly strengthens the manuscript's size-exact
construction and handles `card T ≤ k` without a separate case.  Its selected
Afriat agents are also concave, a property not assumed of an arbitrary witness
in the equivalence.
-/

namespace WGARP

universe u

variable {L : ℕ} {T : Type u}

/-- `NakamuraAtLeast Ω n` says that every family of fewer than `n`
coalitions has a common agent.  It also represents the paper's value
`ν(Ω) = ∞`: in that case this predicate holds for every `n`. -/
def NakamuraAtLeast {C I : Type*}
    (coalitions : FiniteCoalitionSystem C I) (n : ℕ) : Prop :=
  ∀ S : Finset C, S.card < n →
    ∃ i : I, ∀ c ∈ S, i ∈ coalitions.members c

/-- Pairwise coherence is exactly the lower bound `ν(Ω) ≥ 3`. -/
theorem nakamuraAtLeast_three_iff_coherent
    {C I : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) :
    NakamuraAtLeast coalitions 3 ↔ Coherent coalitions := by
  classical
  constructor
  · intro h c d
    obtain ⟨i, hi⟩ := h {c, d} (by
      have : ({c, d} : Finset C).card ≤ 2 := Finset.card_le_two
      omega)
    exact ⟨i, hi c (by simp), hi d (by simp)⟩
  · intro hcoherent S hcard
    have hle : S.card ≤ 2 := by omega
    by_cases hzero : S.card = 0
    · have hempty : S = ∅ := Finset.card_eq_zero.mp hzero
      let c : C := Classical.choice inferInstance
      obtain ⟨i, hi⟩ := coalitions.members_nonempty c
      exact ⟨i, by simp [hempty]⟩
    by_cases hone : S.card = 1
    · obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hone
      obtain ⟨i, hi⟩ := coalitions.members_nonempty c
      exact ⟨i, by simpa using hi⟩
    · have htwo : S.card = 2 := by omega
      obtain ⟨c, d, hne, rfl⟩ := Finset.card_eq_two.mp htwo
      obtain ⟨i, hic, hid⟩ := hcoherent c d
      exact ⟨i, by simp [hic, hid]⟩

/-- A bundled finite CMU rationalization with continuous, strictly increasing
components.  Bundling both finite index types
makes the existential in Theorem 2 genuinely range over arbitrary finite CMU
models rather than over the particular construction used for sufficiency. -/
structure FiniteCMURationalization (D : Dataset L T) where
  Agent : Type u
  Coalition : Type u
  agentFintype : Fintype Agent
  coalitionFintype : Fintype Coalition
  coalitionNonempty : Nonempty Coalition
  coalitions : FiniteCoalitionSystem Coalition Agent
  agents : Agent → Utility L
  agents_continuous : ∀ i, Continuous (agents i)
  agents_strictlyIncreasing : ComponentsStrictlyIncreasing agents
  rationalizes : @PreferenceRationalizes L T D
    (@finiteCMU Coalition Agent (Bundle L)
      coalitionFintype coalitionNonempty coalitions agents)

namespace FiniteCMURationalization

variable {D : Dataset L T}

/-- The preference function represented by a bundled model. -/
noncomputable def preference (M : FiniteCMURationalization D) : PreferenceFunction L := by
  letI := M.coalitionFintype
  letI := M.coalitionNonempty
  exact finiteCMU M.coalitions M.agents

theorem preference_eq (M : FiniteCMURationalization D) :
    M.preference = @finiteCMU M.Coalition M.Agent (Bundle L)
      M.coalitionFintype M.coalitionNonempty M.coalitions M.agents := rfl

theorem preference_rationalizes (M : FiniteCMURationalization D) :
    PreferenceRationalizes D M.preference := by
  simpa [preference_eq] using M.rationalizes

end FiniteCMURationalization

/-- Statement (i) of Theorem 2, with `n = k + 1`. -/
def HasFiniteCMURationalizationWithNakamura
    (D : Dataset L T) (n : ℕ) : Prop :=
  ∃ M : FiniteCMURationalization D, NakamuraAtLeast M.coalitions n

/-- Agent indices in the constructive direction: all nonempty observation
sets containing at most `k` observations. -/
def SmallObservationSet (T : Type*) [Fintype T] (k : ℕ) :=
  {S : Finset T // S.Nonempty ∧ S.card ≤ k}

instance [Fintype T] (k : ℕ) : Fintype (SmallObservationSet T k) :=
  inferInstanceAs (Fintype {S : Finset T // S.Nonempty ∧ S.card ≤ k})

theorem smallObservationSet_nonempty [Fintype T] [Nonempty T]
    {k : ℕ} (hk : 1 ≤ k) : Nonempty (SmallObservationSet T k) := by
  classical
  let t : T := Classical.choice inferInstance
  exact ⟨⟨{t}, by simp, by simpa using hk⟩⟩

/-- Select the regular Afriat utility rationalizing one small restriction. -/
noncomputable def smallSubsetUtility [Fintype T] [DecidableEq T]
    (D : Dataset L T) (k : ℕ) (hsmall : SmallRestrictionGARP D k)
    (S : SmallObservationSet T k) : Utility L := by
  letI : Nonempty {t // t ∈ S.1} := S.2.1.to_subtype
  exact Classical.choose
    (hasRegularUtilityRationalization_of_garp (D.restrict S.1)
      (hsmall S.1 S.2.1 S.2.2))

theorem smallSubsetUtility_spec [Fintype T] [DecidableEq T]
    (D : Dataset L T) (k : ℕ) (hsmall : SmallRestrictionGARP D k)
    (S : SmallObservationSet T k) :
    Continuous (smallSubsetUtility D k hsmall S) ∧
    ConcaveOn ℝ Set.univ (smallSubsetUtility D k hsmall S) ∧
    StrictlyIncreasing (smallSubsetUtility D k hsmall S) ∧
    UtilityRationalizes (D.restrict S.1) (smallSubsetUtility D k hsmall S) := by
  letI : Nonempty {t // t ∈ S.1} := S.2.1.to_subtype
  exact Classical.choose_spec
    (hasRegularUtilityRationalization_of_garp (D.restrict S.1)
      (hsmall S.1 S.2.1 S.2.2))

/-- The coalition attached to observation `t` contains exactly the small-set
agents whose restriction includes `t`. -/
noncomputable def smallSubsetCoalitions [Fintype T]
    (k : ℕ) (hk : 1 ≤ k) :
    FiniteCoalitionSystem T (SmallObservationSet T k) := by
  classical
  exact
    { members := fun t => Finset.univ.filter fun S => t ∈ S.1
      members_nonempty := fun t => by
        let S : SmallObservationSet T k := ⟨{t}, by simp, by simpa using hk⟩
        exact ⟨S, by simp [S]⟩ }

/-- Any family of at most `k` observation coalitions shares the agent indexed
by exactly that family of observations (and the empty family is vacuous). -/
theorem smallSubsetCoalitions_nakamura [Fintype T] [Nonempty T]
    (k : ℕ) (hk : 1 ≤ k) :
    NakamuraAtLeast (smallSubsetCoalitions (T := T) k hk) (k + 1) := by
  classical
  intro S hcard
  have hle : S.card ≤ k := by omega
  by_cases hS : S.Nonempty
  · let agent : SmallObservationSet T k := ⟨S, hS, hle⟩
    refine ⟨agent, ?_⟩
    intro t ht
    simp [smallSubsetCoalitions, agent, ht]
  · let t : T := Classical.choice inferInstance
    let agent : SmallObservationSet T k := ⟨{t}, by simp, by simpa using hk⟩
    refine ⟨agent, ?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp hS]

/-- The small-set utilities rationalize the CMU at every observation. -/
theorem smallSubsetFiniteCMU_rationalizes
    [Fintype T] [Nonempty T] [DecidableEq T]
    (D : Dataset L T) (k : ℕ) (hk : 1 ≤ k)
    (hsmall : SmallRestrictionGARP D k) :
    PreferenceRationalizes D
      (finiteCMU (smallSubsetCoalitions (T := T) k hk)
        (smallSubsetUtility D k hsmall)) := by
  classical
  intro t y hy
  let coalitions := smallSubsetCoalitions (T := T) k hk
  let agents := smallSubsetUtility D k hsmall
  have hscore : 0 ≤ coalitionScore coalitions agents t (D.choice t) y := by
    unfold coalitionScore
    apply Finset.le_inf'
    intro S hS
    have htS : t ∈ S.1 := by
      simpa [coalitions, smallSubsetCoalitions] using hS
    let tS : {s // s ∈ S.1} := ⟨t, htS⟩
    have hrat := (smallSubsetUtility_spec D k hsmall S).2.2.2
    have hy' : Affordable (D.restrict S.1) tS y := by
      exact ⟨hy.1, hy.2⟩
    have hu := hrat tS y hy'
    change 0 ≤ agents S (D.choice t) - agents S y
    exact sub_nonneg.mpr hu
  have houter :
      coalitionScore coalitions agents t (D.choice t) y ≤
        finiteCMU coalitions agents (D.choice t) y :=
    Finset.le_sup' (fun c => coalitionScore coalitions agents c (D.choice t) y)
      (Finset.mem_univ t)
  exact hscore.trans houter

/-- Construct the CMU witness from GARP on all small restrictions. -/
noncomputable def finiteCMURationalizationOfSmallGARP
    [Fintype T] [Nonempty T] [DecidableEq T]
    (D : Dataset L T) (k : ℕ) (hk : 1 ≤ k)
    (hsmall : SmallRestrictionGARP D k) : FiniteCMURationalization D where
  Agent := SmallObservationSet T k
  Coalition := T
  agentFintype := inferInstance
  coalitionFintype := inferInstance
  coalitionNonempty := inferInstance
  coalitions := smallSubsetCoalitions (T := T) k hk
  agents := smallSubsetUtility D k hsmall
  agents_continuous S := (smallSubsetUtility_spec D k hsmall S).1
  agents_strictlyIncreasing S := (smallSubsetUtility_spec D k hsmall S).2.2.1
  rationalizes := smallSubsetFiniteCMU_rationalizes D k hk hsmall

/-- Constructive sufficiency half of Theorem 2. -/
theorem hasFiniteCMURationalizationWithNakamura_of_kAcyclic
    [Fintype T] [Nonempty T]
    (D : Dataset L T) {k : ℕ} (hk : 2 ≤ k) (hacyclic : KAcyclic D k) :
    HasFiniteCMURationalizationWithNakamura D (k + 1) := by
  classical
  let hsmall := (kAcyclic_iff_smallRestrictionGARP D k).mp hacyclic
  refine ⟨finiteCMURationalizationOfSmallGARP D k (by omega) hsmall, ?_⟩
  exact smallSubsetCoalitions_nakamura (T := T) k (by omega)

/-! ## Necessity: common agents rule out a `k`-cycle -/

/-- The directly revealed bundle at the right endpoint is affordable at the
left endpoint's observation. -/
theorem affordable_choice_of_directRevealed
    (D : Dataset L T) {s t : T} (hst : DirectRevealed D s t) :
    Affordable D s (D.choice t) := by
  refine ⟨D.choice_nonneg t, ?_⟩
  rw [DirectRevealed, expenditureGap_eq] at hst
  linarith

/-- Rationalization makes the CMU weakly positive along every direct weak
revealed-preference edge. -/
theorem finiteCMU_nonneg_of_directRevealed
    {C I : Type*} [Fintype C] [Nonempty C]
    (D : Dataset L T) (coalitions : FiniteCoalitionSystem C I)
    (u : I → Utility L)
    (hrat : PreferenceRationalizes D (finiteCMU coalitions u))
    {s t : T} (hst : DirectRevealed D s t) :
    0 ≤ finiteCMU coalitions u (D.choice s) (D.choice t) :=
  hrat s (D.choice t) (affordable_choice_of_directRevealed D hst)

/-- Strict affordability makes a CMU with strictly increasing components
strictly positive.  This is the numerical budget-interior claim used in the
paper's necessity proof. -/
theorem finiteCMU_pos_of_strictDirectRevealed
    {C I : Type*} [Fintype C] [Nonempty C]
    (D : Dataset L T) (coalitions : FiniteCoalitionSystem C I)
    (u : I → Utility L) (hinc : ComponentsStrictlyIncreasing u)
    (hrat : PreferenceRationalizes D (finiteCMU coalitions u))
    {s t : T} (hst : StrictDirectRevealed D s t) :
    0 < finiteCMU coalitions u (D.choice s) (D.choice t) := by
  let r : PreferenceFunction L := finiteCMU coalitions u
  have hx : PreferenceDemand r (D.price s)
      (expenditure D s (D.choice s)) (D.choice s) := by
    refine ⟨⟨D.choice_nonneg s, le_rfl⟩, ?_⟩
    intro y hy
    exact hrat s y hy
  have hcheap : dot (D.price s) (D.choice t) <
      expenditure D s (D.choice s) := by
    rw [StrictDirectRevealed, expenditureGap_eq] at hst
    exact sub_pos.mp hst
  exact preferenceDemand_pos_of_strictlyAffordable
    r (D.price s) (expenditure D s (D.choice s))
    (D.choice s) (D.choice t) (D.price_pos s)
    (lt_of_lt_of_le (by decide : 0 < 2) D.goods_two_le)
    (finiteCMU_strictlyDecreasingSecond coalitions u hinc)
    hx (D.choice_nonneg t) hcheap

/-- A coalition attaining the outer maximum. -/
noncomputable def maximizingCoalition
    {C I X : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (x y : X) : C :=
  Classical.choose (Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun c => coalitionScore coalitions u c x y))

theorem maximizingCoalition_mem_univ
    {C I X : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (x y : X) : maximizingCoalition coalitions u x y ∈ (Finset.univ : Finset C) :=
  (Classical.choose_spec (Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun c => coalitionScore coalitions u c x y))).1

theorem maximizingCoalition_score_eq
    {C I X : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (x y : X) :
    coalitionScore coalitions u (maximizingCoalition coalitions u x y) x y =
      finiteCMU coalitions u x y := by
  symm
  simpa [finiteCMU, maximizingCoalition] using
    (Classical.choose_spec (Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun c => coalitionScore coalitions u c x y))).2

/-- Every member of an attaining coalition weakly bounds the CMU value by
its own utility difference. -/
theorem finiteCMU_le_difference_of_mem_maximizingCoalition
    {C I X : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (x y : X) {i : I}
    (hi : i ∈ coalitions.members (maximizingCoalition coalitions u x y)) :
    finiteCMU coalitions u x y ≤ u i x - u i y := by
  rw [← maximizingCoalition_score_eq coalitions u x y]
  exact Finset.inf'_le (fun j => u j x - u j y) hi

/-- Attaining coalitions for all consecutive edges of a chain. -/
noncomputable def chainCoalitions
    {C I X A : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (q : A → X) : List A → List C
  | a :: b :: rest =>
      maximizingCoalition coalitions u (q a) (q b) ::
        chainCoalitions coalitions u q (b :: rest)
  | _ => []

theorem length_chainCoalitions
    {C I X A : Type*} [Fintype C] [Nonempty C]
    (coalitions : FiniteCoalitionSystem C I) (u : I → X → ℝ)
    (q : A → X) (l : List A) :
    (chainCoalitions coalitions u q l).length = l.length - 1 := by
  induction l with
  | nil => simp [chainCoalitions]
  | cons a l ih =>
      cases l with
      | nil => simp [chainCoalitions]
      | cons b rest => simp [chainCoalitions, ih]

/-- A common member of all edge-maximizing coalitions supplies one ordinary
utility ranking the full chain weakly downward. -/
theorem utility_isChain_of_mem_chainCoalitions
    {C I : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (D : Dataset L T) (coalitions : FiniteCoalitionSystem C I)
    (u : I → Utility L)
    (hrat : PreferenceRationalizes D (finiteCMU coalitions u))
    (i : I) (l : List T)
    (hchain : l.IsChain (DirectRevealed D))
    (hi : ∀ c ∈ (chainCoalitions coalitions u D.choice l).toFinset,
      i ∈ coalitions.members c) :
    l.IsChain (fun s t => u i (D.choice t) ≤ u i (D.choice s)) := by
  revert hi
  induction l with
  | nil => intro _hi; exact .nil
  | cons a l ihl =>
      cases l with
      | nil => intro _hi; exact .singleton _
      | cons b rest =>
          intro hi
          rw [List.isChain_cons_cons] at hchain ⊢
          constructor
          · let c := maximizingCoalition coalitions u (D.choice a) (D.choice b)
            have hic : i ∈ coalitions.members c := by
              apply hi c
              simp [chainCoalitions, c]
            have hcmu : 0 ≤ finiteCMU coalitions u (D.choice a) (D.choice b) :=
              finiteCMU_nonneg_of_directRevealed D coalitions u hrat hchain.1
            have hbound := finiteCMU_le_difference_of_mem_maximizingCoalition
              coalitions u (D.choice a) (D.choice b) hic
            linarith
          · apply ihl hchain.2
            intro c hc
            apply hi c
            simp only [chainCoalitions, List.toFinset_cons, Finset.mem_insert]
            exact Or.inr hc

/-- A weak utility chain orders its last value below its first value. -/
theorem utility_last_le_head_of_isChain
    {I : Type*} (u : I → Utility L) (i : I) (q : T → Bundle L)
    {l : List T} (hne : l ≠ [])
    (hchain : l.IsChain (fun s t => u i (q t) ≤ u i (q s))) :
    u i (q (l.getLast hne)) ≤ u i (q (l.head hne)) := by
  have hreach := List.relationReflTransGen_of_exists_isChain l hchain hne
  refine Relation.ReflTransGen.head_induction_on hreach ?_ ?_
  · exact le_rfl
  · intro a b hab _hbc ih
    exact ih.trans hab

/-- Necessity half of Theorem 2. -/
theorem kAcyclic_of_hasFiniteCMURationalizationWithNakamura
    [Fintype T] [Nonempty T]
    (D : Dataset L T) {k : ℕ} (_hk : 2 ≤ k)
    (hmodel : HasFiniteCMURationalizationWithNakamura D (k + 1)) :
    KAcyclic D k := by
  classical
  rcases hmodel with ⟨M, hnakamura⟩
  letI : Fintype M.Agent := M.agentFintype
  letI : Fintype M.Coalition := M.coalitionFintype
  letI : Nonempty M.Coalition := M.coalitionNonempty
  intro hcycle
  rcases hcycle with ⟨l, hlen, hne, hchain, hstrict⟩
  let closeCoalition := maximizingCoalition M.coalitions M.agents
    (D.choice (l.getLast hne)) (D.choice (l.head hne))
  let selected : List M.Coalition :=
    chainCoalitions M.coalitions M.agents D.choice l ++ [closeCoalition]
  have hselectedLength : selected.length = k := by
    dsimp [selected]
    rw [List.length_append, length_chainCoalitions]
    simp only [List.length_singleton]
    omega
  have hselectedCard : selected.toFinset.card < k + 1 := by
    calc
      selected.toFinset.card ≤ selected.length := selected.toFinset_card_le
      _ = k := hselectedLength
      _ < k + 1 := Nat.lt_succ_self k
  obtain ⟨i, hi⟩ := hnakamura selected.toFinset hselectedCard
  have hichain :
      ∀ c ∈ (chainCoalitions M.coalitions M.agents D.choice l).toFinset,
        i ∈ M.coalitions.members c := by
    intro c hc
    apply hi c
    simp [selected, hc]
  have hutilityChain := utility_isChain_of_mem_chainCoalitions
    D M.coalitions M.agents M.rationalizes i l hchain hichain
  have hweak := utility_last_le_head_of_isChain M.agents i D.choice hne hutilityChain
  have hiclose : i ∈ M.coalitions.members closeCoalition := by
    apply hi closeCoalition
    simp [selected]
  have hcmu : 0 < finiteCMU M.coalitions M.agents
      (D.choice (l.getLast hne)) (D.choice (l.head hne)) :=
    finiteCMU_pos_of_strictDirectRevealed D M.coalitions M.agents
      M.agents_strictlyIncreasing M.rationalizes hstrict
  have hbound := finiteCMU_le_difference_of_mem_maximizingCoalition
    M.coalitions M.agents (D.choice (l.getLast hne))
      (D.choice (l.head hne)) hiclose
  linarith

/-! ## The equivalence and its `k = 2` regression -/

/-- Theorem 2, in paper order. -/
theorem theorem_two [Fintype T] [Nonempty T]
    (D : Dataset L T) (k : ℕ) (hk : 2 ≤ k) :
    HasFiniteCMURationalizationWithNakamura D (k + 1) ↔ KAcyclic D k := by
  classical
  exact ⟨kAcyclic_of_hasFiniteCMURationalizationWithNakamura D hk,
    hasFiniteCMURationalizationWithNakamura_of_kAcyclic D hk⟩

/-- The paper's regression: `2`-acyclicity is exactly WGARP. -/
theorem kAcyclic_two_iff_wgarp (D : Dataset L T) :
    KAcyclic D 2 ↔ WGARP D := by
  constructor
  · intro hacyclic s t hts
    apply le_of_not_gt
    intro hst
    apply hacyclic
    refine ⟨[t, s], by simp, by simp, ?_, ?_⟩
    · simpa [DirectRevealed] using hts
    · simpa [StrictDirectRevealed] using hst
  · intro hwgarp hcycle
    rcases hcycle with ⟨l, hlen, hne, hchain, hstrict⟩
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
    have hab : DirectRevealed D a b := by simpa using hchain
    have hba : StrictDirectRevealed D b a := by simpa using hstrict
    exact (not_lt_of_ge (hwgarp b a hab)) hba

/-- At `k = 2`, Theorem 2 specializes to the coherent-CMU/WGARP result:
the Nakamura threshold is `3`, which is precisely pairwise coherence. -/
theorem theorem_two_at_two [Fintype T] [Nonempty T]
    (D : Dataset L T) :
    HasFiniteCMURationalizationWithNakamura D 3 ↔ WGARP D := by
  exact (theorem_two D 2 (by omega)).trans (kAcyclic_two_iff_wgarp D)

end WGARP
