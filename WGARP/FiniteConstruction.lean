import WGARP.Afriat
import WGARP.FiniteCMU
import WGARP.Necessity

set_option autoImplicit false

/-!
# The finite coherent-CMU construction

This file packages the finite proof of the WGARP rationalization direction of
Theorem 1.  Component utilities are indexed by ordered observation pairs.  The
coalition for observation `s` contains every pair having `s` as either
endpoint.  Consequently coalitions `s` and `t` share the literal agent
`(s,t)`, which makes coherence valid on the diagonal and when there is only one
observation as well.
-/

namespace WGARP

variable {L : ℕ} {T : Type*}

/-- The row/column coalition associated with each observation. -/
noncomputable def rowCoalitions [Fintype T] (_D : Dataset L T) :
    FiniteCoalitionSystem T (T × T) := by
  classical
  exact
    { members := fun s => Finset.univ.filter fun ij => ij.1 = s ∨ ij.2 = s
      members_nonempty := fun s => ⟨(s, s), by simp⟩ }

/-- Any two row/column coalitions share the pair joining their indices. -/
theorem rowCoalitions_coherent [Fintype T] (D : Dataset L T) :
    Coherent (rowCoalitions D) := by
  classical
  intro s t
  exact ⟨(s, t), by simp [rowCoalitions], by simp [rowCoalitions]⟩

/-- Pointwise concavity of every component utility. -/
def ComponentsConcave {I : Type*} (u : I → Utility L) : Prop :=
  ∀ i, ConcaveOn ℝ Set.univ (u i)

/--
Existence of a finite coherent CMU rationalization with the fixed observation
and ordered-pair index types used by the constructive proof.
-/
def HasFiniteCoherentCMURationalization [Fintype T] [Nonempty T]
    (D : Dataset L T) : Prop :=
  ∃ (coalitions : FiniteCoalitionSystem T (T × T))
      (agents : (T × T) → Utility L),
    Coherent coalitions ∧
    (∀ i, Continuous (agents i)) ∧
    ComponentsStrictlyIncreasing agents ∧
    ComponentsConcave agents ∧
    PreferenceRationalizes D (finiteCMU coalitions agents)

variable {D : Dataset L T}

/-- The component at the ordered pair `(s,t)` is the symmetric pair utility. -/
noncomputable def pairAgents (certificate : PairwiseAfriat D) :
    (T × T) → Utility L :=
  fun ij => pairUtility certificate ij.1 ij.2

/-- The component matrix is symmetric, as required in the paper's proof. -/
theorem pairAgents_symmetric (certificate : PairwiseAfriat D) (s t : T) :
    pairAgents certificate (s, t) = pairAgents certificate (t, s) :=
  pairUtility_symm certificate s t

theorem pairAgents_continuous (certificate : PairwiseAfriat D) :
    ∀ i, Continuous (pairAgents certificate i) := by
  rintro ⟨s, t⟩
  exact pairUtility_continuous certificate s t

theorem pairAgents_strictlyIncreasing (certificate : PairwiseAfriat D) :
    ComponentsStrictlyIncreasing (pairAgents certificate) := by
  rintro ⟨s, t⟩
  exact pairUtility_strictlyIncreasing certificate s t

theorem pairAgents_concave (certificate : PairwiseAfriat D) :
    ComponentsConcave (pairAgents certificate) := by
  rintro ⟨s, t⟩
  exact pairUtility_concaveOn certificate s t

/--
The row-coalition CMU rationalizes every observed choice.  At observation
`s`, each member of coalition `s` is a pair utility having `s` as one of its
two endpoints, so all its component differences are nonnegative.
-/
theorem rowFiniteCMU_rationalizes [Fintype T] [Nonempty T]
    (D : Dataset L T) (certificate : PairwiseAfriat D) :
    PreferenceRationalizes D
      (finiteCMU (rowCoalitions D) (pairAgents certificate)) := by
  classical
  intro s y hy
  have hscore :
      0 ≤ coalitionScore (rowCoalitions D) (pairAgents certificate) s
        (D.choice s) y := by
    unfold coalitionScore
    apply Finset.le_inf'
    intro ij hij
    rcases ij with ⟨a, b⟩
    simp only [rowCoalitions, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    change 0 ≤ pairUtility certificate a b (D.choice s) -
      pairUtility certificate a b y
    rcases hij with has | hbs
    · subst a
      exact sub_nonneg.mpr (pairUtility_rationalizes_first certificate s b hy)
    · subst b
      exact sub_nonneg.mpr (pairUtility_rationalizes_second certificate a s hy)
  have houter :
      coalitionScore (rowCoalitions D) (pairAgents certificate) s
          (D.choice s) y ≤
        finiteCMU (rowCoalitions D) (pairAgents certificate) (D.choice s) y :=
    Finset.le_sup' (fun c =>
      coalitionScore (rowCoalitions D) (pairAgents certificate) c
        (D.choice s) y) (Finset.mem_univ s)
  exact hscore.trans houter

/-- WGARP constructively yields the finite coherent CMU in Theorem 1(ii). -/
theorem hasFiniteCoherentCMURationalization_of_wgarp
    [Fintype T] [Nonempty T] (D : Dataset L T) (h : WGARP D) :
    HasFiniteCoherentCMURationalization D := by
  let certificate : PairwiseAfriat D := pairwiseAfriatOfWGARP D h
  exact ⟨rowCoalitions D, pairAgents certificate,
    rowCoalitions_coherent D,
    pairAgents_continuous certificate,
    pairAgents_strictlyIncreasing certificate,
    pairAgents_concave certificate,
    rowFiniteCMU_rationalizes D certificate⟩

/--
Every witness to the finite coherent-CMU statement supplies a jointly
continuous, strictly increasing, asymmetric rationalizing preference
function—the properties in statement (i) of Theorem 1.
-/
theorem exists_statementOne_preference_of_finiteCoherentCMU
    [Fintype T] [Nonempty T] (D : Dataset L T)
    (h : HasFiniteCoherentCMURationalization D) :
    ∃ r : PreferenceFunction L,
      ContinuousPreference r ∧
      StrictlyIncreasingFirst r ∧
      Asymmetric r ∧
      PreferenceRationalizes D r := by
  rcases h with ⟨coalitions, agents, hcoherent, hcontinuous, hincreasing,
    _hconcave, hrationalizes⟩
  refine ⟨finiteCMU coalitions agents, ?_, ?_, ?_, hrationalizes⟩
  · exact finiteCMU_continuous coalitions agents hcontinuous
  · exact finiteCMU_strictlyIncreasingFirst coalitions agents hincreasing
  · exact ⟨
      fun _x _y hxy =>
        finiteCMU_weakSignAsymmetry coalitions agents hcoherent hxy,
      fun _x _y hxy =>
        finiteCMU_signAsymmetry coalitions agents hcoherent hxy⟩

/-- Any finite coherent-CMU rationalization satisfying the retained hypotheses
obeys WGARP, by the paper's necessity lemma. -/
theorem wgarp_of_finiteCoherentCMURationalization
    [Fintype T] [Nonempty T] (D : Dataset L T)
    (h : HasFiniteCoherentCMURationalization D) : WGARP D := by
  obtain ⟨r, _hcontinuous, hincreasing, hasymmetric, hrationalizes⟩ :=
    exists_statementOne_preference_of_finiteCoherentCMU D h
  exact wgarp_of_asymmetric_strictlyIncreasing_rationalization
    D r hasymmetric hincreasing hrationalizes

/-- Finite coherent-CMU rationalizability is equivalent to WGARP. -/
theorem wgarp_iff_hasFiniteCoherentCMURationalization
    [Fintype T] [Nonempty T] (D : Dataset L T) :
    WGARP D ↔ HasFiniteCoherentCMURationalization D := by
  exact ⟨hasFiniteCoherentCMURationalization_of_wgarp D,
    wgarp_of_finiteCoherentCMURationalization D⟩

end WGARP
