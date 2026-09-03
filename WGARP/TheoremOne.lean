import WGARP.FiniteConstruction
import WGARP.MatrixCMU

set_option autoImplicit false

/-!
# Theorem 1: the six-way WGARP characterization

The aliases below follow the statement order in the paper.  Each condition is
proved equivalent to WGARP, followed by the five adjacent equivalences that
constitute the displayed six-way theorem.
-/

namespace WGARP

variable {L : ℕ} {T : Type*}

/-- Theorem 1(i): a continuous, strictly increasing, asymmetric preference
function rationalizes the observations. -/
abbrev StatementI (D : Dataset L T) : Prop :=
  ∃ r : PreferenceFunction L,
    ContinuousPreference r ∧
    StrictlyIncreasingFirst r ∧
    Asymmetric r ∧
    PreferenceRationalizes D r

/-- Theorem 1(ii): the finite coherent-CMU normal form constructed in the
proof rationalizes the observations. -/
abbrev StatementII [Fintype T] [Nonempty T] (D : Dataset L T) : Prop :=
  HasFiniteCoherentCMURationalization D

/-- Theorem 1(iii): the symmetric-matrix/simplex CMU normal form, including
numerical skew symmetry and concavity of all component utilities. -/
abbrev StatementIII [Fintype T] [Nonempty T] (D : Dataset L T) : Prop :=
  HasMatrixCMURationalization D

/-- Theorem 1(iv): the weak generalized axiom of revealed preference. -/
abbrev StatementIV (D : Dataset L T) : Prop := WGARP D

/-- Theorem 1(v): feasibility of the pairwise Afriat inequalities. -/
abbrev StatementV (D : Dataset L T) : Prop := HasPairwiseAfriat D

/-- Theorem 1(vi): feasibility of the pairwise Varian sign inequalities. -/
abbrev StatementVI (D : Dataset L T) : Prop := HasPairwiseVarian D

/-- Statement (i) is equivalent to WGARP.  The sufficiency direction uses the
finite coherent-CMU witness, while necessity is the explicit budget-interior
argument. -/
theorem statementI_iff_wgarp [Fintype T] [Nonempty T] (D : Dataset L T) :
    StatementI D ↔ WGARP D := by
  constructor
  · rintro ⟨r, _hcontinuous, hincreasing, hasymmetric, hrationalizes⟩
    exact wgarp_of_asymmetric_strictlyIncreasing_rationalization
      D r hasymmetric hincreasing hrationalizes
  · intro h
    exact exists_statementOne_preference_of_finiteCoherentCMU D
      (hasFiniteCoherentCMURationalization_of_wgarp D h)

/-- Statement (ii) is equivalent to WGARP. -/
theorem statementII_iff_wgarp [Fintype T] [Nonempty T] (D : Dataset L T) :
    StatementII D ↔ WGARP D :=
  (wgarp_iff_hasFiniteCoherentCMURationalization D).symm

/-- Statement (iii) is equivalent to WGARP. -/
theorem statementIII_iff_wgarp [Fintype T] [Nonempty T] (D : Dataset L T) :
    StatementIII D ↔ WGARP D :=
  (wgarp_iff_hasMatrixCMURationalization D).symm

/-- Statement (iv) is WGARP itself. -/
theorem statementIV_iff_wgarp (D : Dataset L T) : StatementIV D ↔ WGARP D :=
  Iff.rfl

/-- Statement (v) is equivalent to WGARP. -/
theorem statementV_iff_wgarp (D : Dataset L T) : StatementV D ↔ WGARP D :=
  (wgarp_iff_pairwiseAfriat D).symm

/-- Statement (vi) is equivalent to WGARP. -/
theorem statementVI_iff_wgarp (D : Dataset L T) : StatementVI D ↔ WGARP D :=
  (wgarp_iff_pairwiseVarian D).symm

/--
Theorem 1 in paper order: all five adjacent pairs among the six statements are
equivalent.  Keeping the conjunction explicit makes every link directly
available to downstream formal developments.
-/
theorem theorem_one [Fintype T] [Nonempty T] (D : Dataset L T) :
    (StatementI D ↔ StatementII D) ∧
    (StatementII D ↔ StatementIII D) ∧
    (StatementIII D ↔ StatementIV D) ∧
    (StatementIV D ↔ StatementV D) ∧
    (StatementV D ↔ StatementVI D) := by
  have hI := statementI_iff_wgarp D
  have hII := statementII_iff_wgarp D
  have hIII := statementIII_iff_wgarp D
  have hIV := statementIV_iff_wgarp D
  have hV := statementV_iff_wgarp D
  have hVI := statementVI_iff_wgarp D
  exact ⟨hI.trans hII.symm,
    hII.trans hIII.symm,
    hIII.trans hIV.symm,
    hIV.trans hV.symm,
    hV.trans hVI.symm⟩

end WGARP
