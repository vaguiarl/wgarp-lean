import WGARP.TheoremOne

set_option autoImplicit false

/-!
# The one-observation case of Theorem 1

The manuscript's proof used reductions to `T ≥ 2` and `T ≥ 3`.  A nonempty
subsingleton observation type has exactly one observation, and this file checks
all six statements directly through the uniform diagonal construction.
-/

namespace WGARP

variable {L : ℕ} {T : Type*}

/-- Theorem 1(i) holds for a one-observation dataset. -/
theorem singleton_statementI [Subsingleton T] [Fintype T] [Nonempty T]
    (D : Dataset L T) : StatementI D :=
  (statementI_iff_wgarp D).mpr (wgarp_of_subsingleton D)

/-- Theorem 1(ii) holds for a one-observation dataset. -/
theorem singleton_statementII [Subsingleton T] [Fintype T] [Nonempty T]
    (D : Dataset L T) : StatementII D :=
  (statementII_iff_wgarp D).mpr (wgarp_of_subsingleton D)

/-- Theorem 1(iii) holds for a one-observation dataset. -/
theorem singleton_statementIII [Subsingleton T] [Fintype T] [Nonempty T]
    (D : Dataset L T) : StatementIII D :=
  (statementIII_iff_wgarp D).mpr (wgarp_of_subsingleton D)

/-- Theorem 1(iv) holds for a one-observation dataset. -/
theorem singleton_statementIV [Subsingleton T] [Fintype T] [Nonempty T]
    (D : Dataset L T) : StatementIV D :=
  wgarp_of_subsingleton D

/-- Theorem 1(v) holds for a one-observation dataset. -/
theorem singleton_statementV [Subsingleton T] [Fintype T] [Nonempty T]
    (D : Dataset L T) : StatementV D :=
  (statementV_iff_wgarp D).mpr (wgarp_of_subsingleton D)

/-- Theorem 1(vi) holds for a one-observation dataset. -/
theorem singleton_statementVI [Subsingleton T] [Fintype T] [Nonempty T]
    (D : Dataset L T) : StatementVI D :=
  (statementVI_iff_wgarp D).mpr (wgarp_of_subsingleton D)

/-- All six claims simultaneously for exactly one observation. -/
theorem singleton_all_statements [Subsingleton T] [Fintype T] [Nonempty T]
    (D : Dataset L T) :
    StatementI D ∧ StatementII D ∧ StatementIII D ∧
      StatementIV D ∧ StatementV D ∧ StatementVI D := by
  exact ⟨singleton_statementI D,
    singleton_statementII D,
    singleton_statementIII D,
    singleton_statementIV D,
    singleton_statementV D,
    singleton_statementVI D⟩

end WGARP
