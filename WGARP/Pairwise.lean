import WGARP.Data

/-!
# Pairwise Afriat and Varian certificates

This file formalizes statements (iv)--(vi) of Theorem 1 and proves their
equivalence constructively.  In particular, the implication from WGARP to the
pairwise Afriat inequalities does not appeal to the classical Afriat theorem.
The witnesses below work on the diagonal as well, so a one-observation dataset
requires no exceptional argument.
-/

namespace WGARP

variable {L : ℕ} {T : Type*} (D : Dataset L T)

/--
Statement (v) of Theorem 1.  `multiplier s t` represents
`λˢ_{s,t}`: its first argument is the observation whose price occurs in the
inequality and its second is the opposing observation.  Thus the paper's
redundant lower-index symmetry is built into this two-index representation.
-/
structure PairwiseAfriat where
  R : T → T → ℝ
  multiplier : T → T → ℝ
  R_skew : ∀ s t, R s t = -R t s
  multiplier_pos : ∀ s t, 0 < multiplier s t
  inequality : ∀ s t, multiplier s t * expenditureGap D s t ≤ R s t

/-- Statement (vi) of Theorem 1. -/
structure PairwiseVarian where
  V : T → T → ℝ
  V_skew : ∀ s t, V s t = -V t s
  weak_sign : ∀ s t, 0 ≤ expenditureGap D s t → 0 ≤ V s t
  strict_sign : ∀ s t, 0 < expenditureGap D s t → 0 < V s t

/-- Existence of a certificate satisfying the pairwise Afriat inequalities. -/
abbrev HasPairwiseAfriat : Prop := Nonempty (PairwiseAfriat D)

/-- Existence of a certificate satisfying the pairwise Varian inequalities. -/
abbrev HasPairwiseVarian : Prop := Nonempty (PairwiseVarian D)

namespace PairwiseAfriat

variable {D}

/-- Skew symmetry forces the diagonal Afriat value to be zero. -/
@[simp]
theorem R_self (certificate : PairwiseAfriat D) (s : T) : certificate.R s s = 0 := by
  have h := certificate.R_skew s s
  linarith

/-- A pairwise Afriat certificate immediately gives a Varian certificate. -/
def toVarian (certificate : PairwiseAfriat D) : PairwiseVarian D where
  V := certificate.R
  V_skew := certificate.R_skew
  weak_sign s t hgap := by
    have hproduct : 0 ≤ certificate.multiplier s t * expenditureGap D s t :=
      mul_nonneg (le_of_lt (certificate.multiplier_pos s t)) hgap
    exact hproduct.trans (certificate.inequality s t)
  strict_sign s t hgap := by
    have hproduct : 0 < certificate.multiplier s t * expenditureGap D s t :=
      mul_pos (certificate.multiplier_pos s t) hgap
    exact hproduct.trans_le (certificate.inequality s t)

end PairwiseAfriat

namespace PairwiseVarian

variable {D}

/-- Skew symmetry forces the diagonal Varian value to be zero. -/
@[simp]
theorem V_self (certificate : PairwiseVarian D) (s : T) : certificate.V s s = 0 := by
  have h := certificate.V_skew s s
  linarith

/-- The Varian sign inequalities rule out exactly the WGARP binary cycle. -/
theorem wgarp (certificate : PairwiseVarian D) : WGARP D := by
  intro s t hts
  by_contra hst
  have hst' : 0 < expenditureGap D s t := lt_of_not_ge hst
  have hvts : 0 ≤ certificate.V t s := certificate.weak_sign t s hts
  have hvst : 0 < certificate.V s t := certificate.strict_sign s t hst'
  rw [certificate.V_skew s t] at hvst
  linarith

end PairwiseVarian

/--
Positive scale used in the direct WGARP-to-Afriat construction.  Its asymmetric
first branch balances a positive expenditure gap against the necessarily
negative reverse gap.
-/
private noncomputable def pairwiseScale (a b : ℝ) : ℝ :=
  if 0 < a then -b else if 0 < b then b else 1

private theorem pairwiseScale_pos
    {a b : ℝ} (hab : 0 ≤ b → a ≤ 0) : 0 < pairwiseScale a b := by
  by_cases ha : 0 < a
  · have hb : b < 0 := by
      by_contra hbn
      exact (not_lt_of_ge (hab (le_of_not_gt hbn))) ha
    simp [pairwiseScale, ha, hb]
  · by_cases hb : 0 < b
    · simp [pairwiseScale, ha, hb]
    · simp [pairwiseScale, ha, hb]

private theorem pairwiseScale_weighted_sum_nonpos
    {a b : ℝ} (hab : 0 ≤ b → a ≤ 0) :
    pairwiseScale a b * a + pairwiseScale b a * b ≤ 0 := by
  by_cases ha : 0 < a
  · have hb : ¬0 < b := by
      intro hb
      exact (not_lt_of_ge (hab (le_of_lt hb))) ha
    simp [pairwiseScale, ha, hb]
    ring_nf
    exact le_refl _
  · by_cases hb : 0 < b
    · simp [pairwiseScale, ha, hb]
      ring_nf
      exact le_refl _
    · have ha' : a ≤ 0 := le_of_not_gt ha
      have hb' : b ≤ 0 := le_of_not_gt hb
      simp [pairwiseScale, ha, hb]
      linarith

/--
Construct the pairwise Afriat numbers directly from WGARP.  For each unordered
pair, the two positive scales make the weighted expenditure gaps sum to a
nonpositive number; their antisymmetric midpoint is the required `R` value.
-/
noncomputable def pairwiseAfriatOfWGARP (h : WGARP D) : PairwiseAfriat D where
  R s t :=
    (pairwiseScale (expenditureGap D s t) (expenditureGap D t s) *
        expenditureGap D s t -
      pairwiseScale (expenditureGap D t s) (expenditureGap D s t) *
        expenditureGap D t s) / 2
  multiplier s t := pairwiseScale (expenditureGap D s t) (expenditureGap D t s)
  R_skew s t := by
    ring
  multiplier_pos s t := pairwiseScale_pos (h s t)
  inequality s t := by
    have hsum :
        pairwiseScale (expenditureGap D s t) (expenditureGap D t s) *
            expenditureGap D s t +
          pairwiseScale (expenditureGap D t s) (expenditureGap D s t) *
            expenditureGap D t s ≤ 0 :=
      pairwiseScale_weighted_sum_nonpos (h s t)
    linarith

/-- WGARP is equivalent to feasibility of the pairwise Afriat inequalities. -/
theorem wgarp_iff_pairwiseAfriat : WGARP D ↔ HasPairwiseAfriat D := by
  constructor
  · exact fun h => ⟨pairwiseAfriatOfWGARP D h⟩
  · rintro ⟨certificate⟩
    exact certificate.toVarian.wgarp

/-- WGARP is equivalent to feasibility of the pairwise Varian inequalities. -/
theorem wgarp_iff_pairwiseVarian : WGARP D ↔ HasPairwiseVarian D := by
  constructor
  · intro h
    exact ⟨(pairwiseAfriatOfWGARP D h).toVarian⟩
  · rintro ⟨certificate⟩
    exact certificate.wgarp

/-- Any dataset with at most one observation satisfies WGARP. -/
theorem wgarp_of_subsingleton [Subsingleton T] : WGARP D := by
  intro s t
  have hst : s = t := Subsingleton.elim s t
  subst t
  simp

/-- The diagonal and hence the `T = 1` case have an Afriat certificate. -/
theorem hasPairwiseAfriat_of_subsingleton [Subsingleton T] : HasPairwiseAfriat D :=
  (wgarp_iff_pairwiseAfriat D).mp (wgarp_of_subsingleton D)

/-- The diagonal and hence the `T = 1` case have a Varian certificate. -/
theorem hasPairwiseVarian_of_subsingleton [Subsingleton T] : HasPairwiseVarian D :=
  (wgarp_iff_pairwiseVarian D).mp (wgarp_of_subsingleton D)

end WGARP
