/-
SPDX-License-Identifier: Apache-2.0
This Lean source file is licensed under the Apache License, Version 2.0.
See LICENSE-LEAN for the terms and NOTICE-LEAN for attribution.
-/

import WGARP.Data
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Lattice

set_option autoImplicit false

/-!
# Shared expenditure and affine primitives

These declarations are shared by classical finite Afriat and the pairwise
WGARP construction. They were extracted from `WGARP.Afriat` without changing
their public names, statements, or binder names. Classical Afriat need not
import pairwise WGARP certificates merely to use a continuous linear price
functional. This is a downstream dependency cleanup, not a MathEconLib port
or a replacement for its general choice API.
-/

open scoped BigOperators

namespace WGARP

variable {L : ℕ} {T : Type*}

/-- Wealth at an observed price-choice pair. -/
def wealth (D : Dataset L T) (s : T) : ℝ :=
  expenditure D s (D.choice s)

/-- A positive finite-dimensional price vector defines a strictly
increasing expenditure functional for the paper's weak-coordinate-plus-
inequality notion of strict dominance. -/
theorem dot_strictlyIncreasing_of_pos
    {p x z : Bundle L} (hp : ∀ i, 0 < p i)
    (hxz : StrictDominates x z) :
    dot p z < dot p x := by
  rcases hxz with ⟨hle, hne⟩
  have hexists : ∃ i, z i < x i := by
    by_contra hnone
    apply hne
    funext i
    have hxle : x i ≤ z i := by
      apply le_of_not_gt
      intro hstrict
      exact hnone ⟨i, hstrict⟩
    exact le_antisymm hxle (hle i)
  unfold dot
  apply Finset.sum_lt_sum
  · intro i _hi
    exact mul_le_mul_of_nonneg_left (hle i) (hp i).le
  · obtain ⟨i, hi⟩ := hexists
    exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hp i)⟩

/-- Observed expenditure is strictly increasing under strict dominance. -/
theorem expenditure_strictlyIncreasing
    (D : Dataset L T) (s : T) :
    StrictlyIncreasing (expenditure D s) := by
  intro x z hxz
  exact dot_strictlyIncreasing_of_pos (D.price_pos s) hxz

/-- The finite-dimensional dot product is continuous in its second
argument. -/
theorem continuous_dot (p : Bundle L) : Continuous (dot p) := by
  unfold dot
  apply continuous_finsetSum Finset.univ
  intro i _hi
  exact continuous_const.mul (continuous_apply i)

/-- Linear functional represented by the package's finite dot product. -/
def dotLinear (p : Bundle L) : Bundle L →ₗ[ℝ] ℝ where
  toFun x := dot p x
  map_add' x y := by
    simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    calc
      dot p (a • x) = ∑ i : Fin L, a * (p i * x i) := by
        unfold dot
        apply Finset.sum_congr rfl
        intro i _hi
        simp
        ring
      _ = a * dot p x := by
        simp [dot, Finset.mul_sum]

@[simp]
theorem dotLinear_apply (p x : Bundle L) : dotLinear p x = dot p x := rfl

/-- Dot products preserve affine combinations. -/
theorem dot_add_smul (p x y : Bundle L) (a b : ℝ) :
    dot p (a • x + b • y) = a * dot p x + b * dot p y := by
  change dotLinear p (a • x + b • y) =
    a * dotLinear p x + b * dotLinear p y
  rw [map_add, map_smul, map_smul]
  simp only [smul_eq_mul]

end WGARP
