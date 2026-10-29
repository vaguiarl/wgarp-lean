/-
SPDX-License-Identifier: Apache-2.0
This Lean source file is licensed under the Apache License, Version 2.0.
See LICENSE-LEAN for the terms and NOTICE-LEAN for attribution.
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order

/-!
# Compactness for finite-local descriptions

This is the compactness engine behind the scaling method of Gonczarowski,
Kominers, and Shorrer (2025), *To infinity and beyond: A general framework
for scaling economic theories*, Theoretical Economics 20, 511–542,
doi:10.3982/TE5878, Section 2 and Lemma 1.

We reuse Mathlib's topological compactness theorem. The closed-constraint
helper below is a local convenience wrapper, not a new compactness theorem
to upstream. A finite-local constraint is an arbitrary predicate of finitely
many values from a finite type. Its Boolean specialization covers every
finite propositional formula without duplicating a syntax API.
The scaling theorem transports this logical result through a faithful
description of an economic solution concept. It does not assert that every
finite-data theorem scales, or that a real-valued utility follows from an
arbitrary first-order model.
-/

namespace WGARP.LogicalCompactness

universe u v w z

/-- Closed constraints on a compact space have a simultaneous solution
provided every finite subfamily has one. This is a thin local wrapper around
Mathlib's `IsCompact.inter_iInter_nonempty`, retained for downstream
readability and API compatibility rather than proposed as new mathematics. -/
theorem exists_satisfying_closed_constraints
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {I : Type v} (P : I → X → Prop)
    (hclosed : ∀ i, IsClosed {x | P i x})
    (hfinite : ∀ s : Finset I, ∃ x, ∀ i ∈ s, P i x) :
    ∃ x, ∀ i, P i x := by
  have h := isCompact_univ.inter_iInter_nonempty
    (fun i => {x | P i x}) hclosed (by
      intro s
      obtain ⟨x, hx⟩ := hfinite s
      exact ⟨x, by simpa using hx⟩)
  simpa using h

/-- Compactness for constraints depending on finitely many variables with
values in an arbitrary finite type. Neither the variable set nor the
constraint set need be finite or countable. No nonempty-value assumption
is hidden: finite feasibility, including the empty subfamily, supplies any
assignment needed by the proof. -/
theorem finite_local_compactness
    {Value : Type z} [Finite Value]
    {V : Type u} {I : Type v} {Key : I → Type w}
    [∀ i, Finite (Key i)]
    (vars : (i : I) → Key i → V)
    (allowed : (i : I) → (Key i → Value) → Prop)
    (hfinite : ∀ s : Finset I, ∃ a : V → Value,
      ∀ i ∈ s, allowed i (fun k => a (vars i k))) :
    ∃ a : V → Value, ∀ i, allowed i (fun k => a (vars i k)) := by
  letI : TopologicalSpace Value := ⊥
  letI : DiscreteTopology Value := ⟨rfl⟩
  apply exists_satisfying_closed_constraints
    (fun i (a : V → Value) => allowed i (fun k => a (vars i k)))
  · intro i
    have hc : Continuous (fun a : V → Value => fun k : Key i => a (vars i k)) :=
      continuous_pi fun k => continuous_apply (vars i k)
    exact (isClosed_discrete {b : Key i → Value | allowed i b}).preimage hc
  · exact hfinite

/-- A finite-valued finite-local description is satisfiable exactly when
each finite subdescription is satisfiable. -/
theorem finite_local_compactness_iff
    {Value : Type z} [Finite Value]
    {V : Type u} {I : Type v} {Key : I → Type w}
    [∀ i, Finite (Key i)]
    (vars : (i : I) → Key i → V)
    (allowed : (i : I) → (Key i → Value) → Prop) :
    (∃ a : V → Value, ∀ i, allowed i (fun k => a (vars i k))) ↔
      ∀ s : Finset I, ∃ a : V → Value,
        ∀ i ∈ s, allowed i (fun k => a (vars i k)) := by
  constructor
  · rintro ⟨a, ha⟩ s
    exact ⟨a, fun i _hi => ha i⟩
  · exact finite_local_compactness vars allowed

/-- Propositional compactness as a specialization of finite-valued
compactness. This preserves the original public Boolean interface. -/
theorem finite_local_bool_compactness
    {V : Type u} {I : Type v} {Key : I → Type w}
    [∀ i, Finite (Key i)]
    (vars : (i : I) → Key i → V)
    (allowed : (i : I) → (Key i → Bool) → Prop)
    (hfinite : ∀ s : Finset I, ∃ a : V → Bool,
      ∀ i ∈ s, allowed i (fun k => a (vars i k))) :
    ∃ a : V → Bool, ∀ i, allowed i (fun k => a (vars i k)) :=
  finite_local_compactness vars allowed hfinite

/-- A finite-local Boolean description is satisfiable exactly when each
finite subdescription is satisfiable. -/
theorem finite_local_bool_compactness_iff
    {V : Type u} {I : Type v} {Key : I → Type w}
    [∀ i, Finite (Key i)]
    (vars : (i : I) → Key i → V)
    (allowed : (i : I) → (Key i → Bool) → Prop) :
    (∃ a : V → Bool, ∀ i, allowed i (fun k => a (vars i k))) ↔
      ∀ s : Finset I, ∃ a : V → Bool,
        ∀ i ∈ s, allowed i (fun k => a (vars i k)) := by
  constructor
  · rintro ⟨a, ha⟩ s
    exact ⟨a, fun i _hi => ha i⟩
  · exact finite_local_bool_compactness vars allowed

/-- The GKS scaling principle: a faithful finite-local description and
finite-subset transfer from solvable problems yield a solution for the
target problem. No finiteness of the target variable set is assumed. -/
theorem scaling_of_finite_local_description
    {Problem : Type*} {V : Type u} {I : Type v} {Key : I → Type w}
    [∀ i, Finite (Key i)]
    (solution : Problem → Prop)
    (vars : (i : I) → Key i → V)
    (allowed : Problem → (i : I) → (Key i → Bool) → Prop)
    (description : ∀ p, solution p ↔
      ∃ a : V → Bool, ∀ i, allowed p i (fun k => a (vars i k)))
    (p : Problem)
    (finite_subset_property : ∀ s : Finset I, ∃ q,
      solution q ∧ ∀ a : V → Bool,
        (∀ i, allowed q i (fun k => a (vars i k))) →
          ∀ i ∈ s, allowed p i (fun k => a (vars i k))) :
    solution p := by
  apply (description p).mpr
  apply finite_local_bool_compactness vars (allowed p)
  intro s
  obtain ⟨q, hq, htransfer⟩ := finite_subset_property s
  obtain ⟨a, ha⟩ := (description q).mp hq
  exact ⟨a, htransfer a ha⟩

namespace Examples

private def chainVars (n : ℕ) (k : Fin 2) : ℕ := n + k.val

private def chainRule (n : ℕ) (b : Fin 2 → Bool) : Prop :=
  if n = 0 then b 0 = false ∧ b 1 = true else b 0 = true → b 1 = true

/-- A checked application to an infinite family of two-variable rules.
The model is false at zero, true at one, and stays true thereafter. -/
theorem infinite_chain_model :
    ∃ a : ℕ → Bool, a 0 = false ∧ a 1 = true ∧
      ∀ n, 0 < n → a n = true → a (n + 1) = true := by
  have hf : ∀ s : Finset ℕ, ∃ a : ℕ → Bool,
      ∀ n ∈ s, chainRule n (fun k => a (chainVars n k)) := by
    intro s
    refine ⟨fun n => if n = 0 then false else true, ?_⟩
    intro n _hn
    by_cases h : n = 0
    · simp [chainRule, chainVars, h]
    · simp [chainRule, chainVars, h]
  obtain ⟨a, ha⟩ := finite_local_bool_compactness chainVars chainRule hf
  have hzero := ha 0
  have hz : a 0 = false ∧ a 1 = true := by
    simpa [chainRule, chainVars] using hzero
  refine ⟨a, hz.1, hz.2, ?_⟩
  intro n hn
  have h := ha n
  simpa [chainRule, chainVars, Nat.ne_of_gt hn] using h

end Examples
end WGARP.LogicalCompactness
