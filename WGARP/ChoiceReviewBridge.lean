/-
SPDX-License-Identifier: Apache-2.0
This Lean source file is licensed under the Apache License, Version 2.0.
See LICENSE-LEAN for the terms and NOTICE-LEAN for attribution.
-/

import WGARP.Data
import Mathlib.Order.Filter.Extr

/-!
# Review interfaces: observations, alternative choices, and bundles of contracts

This downstream prototype addresses the distinction requested in MathEconLib
issue #201. It does not introduce a competing `ChoiceFunction` structure or
change the existing consumer dataset. MathEconLib's existing `ChoiceFunction`
already consists of a set map with contraction. The interfaces here use that
same raw map and its contraction property, for a later small upstream bridge.

An observed consumption bundle is one alternative in an observed opportunity
set. Utility rationalization requires membership in the maximizers, not unique
choice or a nonempty correspondence on all unobserved menus. In contrast, a
matching choice `C A` is one bundle of contracts held jointly. Its alternative-
level representation is the singleton `{C A}` in the opportunity set `A.powerset`.
In particular, choosing the empty contract bundle is not an empty set of
chosen bundle-alternatives.

The IRC/bundle-WARP equivalence below assumes the available menu domain is
intersection closed. It makes no assertion of individual-contract WARP,
consumer GARP, or substitutability. The tie-breaking example shows why an
arbitrary selection from weakly optimal bundles does not itself imply IRC.

Design discussion: Scott Duke Kominers and Bo Cowgill (2026),
https://github.com/matheconlib/matheconlib/issues/201 .
The terminology `Consistent` in MathEconLib.Choice.ChoiceFunction corresponds
to the unrestricted-menu instance of `IRCOn` here.
-/

set_option autoImplicit false

namespace WGARP.ChoiceReviewBridge

universe u v

variable {α : Type u} {T : Type v}

/-- A statement about specified observations, not a choice correspondence
defined on every menu. The index type may be finite, infinite, or empty. -/
def ObservedMaximizes (menus : T → Set α) (chosen : T → α) (u : α → ℝ) : Prop :=
  ∀ t, chosen t ∈ menus t ∧ IsMaxOn u (menus t) (chosen t)

/-- An observed greatest-choice condition for an arbitrary binary relation.
No completeness, transitivity, asymmetry, or uniqueness is built in. -/
def ObservedGreatest (menus : T → Set α) (chosen : T → α)
    (weaklyPreferred : α → α → Prop) : Prop :=
  ∀ t, chosen t ∈ menus t ∧ ∀ y ∈ menus t, weaklyPreferred (chosen t) y

theorem observedMaximizes_iff_observedGreatest
    (menus : T → Set α) (chosen : T → α) (u : α → ℝ) :
    ObservedMaximizes menus chosen u ↔
      ObservedGreatest menus chosen (fun x y => u y ≤ u x) := by
  simp only [ObservedMaximizes, ObservedGreatest, isMaxOn_iff]

/-- The accepted-paper dataset rationalization embeds into an observation
interface without creating choices on any unobserved menu. -/
theorem utilityRationalizes_iff_observedMaximizes
    {L : ℕ} (D : Dataset L T) (u : Utility L) :
    UtilityRationalizes D u ↔
      ObservedMaximizes (fun t => {y | Affordable D t y}) D.choice u := by
  constructor
  · intro h t
    exact ⟨affordable_choice D t, isMaxOn_iff.mpr (h t)⟩
  · intro h t y hy
    exact isMaxOn_iff.mp (h t).2 y hy

/-- The same observation interface accepts the possibly incomplete or
intransitive numerical preference functions used by the WGARP theorem. -/
theorem preferenceRationalizes_iff_observedGreatest
    {L : ℕ} (D : Dataset L T) (r : PreferenceFunction L) :
    PreferenceRationalizes D r ↔
      ObservedGreatest (fun t => {y | Affordable D t y}) D.choice
        (fun x y => 0 ≤ r x y) := by
  constructor
  · intro h t
    exact ⟨affordable_choice D t, h t⟩
  · intro h t y hy
    exact (h t).2 y hy

/-- Deterministic WARP at the level of observed alternatives. When an
alternative is itself a contract bundle, mutual availability is inclusion
of the two chosen bundles in the opposite contract menus. -/
def ObservedWARP (menus : T → Set α) (chosen : T → α) : Prop :=
  ∀ s t, chosen s ∈ menus t → chosen t ∈ menus s → chosen s = chosen t

/-- The matching interpretation treats the entire chosen contract set as
one alternative, not as many alternative consumption bundles. -/
def bundleAlternatives (C : Set α → Set α) (A : Set α) : Set (Set α) := {C A}

theorem bundleAlternatives_subset_powerset_iff (C : Set α → Set α) (A : Set α) :
    bundleAlternatives C A ⊆ A.powerset ↔ C A ⊆ A := by
  simp [bundleAlternatives]

/-- Choosing no contracts is one feasible chosen bundle-alternative. -/
theorem empty_contract_bundle_is_one_alternative (A : Set α) :
    (bundleAlternatives (fun _ => ∅) A).Nonempty ∧
      bundleAlternatives (fun _ => ∅) A ⊆ A.powerset := by
  simp [bundleAlternatives]

/-- IRC/consistency restricted to an explicit domain of contract menus. -/
def IRCOn (domain : Set (Set α)) (C : Set α → Set α) : Prop :=
  ∀ A ∈ domain, ∀ B ∈ domain, C A ⊆ B → B ⊆ A → C B = C A

/-- WARP for chosen bundles, each regarded as one alternative. It is not
WARP for individual contracts or the consumer-data predicate WGARP. -/
def BundleWARPOn (domain : Set (Set α)) (C : Set α → Set α) : Prop :=
  ∀ A ∈ domain, ∀ B ∈ domain, C A ⊆ B → C B ⊆ A → C A = C B

/-- The subbundle opportunity-set interpretation gives precisely bundle
WARP; no identification with individual-contract alternatives is used. -/
theorem bundleWARPOn_iff_observedWARP
    (domain : Set (Set α)) (C : Set α → Set α) :
    BundleWARPOn domain C ↔
      ObservedWARP (fun A : domain => (A : Set α).powerset)
        (fun A : domain => C A) := by
  constructor
  · intro h A B hAB hBA
    exact h A A.property B B.property hAB hBA
  · intro h A hA B hB hAB hBA
    exact h ⟨A, hA⟩ ⟨B, hB⟩ hAB hBA

/-- Scott Kominers' intersection argument: IRC is equivalent to bundle
WARP on an intersection-closed menu domain, with feasibility explicit. -/
theorem ircOn_iff_bundleWARPOn
    (domain : Set (Set α)) (C : Set α → Set α)
    (hcontract : ∀ A ∈ domain, C A ⊆ A)
    (hinter : ∀ A ∈ domain, ∀ B ∈ domain, A ∩ B ∈ domain) :
    IRCOn domain C ↔ BundleWARPOn domain C := by
  constructor
  · intro h A hA B hB hAB hBA
    have hI := hinter A hA B hB
    have hCA : C A ⊆ A ∩ B := fun _ hx => ⟨hcontract A hA hx, hAB hx⟩
    have hCB : C B ⊆ A ∩ B := fun _ hx => ⟨hBA hx, hcontract B hB hx⟩
    have heA : C (A ∩ B) = C A := h A hA (A ∩ B) hI hCA Set.inter_subset_left
    have heB : C (A ∩ B) = C B := h B hB (A ∩ B) hI hCB Set.inter_subset_right
    exact heA.symm.trans heB
  · intro h A hA B hB hAB hBA
    exact (h A hA B hB hAB ((hcontract B hB).trans hBA)).symm

/-- Unrestricted-menu specialization; no finiteness hypothesis is needed. -/
theorem irc_iff_bundleWARP (C : Set α → Set α)
    (hcontract : ∀ A, C A ⊆ A) :
    (∀ A B, C A ⊆ B → B ⊆ A → C B = C A) ↔
      ∀ A B, C A ⊆ B → C B ⊆ A → C A = C B := by
  simpa only [IRCOn, BundleWARPOn, Set.mem_univ, forall_true_left] using
    ircOn_iff_bundleWARPOn Set.univ C (fun A _ => hcontract A)
      (fun _ _ _ _ => Set.mem_univ _)

namespace Examples

/-- A menu-dependent selection among equally good bundles. -/
noncomputable def menuDependentTies (A : Set Bool) : Set Bool := by
  classical
  exact if A = {false} then {false} else ∅

theorem menuDependentTies_contracts (A : Set Bool) : menuDependentTies A ⊆ A := by
  classical
  by_cases h : A = {false}
  · subst A
    simp [menuDependentTies]
  · simp [menuDependentTies, h]

private theorem univ_ne_singleton_false : (Set.univ : Set Bool) ≠ {false} := by
  intro h
  have ht : true ∈ ({false} : Set Bool) := h ▸ Set.mem_univ true
  simp at ht

/-- Every selected bundle maximizes the SAME weak utility, constant zero,
but the arbitrary tie selection below still fails IRC. -/
theorem menuDependentTies_maximizes_constant_utility :
    ObservedMaximizes (fun A : Set Bool => A.powerset) menuDependentTies
      (fun _ : Set Bool => (0 : ℝ)) := by
  intro A
  exact ⟨menuDependentTies_contracts A, isMaxOn_iff.mpr (fun _ _ => le_rfl)⟩

theorem menuDependentTies_not_irc : ¬ IRCOn Set.univ menuDependentTies := by
  intro h
  have hsmall : menuDependentTies ({false} : Set Bool) = {false} := by
    simp [menuDependentTies]
  have hlarge : menuDependentTies (Set.univ : Set Bool) = ∅ := by
    unfold menuDependentTies
    rw [if_neg univ_ne_singleton_false]
  have he := h Set.univ (Set.mem_univ _) {false} (Set.mem_univ _)
    (by rw [hlarge]; exact Set.empty_subset _) (Set.subset_univ _)
  rw [hsmall, hlarge] at he
  have hf : false ∈ (∅ : Set Bool) := he ▸ Set.mem_singleton false
  exact hf

theorem menuDependentTies_not_bundleWARP :
    ¬ BundleWARPOn Set.univ menuDependentTies := by
  intro h
  exact menuDependentTies_not_irc
    ((ircOn_iff_bundleWARPOn Set.univ menuDependentTies
      (fun A _ => menuDependentTies_contracts A)
      (fun _ _ _ _ => Set.mem_univ _)).mpr h)

end Examples

#print axioms utilityRationalizes_iff_observedMaximizes
#print axioms preferenceRationalizes_iff_observedGreatest
#print axioms bundleWARPOn_iff_observedWARP
#print axioms ircOn_iff_bundleWARPOn
#print axioms Examples.menuDependentTies_maximizes_constant_utility
#print axioms Examples.menuDependentTies_not_bundleWARP

end WGARP.ChoiceReviewBridge
