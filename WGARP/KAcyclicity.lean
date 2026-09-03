import WGARP.GARP
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false

/-!
# Finite revealed-preference cycles

This file formalizes the paper's exact `k`-acyclicity convention.  A cycle is
a list of exactly `k` observations: consecutive observations are directly
weakly revealed preferred and the last observation is directly *strictly*
revealed preferred to the first.  The list need not be injective.  Thus the
formalization deliberately permits the repeated observations used to pad a
shorter cycle to length `k`.

The main combinatorial result identifies this condition with GARP on every
nonempty restriction containing at most `k` observations.  Its loop-erasure
step is explicit: a directed reachability witness is regarded as a walk in
the symmetrized simple graph, repeated vertices are bypassed, and the
orientation of every retained dart is recovered from the original walk.
-/

namespace WGARP

variable {L : ℕ} {T : Type*}

/-- Restrict a dataset to a finite set of its observations. -/
def Dataset.restrict [DecidableEq T] (D : Dataset L T) (S : Finset T) :
    Dataset L {t // t ∈ S} where
  price t := D.price t.1
  choice t := D.choice t.1
  goods_two_le := D.goods_two_le
  price_pos t := D.price_pos t.1
  choice_nonneg t := D.choice_nonneg t.1
  choice_ne_zero t := D.choice_ne_zero t.1

@[simp]
theorem Dataset.restrict_price [DecidableEq T]
    (D : Dataset L T) (S : Finset T) (t : {t // t ∈ S}) :
    (D.restrict S).price t = D.price t.1 := rfl

@[simp]
theorem Dataset.restrict_choice [DecidableEq T]
    (D : Dataset L T) (S : Finset T) (t : {t // t ∈ S}) :
    (D.restrict S).choice t = D.choice t.1 := rfl

@[simp]
theorem Dataset.restrict_expenditureGap [DecidableEq T]
    (D : Dataset L T) (S : Finset T) (s t : {t // t ∈ S}) :
    expenditureGap (D.restrict S) s t = expenditureGap D s.1 t.1 := rfl

/-- A paper-exact revealed-preference cycle with exactly `k` (not
necessarily distinct) observations. -/
def HasKCycle (D : Dataset L T) (k : ℕ) : Prop :=
  ∃ l : List T,
    l.length = k ∧
    ∃ hne : l ≠ [],
      l.IsChain (DirectRevealed D) ∧
      StrictDirectRevealed D (l.getLast hne) (l.head hne)

/-- The paper's `k`-acyclicity axiom.  Repetitions in the witnessing chain
are allowed, exactly as needed for the monotonicity across cycle lengths
used in the manuscript. -/
def KAcyclic (D : Dataset L T) (k : ℕ) : Prop :=
  ¬ HasKCycle D k

/-- GARP holds on every nonempty restriction of cardinality at most `k`. -/
def SmallRestrictionGARP [DecidableEq T] (D : Dataset L T) (k : ℕ) : Prop :=
  ∀ (S : Finset T), S.Nonempty → S.card ≤ k → GARP (D.restrict S)

namespace DirectedLoopErasure

variable {A : Type*} (R : A → A → Prop)

/-- The undirected shadow used only to invoke finite walk loop erasure. -/
def shadow : SimpleGraph A := SimpleGraph.fromRel R

/-- Every dart of a walk has the original directed orientation. -/
def Directed {a b : A} (p : (shadow R).Walk a b) : Prop :=
  ∀ d ∈ p.darts, R d.1.1 d.1.2

theorem directed_nil (a : A) : Directed R ((SimpleGraph.Walk.nil : (shadow R).Walk a a)) := by
  simp [Directed]

theorem directed_toWalk {a b : A} (hab : R a b) (hne : a ≠ b) :
    Directed R ((show (shadow R).Adj a b from
      (SimpleGraph.fromRel_adj R a b).2 ⟨hne, Or.inl hab⟩).toWalk) := by
  intro d hd
  simp only [SimpleGraph.Walk.darts, List.mem_singleton] at hd
  subst d
  exact hab

theorem Directed.append {a b c : A}
    {p : (shadow R).Walk a b} {q : (shadow R).Walk b c}
    (hp : Directed R p) (hq : Directed R q) : Directed R (p.append q) := by
  intro d hd
  rw [SimpleGraph.Walk.darts_append] at hd
  rcases List.mem_append.mp hd with hd | hd
  · exact hp d hd
  · exact hq d hd

/-- A reflexive-transitive directed path can be represented by a walk in the
undirected shadow without losing the orientation of any traversed dart.
Reflexive directed steps are discarded, since simple graphs have no loops. -/
theorem exists_directedWalk_of_reflTransGen {a b : A}
    (h : Relation.ReflTransGen R a b) :
    ∃ p : (shadow R).Walk a b, Directed R p := by
  induction h with
  | refl => exact ⟨SimpleGraph.Walk.nil, directed_nil R _⟩
  | @tail b c h hab ih =>
      obtain ⟨p, hp⟩ := ih
      by_cases heq : b = c
      · subst c
        exact ⟨p, hp⟩
      · let hedge : (shadow R).Adj b c :=
          (SimpleGraph.fromRel_adj R b c).2 ⟨heq, Or.inl hab⟩
        exact ⟨p.append hedge.toWalk,
          Directed.append R hp (directed_toWalk R hab heq)⟩

/-- Loop erasure retains only darts of the original walk, so their directed
orientation is retained as well. -/
theorem Directed.bypass [DecidableEq A] {a b : A}
    {p : (shadow R).Walk a b} (hp : Directed R p) :
    Directed R p.bypass := by
  intro d hd
  exact hp d (p.darts_bypass_sublist_darts.subset hd)

/-- A directed walk induces a chain in the original relation on its support. -/
theorem Directed.isChain_support {a b : A}
    {p : (shadow R).Walk a b} (hp : Directed R p) :
    p.support.IsChain R := by
  induction p with
  | nil => exact .singleton _
  | @cons a b c hab p ih =>
      rw [SimpleGraph.Walk.support_cons]
      apply List.IsChain.cons
      · apply ih
        intro d hd
        exact hp d (by simp [SimpleGraph.Walk.darts, hd])
      · intro y hy
        have hbhead : p.support.head? = some b := by cases p <;> rfl
        have hyb : y = b := (Option.some.inj (hbhead.symm.trans hy)).symm
        subst y
        exact hp ⟨(a, b), hab⟩ (by simp [SimpleGraph.Walk.darts])

/-- Finite directed loop erasure: reachability has a direct chain with the
same endpoints and at most one occurrence of each vertex. -/
theorem exists_simple_directed_chain [Fintype A] {a b : A}
    (h : Relation.ReflTransGen R a b) :
    ∃ (l : List A) (hne : l ≠ []),
      l.head hne = a ∧ l.getLast hne = b ∧ l.IsChain R ∧
      l.Nodup ∧ l.length ≤ Fintype.card A := by
  classical
  obtain ⟨p, hp⟩ := exists_directedWalk_of_reflTransGen R h
  let q := p.bypass
  have hqdir : Directed R q := hp.bypass
  have hqpath : q.IsPath := p.bypass_isPath
  refine ⟨q.support, q.support_ne_nil, ?_, ?_, hqdir.isChain_support,
    hqpath.support_nodup, ?_⟩
  · exact q.head_support
  · exact q.getLast_support
  · rw [q.length_support]
    have hlt := hqpath.length_lt
    omega

end DirectedLoopErasure

namespace ChainPadding

variable {A : Type*} {R : A → A → Prop}

/-- Pad a nonempty chain on the left by repetitions of its first vertex. -/
def padLeft (l : List A) (n : ℕ) (hne : l ≠ []) : List A :=
  List.replicate (n - l.length) (l.head hne) ++ l

theorem padLeft_ne_nil (l : List A) (n : ℕ) (hne : l ≠ []) :
    padLeft l n hne ≠ [] := by
  simp [padLeft, hne]

theorem length_padLeft {l : List A} {n : ℕ} (hne : l ≠ [])
    (hlen : l.length ≤ n) :
    (padLeft l n hne).length = n := by
  simp [padLeft]
  omega

theorem head_padLeft {l : List A} {n : ℕ} (hne : l ≠ []) :
    (padLeft l n hne).head (padLeft_ne_nil l n hne) = l.head hne := by
  by_cases hzero : n - l.length = 0
  · simp [padLeft, hzero]
  · have hpos : 0 < n - l.length := Nat.pos_of_ne_zero hzero
    simp [padLeft, hpos.ne']

theorem getLast_padLeft {l : List A} {n : ℕ} (hne : l ≠ []) :
    (padLeft l n hne).getLast (padLeft_ne_nil l n hne) = l.getLast hne := by
  exact List.getLast_append_of_ne_nil _ hne

theorem isChain_replicate (a : A) (n : ℕ) (haa : R a a) :
    (List.replicate n a).IsChain R := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
      cases n with
      | zero => exact .singleton _
      | succ n =>
          rw [List.replicate_succ]
          apply ih.cons
          intro y hy
          have hhead : (List.replicate (n + 1) a).head? = some a := by
            rw [List.head?_replicate]
            simp
          have hay : a = y := Option.some.inj (hhead.symm.trans hy)
          subst y
          exact haa

theorem isChain_padLeft {l : List A} {n : ℕ} (hne : l ≠ [])
    (hchain : l.IsChain R) (hrefl : R (l.head hne) (l.head hne)) :
    (padLeft l n hne).IsChain R := by
  rw [padLeft, List.isChain_append]
  refine ⟨isChain_replicate _ _ hrefl, hchain, ?_⟩
  intro x hx y hy
  simp only [List.getLast?_replicate] at hx
  split at hx
  · contradiction
  · have hx' : x = l.head hne := (by simpa using hx : l.head hne = x).symm
    have hy' : y = l.head hne := by
      have hhead : l.head? = some (l.head hne) := List.head?_eq_some_head hne
      exact (Option.some.inj (hhead.symm.trans hy)).symm
    simpa [hx', hy'] using hrefl

end ChainPadding

/-- The chain convention implies the usual monotonicity in its length: a
cycle with at most `k` vertices can be padded, using repeated observations,
to one with exactly `k` vertices. -/
theorem hasKCycle_of_chain_le
    (D : Dataset L T) {l : List T} {k : ℕ} (hne : l ≠ [])
    (hlen : l.length ≤ k) (hchain : l.IsChain (DirectRevealed D))
    (hclose : StrictDirectRevealed D (l.getLast hne) (l.head hne)) :
    HasKCycle D k := by
  let padded := ChainPadding.padLeft l k hne
  have hpne : padded ≠ [] := ChainPadding.padLeft_ne_nil l k hne
  refine ⟨padded, ChainPadding.length_padLeft hne hlen, hpne, ?_, ?_⟩
  · apply ChainPadding.isChain_padLeft hne hchain
    simp [DirectRevealed]
  · dsimp [padded]
    rw [ChainPadding.getLast_padLeft hne, ChainPadding.head_padLeft hne]
    exact hclose

/-- Every small-restriction GARP condition rules out a paper-exact cycle. -/
theorem kAcyclic_of_smallRestrictionGARP [Fintype T] [DecidableEq T]
    (D : Dataset L T) {k : ℕ} (hsmall : SmallRestrictionGARP D k) :
    KAcyclic D k := by
  classical
  intro hcycle
  rcases hcycle with ⟨l, hlen, hne, hchain, hstrict⟩
  let S : Finset T := l.toFinset
  have hSnonempty : S.Nonempty := by
    exact ⟨l.head hne, by simp [S, List.head_mem hne]⟩
  have hScard : S.card ≤ k := by
    calc
      S.card ≤ l.length := by simpa [S] using l.toFinset_card_le
      _ = k := hlen
  have hG := hsmall S hSnonempty hScard
  let memS : ∀ x ∈ l, x ∈ S := fun x hx => by simpa [S] using hx
  let lifted : List {x // x ∈ S} :=
    List.pmap (fun x hx => (⟨x, hx⟩ : {x // x ∈ S})) l memS
  have hlift_ne : lifted ≠ [] := by simp [lifted, hne]
  have hlift_chain : lifted.IsChain (DirectRevealed (D.restrict S)) := by
    dsimp [lifted]
    apply List.isChain_pmap_of_isChain
      (f := fun a ha => (⟨a, ha⟩ : {x // x ∈ S})) (p := fun x => x ∈ S)
    · intro a b ha hb hab
      simpa [DirectRevealed] using hab
    · exact hchain
  have hreach : DatasetRevealedPref (D.restrict S)
      (lifted.head hlift_ne) (lifted.getLast hlift_ne) := by
    exact Relation.ReflTransGen.mono
      (fun a b hab => (directRevealed_iff_directRP (D.restrict S) a b).mp hab)
      _ _ (List.relationReflTransGen_of_exists_isChain lifted hlift_chain hlift_ne)
  have hclose : StrictDirectRevealed (D.restrict S)
      (lifted.getLast hlift_ne) (lifted.head hlift_ne) := by
    have hhead := List.head_attachWith (P := fun x => x ∈ S) hlift_ne
    have hlast := List.getLast_attachWith (P := fun x => x ∈ S) hlift_ne
    simpa [lifted, StrictDirectRevealed] using hstrict
  exact ((garp_dataset_iff (D.restrict S)).1 hG _ _ hreach) hclose

/-- Paper-exact `k`-acyclicity implies GARP on every nonempty restriction
with at most `k` observations. -/
theorem smallRestrictionGARP_of_kAcyclic [Fintype T] [DecidableEq T]
    (D : Dataset L T) {k : ℕ} (hacyclic : KAcyclic D k) :
    SmallRestrictionGARP D k := by
  classical
  intro S hSnonempty hScard
  rw [garp_dataset_iff]
  intro s t hreach hstrict
  have hreach' : Relation.ReflTransGen (DirectRevealed (D.restrict S)) s t := by
    exact Relation.ReflTransGen.mono
      (fun a b hab => (directRevealed_iff_directRP (D.restrict S) a b).mpr hab)
      _ _ hreach
  obtain ⟨l, hne, hhead, hlast, hchain, _hnodup, hcard⟩ :=
    DirectedLoopErasure.exists_simple_directed_chain
      (R := DirectRevealed (D.restrict S)) hreach'
  have hlen : l.length ≤ k := by
    calc
      l.length ≤ Fintype.card {x // x ∈ S} := hcard
      _ = S.card := Fintype.card_coe S
      _ ≤ k := hScard
  let projected : List T := l.map Subtype.val
  have hprojected_ne : projected ≠ [] := by
    intro hp
    exact hne (List.map_eq_nil_iff.mp hp)
  have hprojected_chain : projected.IsChain (DirectRevealed D) := by
    dsimp [projected]
    rw [List.isChain_map]
    exact hchain.imp fun _ _ hab => by simpa [DirectRevealed] using hab
  have hprojected_close : StrictDirectRevealed D
      (projected.getLast hprojected_ne) (projected.head hprojected_ne) := by
    have hhead' : (projected.head hprojected_ne) = s.1 := by
      calc
        projected.head hprojected_ne = (l.head hne).1 := List.head_map hprojected_ne
        _ = s.1 := congrArg Subtype.val hhead
    have hlast' : (projected.getLast hprojected_ne) = t.1 := by
      calc
        projected.getLast hprojected_ne = (l.getLast hne).1 :=
          List.getLast_map hprojected_ne
        _ = t.1 := congrArg Subtype.val hlast
    simpa [hhead', hlast', StrictDirectRevealed] using hstrict
  apply hacyclic
  apply hasKCycle_of_chain_le D hprojected_ne
  · simpa [projected] using hlen
  · exact hprojected_chain
  · exact hprojected_close

/-- Exact bridge used in Theorem 2: `k`-acyclicity is equivalent to GARP on
every restriction of at most `k` observations. -/
theorem kAcyclic_iff_smallRestrictionGARP [Fintype T] [DecidableEq T]
    (D : Dataset L T) (k : ℕ) :
    KAcyclic D k ↔ SmallRestrictionGARP D k := by
  exact ⟨smallRestrictionGARP_of_kAcyclic D,
    kAcyclic_of_smallRestrictionGARP D⟩

end WGARP
