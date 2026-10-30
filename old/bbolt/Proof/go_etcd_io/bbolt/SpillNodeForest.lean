/-
The node graph of a bucket as a forest (`treeHN`: ranks, children and parents agreeing), and its
tree from the root (`kidsTree_rootN`), during `node.spill` (a copy of `SpillCommit.lean`'s
`treeH` lemmas).
-/
module

public import Proof.go_etcd_io.bbolt.SpillNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section tree
variable [ext : FfiSyntax]

/-- `x` is `y` or one of its parents' (up the parent chain). -/
inductive ancN (ns : GMap Loc NRec) (x : Loc) : Loc → Prop
  | self : ancN ns x x
  | up (y : Loc) (r : NRec) : ns !! y = some r → r.nv.parent' ≠ null → ancN ns x r.nv.parent' →
      ancN ns x y

/-- The facts of a node graph `ns` that make it a forest: ranks going up the parent chains,
bounded; children lists without duplicates, each child's parent the node; each node in its
parent's children. -/
def treeHN (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) : Prop :=
  (∀ l r, ns !! l = some r → rk l ≤ N ∧ (r.nv.parent' ≠ null → rk l < rk r.nv.parent')) ∧
  (∀ l r, ns !! l = some r → r.cs.Nodup ∧ ∀ c ∈ r.cs, ∃ rc, ns !! c = some rc ∧ rc.nv.parent' = l) ∧
  (∀ l r, ns !! l = some r → r.nv.parent' ≠ null → ∃ rp, ns !! r.nv.parent' = some rp ∧ l ∈ rp.cs) ∧
  (∀ l r, ns !! l = some r → l ≠ null)

theorem ancN_trans (ns : GMap Loc NRec) (x z y : Loc) (h1 : ancN ns x z) (h2 : ancN ns z y) :
    ancN ns x y := by
  induction h2 with
  | self => exact h1
  | up y r hy hp _ ih => exact .up y r hy hp ih

theorem ancN_some (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (hT : treeHN ns rk N) (x y : Loc)
    (h : ancN ns x y) (hx : (ns !! x).isSome) : (ns !! y).isSome := by
  induction h with
  | self => exact hx
  | up y r hy _ _ _ => rw [hy]; rfl

theorem ancN_rk (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (hT : treeHN ns rk N) (x y : Loc)
    (h : ancN ns x y) : rk y ≤ rk x := by
  induction h with
  | self => exact Nat.le_refl _
  | up y r hy hp _ ih => have := (hT.1 y r hy).2 hp; omega

theorem ancN_cmp (ns : GMap Loc NRec) (x y : Loc) (h1 : ancN ns x y) :
    ∀ z, ancN ns z y → ancN ns x z ∨ ancN ns z x := by
  induction h1 with
  | self => intro z h; exact Or.inr h
  | up y r hy hp h ih =>
    intro z h2
    cases h2 with
    | self => exact Or.inl (.up y r hy hp h)
    | up _ r' hy' hp' h' =>
      rw [hy] at hy'; cases hy'
      exact ih z h'

theorem ancN_child_unique (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (hT : treeHN ns rk N)
    (l c1 c2 y : Loc) (r1 r2 : NRec) (h1 : ns !! c1 = some r1) (h2 : ns !! c2 = some r2)
    (hp1 : r1.nv.parent' = l) (hp2 : r2.nv.parent' = l) (hl : l ≠ null)
    (a1 : ancN ns c1 y) (a2 : ancN ns c2 y) : c1 = c2 := by
  have key : ∀ a b ra rb, ns !! a = some ra → ns !! b = some rb → ra.nv.parent' = l →
      rb.nv.parent' = l → ancN ns a b → a = b := by
    intro a b ra rb ha hb hpa hpb hab
    cases hab with
    | self => rfl
    | up _ r hr hp hup =>
      rw [hb] at hr; cases hr
      rw [hpb] at hup
      have h1 := ancN_rk ns rk N hT a l hup
      have h2 := (hT.1 a ra ha).2 (by rw [hpa]; exact hl)
      rw [hpa] at h2
      omega
  rcases ancN_cmp ns c1 y a1 c2 a2 with h | h
  · exact key c1 c2 r1 r2 h1 h2 hp1 hp2 h
  · exact (key c2 c1 r2 r1 h2 h1 hp2 hp1 h).symm

theorem ancN_child (ns : GMap Loc NRec) (l y : Loc) (h : ancN ns l y) (hne : y ≠ l) :
    ∃ c r, ns !! c = some r ∧ r.nv.parent' = l ∧ ancN ns c y := by
  induction h with
  | self => exact absurd rfl hne
  | up y r hy hp h ih =>
    by_cases e : r.nv.parent' = l
    · exact ⟨y, r, hy, e, .self⟩
    · obtain ⟨c, rc, hc, hpc, hcy⟩ := ih e
      exact ⟨c, rc, hc, hpc, .up y r hy hp hcy⟩

theorem forall2_chooseN {α β : Type} (P : α → β → Prop) :
    ∀ (l : List α), (∀ a ∈ l, ∃ b, P a b) → ∃ bs, List.Forall₂ P l bs
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨bs, hbs⟩ := forall2_chooseN P l (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))
    exact ⟨b :: bs, .cons hb hbs⟩

theorem forall2_mem_rN {α β : Type} (P : α → β → Prop) :
    ∀ (xs : List α) (bs : List β), List.Forall₂ P xs bs → ∀ b ∈ bs, ∃ a ∈ xs, P a b
  | _, _, .nil, b, hb => by cases hb
  | _, _, .cons (a := a) (b := b0) hab h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', h'⟩ := forall2_mem_rN P _ _ h b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem forall2_mem_lN {α β : Type} (P : α → β → Prop) :
    ∀ (xs : List α) (bs : List β), List.Forall₂ P xs bs → ∀ a ∈ xs, ∃ b ∈ bs, P a b
  | _, _, .nil, a, ha => by cases ha
  | _, _, .cons (a := a0) (b := b) hab h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, List.mem_cons_self, hab⟩
    · obtain ⟨b', hb', h'⟩ := forall2_mem_lN P _ _ h a ha
      exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

theorem forall2_pairwiseN {α β : Type} (P : α → β → Prop) (R : β → β → Prop)
    (hR : ∀ a1 a2 b1 b2, P a1 b1 → P a2 b2 → a1 ≠ a2 → R b1 b2) :
    ∀ (xs : List α) (bs : List β), List.Forall₂ P xs bs → xs.Nodup → bs.Pairwise R
  | _, _, .nil, _ => .nil
  | _, _, .cons (a := a) (b := b) hab h, hnd => by
    have hna := (List.nodup_cons.1 hnd).1
    refine List.Pairwise.cons (fun b' hb' => ?_) (forall2_pairwiseN P R hR _ _ h (List.nodup_cons.1 hnd).2)
    obtain ⟨a', ha', h'⟩ := forall2_mem_rN P _ _ h b' hb'
    exact hR a a' b b' hab h' (fun e => hna (e ▸ ha'))

theorem nodup_flattenN {α : Type} : ∀ (L : List (List α)), (∀ l ∈ L, l.Nodup) →
    L.Pairwise List.Disjoint → L.flatten.Nodup
  | [], _, _ => List.nodup_nil
  | S :: L, h1, h2 => by
    rw [List.flatten_cons, List.nodup_append]
    refine ⟨h1 S List.mem_cons_self, nodup_flattenN L (fun l hl => h1 l (List.mem_cons_of_mem _ hl))
      (List.pairwise_cons.1 h2).2, fun a ha b hb e => ?_⟩
    subst e
    obtain ⟨S', hS', haS'⟩ := List.mem_flatten.1 hb
    exact (List.pairwise_cons.1 h2).1 S' hS' ha haS'

/-- The subtree of a node, by strong induction on its rank. -/
theorem kidsTree_of_treeHN (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (hT : treeHN ns rk N) :
    ∀ n l r, ns !! l = some r → rk l < n → ∃ S, kidsTree ns l S ∧ ∀ y, y ∈ S ↔ ancN ns l y := by
  intro n
  induction n with
  | zero => intro l r _ h; omega
  | succ n ih =>
    intro l r hl hn
    obtain ⟨hcnd, hcs⟩ := hT.2.1 l r hl
    let P : Loc → List Loc → Prop := fun c S => kidsTree ns c S ∧ (∀ y, y ∈ S ↔ ancN ns c y) ∧
      ∃ rc, ns !! c = some rc ∧ rc.nv.parent' = l
    have hex : ∀ c ∈ r.cs, ∃ S, P c S := by
      intro c hc
      obtain ⟨rc, hrc, hpc⟩ := hcs c hc
      have hlt : rk c < rk l := by
        have hl0 : l ≠ null := hT.2.2.2 l r hl
        have := (hT.1 c rc hrc).2 (by rw [hpc]; exact hl0)
        rw [hpc] at this; exact this
      obtain ⟨S, hS, hm⟩ := ih c rc hrc (by omega)
      exact ⟨S, hS, hm, rc, hrc, hpc⟩
    obtain ⟨subs, hsubs⟩ := forall2_chooseN P r.cs hex
    have hl0 : l ≠ null := hT.2.2.2 l r hl
    have hmem : ∀ y, y ∈ l :: subs.flatten ↔ ancN ns l y := by
      intro y
      constructor
      · intro hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact .self
        · obtain ⟨S, hS, hyS⟩ := List.mem_flatten.1 hy
          obtain ⟨c, -, hcS, hm, rc, hrc, hpc⟩ := forall2_mem_rN P _ _ hsubs S hS
          have hcy := (hm y).1 hyS
          exact ancN_trans ns l c y (.up c rc hrc (by rw [hpc]; exact hl0) (by rw [hpc]; exact .self)) hcy
      · intro hy
        by_cases e : y = l
        · rw [e]; exact List.mem_cons_self
        · obtain ⟨c, rc, hrc, hpc, hcy⟩ := ancN_child ns l y hy e
          obtain ⟨rp, hrp, hcin⟩ := hT.2.2.1 c rc hrc (by rw [hpc]; exact hl0)
          rw [hpc, hl] at hrp; cases hrp
          obtain ⟨S, hS, -, hm, -⟩ := forall2_mem_lN P _ _ hsubs c hcin
          exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨S, hS, (hm y).2 hcy⟩)
    refine ⟨l :: subs.flatten, .mk l r subs hl (hsubs.imp (fun h => h.1)) ?_, hmem⟩
    refine List.nodup_cons.2 ⟨fun hlS => ?_, ?_⟩
    · obtain ⟨S, hS, hyS⟩ := List.mem_flatten.1 hlS
      obtain ⟨c, -, -, hm, rc, hrc, hpc⟩ := forall2_mem_rN P _ _ hsubs S hS
      have h1 := ancN_rk ns rk N hT c l ((hm l).1 hyS)
      have h2 := (hT.1 c rc hrc).2 (by rw [hpc]; exact hl0)
      rw [hpc] at h2; omega
    · refine nodup_flattenN _ (fun S hS => ?_) ?_
      · obtain ⟨c, -, hcS, -⟩ := forall2_mem_rN P _ _ hsubs S hS
        exact kidsTree_nodup ns c S hcS
      · refine forall2_pairwiseN P List.Disjoint ?_ r.cs subs hsubs hcnd
        intro a1 a2 b1 b2 hb1 hb2 hne y hy1 hy2
        obtain ⟨-, hm1, r1, hr1, hp1⟩ := hb1
        obtain ⟨-, hm2, r2, hr2, hp2⟩ := hb2
        exact hne (ancN_child_unique ns rk N hT l a1 a2 y r1 r2 hr1 hr2 hp1 hp2 hl0
          ((hm1 y).1 hy1) ((hm2 y).1 hy2))

/-- Every node is under the root (the only node without a parent). -/
theorem ancN_root (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (hT : treeHN ns rk N) (rn : Loc)
    (hroot : ∀ l r, ns !! l = some r → r.nv.parent' = null → l = rn) :
    ∀ n l r, ns !! l = some r → N + 1 - rk l < n → ancN ns rn l := by
  intro n
  induction n with
  | zero => intro l r _ h; omega
  | succ n ih =>
    intro l r hl hn
    by_cases hp : r.nv.parent' = null
    · rw [hroot l r hl hp]; exact .self
    · obtain ⟨rp, hrp, -⟩ := hT.2.2.1 l r hl hp
      have h1 := (hT.1 l r hl).2 hp
      have h2 := (hT.1 _ rp hrp).1
      exact .up l r hl hp (ih _ rp hrp (by omega))

/-- A ranked node graph with one root is a tree from it, of all its nodes. -/
theorem kidsTree_rootN (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (hT : treeHN ns rk N)
    (rn : Loc) (r0 : NRec) (h0 : ns !! rn = some r0)
    (hroot : ∀ l r, ns !! l = some r → r.nv.parent' = null → l = rn) :
    ∃ S, kidsTree ns rn S ∧ ∀ y, y ∈ S ↔ (ns !! y).isSome := by
  obtain ⟨S, hS, hm⟩ := kidsTree_of_treeHN ns rk N hT (rk rn + 1) rn r0 h0 (by omega)
  refine ⟨S, hS, fun y => ⟨fun hy => ancN_some ns rk N hT rn y ((hm y).1 hy) (by rw [h0]; rfl),
    fun hy => ?_⟩⟩
  obtain ⟨ry, hry⟩ := Option.isSome_iff_exists.1 hy
  have := (hT.1 y ry hry).1
  exact (hm y).2 (ancN_root ns rk N hT rn hroot (N + 2 - rk y) y ry hry (by omega))


/-- The bucket's nodes a tree from its root, every one ready for `dereference`. -/
def treeOK (bl : Loc) (B : BRec) : Prop :=
  (∃ rk N, treeHN B.ns rk N) ∧ (∃ r0, B.ns !! B.bv.rootNode' = some r0 ∧ r0.nv.parent' = null) ∧
  (∀ l r, B.ns !! l = some r → r.nv.parent' = null → l = B.bv.rootNode') ∧
  (∀ l r, B.ns !! l = some r → derefOK bl r)

/-- A bucket whose nodes are a tree: its live nodes all of them. -/
theorem live_of_treeOK (bl : Loc) (B : BRec) (h : treeOK bl B) :
    ∃ S, liveNodesX B S ∧ ∀ l ∈ S, ∃ r, B.ns !! l = some r ∧ derefOK bl r := by
  obtain ⟨⟨rk, N, hT⟩, ⟨r0, h0, hp0⟩, hroot, hok⟩ := h
  obtain ⟨S, hS, hm⟩ := kidsTree_rootN B.ns rk N hT B.bv.rootNode' r0 h0 hroot
  refine ⟨S, ⟨[B.bv.rootNode'], B.bv.rootNode', upPath.self _ r0 h0 hp0,
    List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, hS, fun l hl hlS => ?_⟩, fun l hl => ?_⟩
  · rw [List.mem_singleton] at hl; subst hl
    exact absurd ((hm _).2 (by rw [h0]; rfl)) hlS
  · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 ((hm l).1 hl)
    exact ⟨r, hr, hok l r hr⟩

theorem bktReach_bmN (T T' : WTx) (rl : Loc)
    (hbm : ∀ c C', T'.bs !! c = some C' → ∃ C, T.bs !! c = some C ∧ C'.bm = C.bm)
    (hdom : ∀ c, (T.bs !! c).isSome → (T'.bs !! c).isSome) :
    ∀ c, bktReach T rl c → bktReach T' rl c := by
  intro c h
  induction h with
  | root => exact bktReach.root
  | child x X name y _ hX hn ih =>
    obtain ⟨X', hX'⟩ := Option.isSome_iff_exists.1 (hdom x (by rw [hX]; rfl))
    obtain ⟨X0, hX0, hb⟩ := hbm x X' hX'
    rw [hX] at hX0; cases hX0
    exact bktReach.child x X' name y ih hX' (by rw [hb]; exact hn)

end tree



end bbolt
end EtcdGrove
end Perennial
