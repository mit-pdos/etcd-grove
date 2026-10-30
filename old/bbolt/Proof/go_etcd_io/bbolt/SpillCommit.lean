/-
`Commit`'s spill, `tx.root.spill()`, from what `rebalance` leaves (`spill_start`: the
transaction during the spill, `spillR`/`spillG`, and `Bucket.spill.spec`'s premises for the root
bucket, every bucket reachable from it) to what `Commit` needs after it (`spill_tree`: the root
bucket's root page and its written tree, `wtree`, over the view's and the dirty pages, below
the transaction's high-water mark).

`rebalance`'s post (`RebalanceBkt.lean`): `ownWriteTx`, `txShapeR`, `dbWR`, the stash of freed
pages, with every bucket in the rebalance's invariant (`rblTxOK`: clean, `rblKeys`, parent
pointers without cycle `rblAcyc` — a tree, `bktRanked_of_acyc` —, heights `rblHt`), balanced
from the root bucket (`balancedFrom`), the freed pages `freedOK`.

What `Commit`'s caller must give beyond it (`spillPre`): every bucket reachable from the root
one through the bucket caches, those caches acyclic (`dep`); each bucket's leaves' entries
without a child page (`leafPg0`), every entry's key and value together at most 2^28 bytes, its split
threshold at most the page size (a float fact); the page size below 1 MiB; of the database, no
reader's high-water mark above the writer's (not among `dbOK`'s facts); each bucket opened
from one parent entry (`bmUnique`, a write-path fact); and the meta's high-water mark times the
page size below 2^48 (`hpg`). `spill_root` is `tx.root.spill()` from `rebalance`'s post.
-/
module

public import Proof.go_etcd_io.bbolt.SpillReady
public import Proof.go_etcd_io.bbolt.RebalanceBkt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [float_sem : go.FloatConvSemantics]

/-- What `Commit`'s spill needs beyond `rebalance`'s post (see the module doc). -/
def spillPre (W : WView) (txl : Loc) (T : WTx) (ρ : DBState) : Prop :=
  (∀ c, (T.bs !! c).isSome → bktReach T (structFieldRef Tx go!"root" txl) c) ∧
  (∃ dep : Loc → Nat, ∀ bl B name c, T.bs !! bl = some B → B.bm !! name = some c → dep c < dep bl) ∧
  (∀ c C, T.bs !! c = some C → leafPg0 C ∧
    (∀ l r, C.ns !! l = some r → ∀ w ∈ r.ws, w.key.length + w.value.length ≤ 2 ^ 28) ∧
    uint.Z (splitThr (W64 (W.ps : Int)) C.bv.FillPercent') ≤ W.ps) ∧
  W.ps < 2 ^ 20 ∧ (∀ k r, ρ.readers !! k = some r → r.hwm ≤ W.hwm) ∧ bmUnique T

end pure

/-! ### Parent pointers without cycle are a ranked tree -/

section ranked
variable [ext : FfiSyntax]

theorem le_sum_of_memC (f : Loc → Nat) : ∀ (L : List Loc) (l : Loc), l ∈ L → f l ≤ (L.map f).sum
  | [], _, h => by cases h
  | x :: xs, l, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_sum_of_memC f xs l h; omega

/-- `rebalance`'s parent pointers without cycle (`rblAcyc`) rank the nodes (`bktRanked`): the
ranks of the finitely many nodes are bounded. -/
theorem bktRanked_of_acyc (B : BRec) (h : rblAcyc B) : bktRanked B := by
  obtain ⟨ht, hht⟩ := h
  refine ⟨ht, (B.ns.domList.map ht).sum, fun l r hr => ⟨?_, hht l r hr⟩⟩
  exact le_sum_of_memC ht _ l ((GMap.mem_dom_list B.ns l).2 (by rw [hr]; rfl))

end ranked

/-! ### A ranked node graph is a tree from its root (`kidsTree`) -/

section tree
variable [ext : FfiSyntax]

/-- `x` is `y` or one of its parents' (up the parent chain). -/
inductive ancC (ns : GMap Loc NRec) (x : Loc) : Loc → Prop
  | self : ancC ns x x
  | up (y : Loc) (r : NRec) : ns !! y = some r → r.nv.parent' ≠ null → ancC ns x r.nv.parent' →
      ancC ns x y

/-- The facts of a node graph `ns` that make it a forest: ranks going up the parent chains,
bounded; children lists without duplicates, each child's parent the node; each node in its
parent's children. -/
def treeH (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) : Prop :=
  (∀ l r, ns !! l = some r → rk l ≤ N ∧ (r.nv.parent' ≠ null → rk l < rk r.nv.parent')) ∧
  (∀ l r, ns !! l = some r → r.cs.Nodup ∧ ∀ c ∈ r.cs, ∃ rc, ns !! c = some rc ∧ rc.nv.parent' = l) ∧
  (∀ l r, ns !! l = some r → r.nv.parent' ≠ null → ∃ rp, ns !! r.nv.parent' = some rp ∧ l ∈ rp.cs) ∧
  (∀ l r, ns !! l = some r → l ≠ null)

theorem ancC_trans (ns : GMap Loc NRec) (x z y : Loc) (h1 : ancC ns x z) (h2 : ancC ns z y) :
    ancC ns x y := by
  induction h2 with
  | self => exact h1
  | up y r hy hp _ ih => exact .up y r hy hp ih

theorem ancC_some (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (hT : treeH ns rk N) (x y : Loc)
    (h : ancC ns x y) (hx : (ns !! x).isSome) : (ns !! y).isSome := by
  induction h with
  | self => exact hx
  | up y r hy _ _ _ => rw [hy]; rfl

theorem ancC_rk (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (hT : treeH ns rk N) (x y : Loc)
    (h : ancC ns x y) : rk y ≤ rk x := by
  induction h with
  | self => exact Nat.le_refl _
  | up y r hy hp _ ih => have := (hT.1 y r hy).2 hp; omega

theorem ancC_cmp (ns : GMap Loc NRec) (x y : Loc) (h1 : ancC ns x y) :
    ∀ z, ancC ns z y → ancC ns x z ∨ ancC ns z x := by
  induction h1 with
  | self => intro z h; exact Or.inr h
  | up y r hy hp h ih =>
    intro z h2
    cases h2 with
    | self => exact Or.inl (.up y r hy hp h)
    | up _ r' hy' hp' h' =>
      rw [hy] at hy'; cases hy'
      exact ih z h'

theorem ancC_child_unique (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (hT : treeH ns rk N)
    (l c1 c2 y : Loc) (r1 r2 : NRec) (h1 : ns !! c1 = some r1) (h2 : ns !! c2 = some r2)
    (hp1 : r1.nv.parent' = l) (hp2 : r2.nv.parent' = l) (hl : l ≠ null)
    (a1 : ancC ns c1 y) (a2 : ancC ns c2 y) : c1 = c2 := by
  have key : ∀ a b ra rb, ns !! a = some ra → ns !! b = some rb → ra.nv.parent' = l →
      rb.nv.parent' = l → ancC ns a b → a = b := by
    intro a b ra rb ha hb hpa hpb hab
    cases hab with
    | self => rfl
    | up _ r hr hp hup =>
      rw [hb] at hr; cases hr
      rw [hpb] at hup
      have h1 := ancC_rk ns rk N hT a l hup
      have h2 := (hT.1 a ra ha).2 (by rw [hpa]; exact hl)
      rw [hpa] at h2
      omega
  rcases ancC_cmp ns c1 y a1 c2 a2 with h | h
  · exact key c1 c2 r1 r2 h1 h2 hp1 hp2 h
  · exact (key c2 c1 r2 r1 h2 h1 hp2 hp1 h).symm

theorem ancC_child (ns : GMap Loc NRec) (l y : Loc) (h : ancC ns l y) (hne : y ≠ l) :
    ∃ c r, ns !! c = some r ∧ r.nv.parent' = l ∧ ancC ns c y := by
  induction h with
  | self => exact absurd rfl hne
  | up y r hy hp h ih =>
    by_cases e : r.nv.parent' = l
    · exact ⟨y, r, hy, e, .self⟩
    · obtain ⟨c, rc, hc, hpc, hcy⟩ := ih e
      exact ⟨c, rc, hc, hpc, .up y r hy hp hcy⟩

theorem forall2_choose {α β : Type} (P : α → β → Prop) :
    ∀ (l : List α), (∀ a ∈ l, ∃ b, P a b) → ∃ bs, List.Forall₂ P l bs
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨bs, hbs⟩ := forall2_choose P l (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))
    exact ⟨b :: bs, .cons hb hbs⟩

theorem forall2_mem_rC {α β : Type} (P : α → β → Prop) :
    ∀ (xs : List α) (bs : List β), List.Forall₂ P xs bs → ∀ b ∈ bs, ∃ a ∈ xs, P a b
  | _, _, .nil, b, hb => by cases hb
  | _, _, .cons (a := a) (b := b0) hab h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', h'⟩ := forall2_mem_rC P _ _ h b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem forall2_mem_lC {α β : Type} (P : α → β → Prop) :
    ∀ (xs : List α) (bs : List β), List.Forall₂ P xs bs → ∀ a ∈ xs, ∃ b ∈ bs, P a b
  | _, _, .nil, a, ha => by cases ha
  | _, _, .cons (a := a0) (b := b) hab h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, List.mem_cons_self, hab⟩
    · obtain ⟨b', hb', h'⟩ := forall2_mem_lC P _ _ h a ha
      exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

theorem forall2_pairwise {α β : Type} (P : α → β → Prop) (R : β → β → Prop)
    (hR : ∀ a1 a2 b1 b2, P a1 b1 → P a2 b2 → a1 ≠ a2 → R b1 b2) :
    ∀ (xs : List α) (bs : List β), List.Forall₂ P xs bs → xs.Nodup → bs.Pairwise R
  | _, _, .nil, _ => .nil
  | _, _, .cons (a := a) (b := b) hab h, hnd => by
    have hna := (List.nodup_cons.1 hnd).1
    refine List.Pairwise.cons (fun b' hb' => ?_) (forall2_pairwise P R hR _ _ h (List.nodup_cons.1 hnd).2)
    obtain ⟨a', ha', h'⟩ := forall2_mem_rC P _ _ h b' hb'
    exact hR a a' b b' hab h' (fun e => hna (e ▸ ha'))

theorem nodup_flatten' {α : Type} : ∀ (L : List (List α)), (∀ l ∈ L, l.Nodup) →
    L.Pairwise List.Disjoint → L.flatten.Nodup
  | [], _, _ => List.nodup_nil
  | S :: L, h1, h2 => by
    rw [List.flatten_cons, List.nodup_append]
    refine ⟨h1 S List.mem_cons_self, nodup_flatten' L (fun l hl => h1 l (List.mem_cons_of_mem _ hl))
      (List.pairwise_cons.1 h2).2, fun a ha b hb e => ?_⟩
    subst e
    obtain ⟨S', hS', haS'⟩ := List.mem_flatten.1 hb
    exact (List.pairwise_cons.1 h2).1 S' hS' ha haS'

/-- The subtree of a node, by strong induction on its rank. -/
theorem kidsTree_of_treeH (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (hT : treeH ns rk N) :
    ∀ n l r, ns !! l = some r → rk l < n → ∃ S, kidsTree ns l S ∧ ∀ y, y ∈ S ↔ ancC ns l y := by
  intro n
  induction n with
  | zero => intro l r _ h; omega
  | succ n ih =>
    intro l r hl hn
    obtain ⟨hcnd, hcs⟩ := hT.2.1 l r hl
    let P : Loc → List Loc → Prop := fun c S => kidsTree ns c S ∧ (∀ y, y ∈ S ↔ ancC ns c y) ∧
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
    obtain ⟨subs, hsubs⟩ := forall2_choose P r.cs hex
    have hl0 : l ≠ null := hT.2.2.2 l r hl
    have hmem : ∀ y, y ∈ l :: subs.flatten ↔ ancC ns l y := by
      intro y
      constructor
      · intro hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact .self
        · obtain ⟨S, hS, hyS⟩ := List.mem_flatten.1 hy
          obtain ⟨c, -, hcS, hm, rc, hrc, hpc⟩ := forall2_mem_rC P _ _ hsubs S hS
          have hcy := (hm y).1 hyS
          exact ancC_trans ns l c y (.up c rc hrc (by rw [hpc]; exact hl0) (by rw [hpc]; exact .self)) hcy
      · intro hy
        by_cases e : y = l
        · rw [e]; exact List.mem_cons_self
        · obtain ⟨c, rc, hrc, hpc, hcy⟩ := ancC_child ns l y hy e
          obtain ⟨rp, hrp, hcin⟩ := hT.2.2.1 c rc hrc (by rw [hpc]; exact hl0)
          rw [hpc, hl] at hrp; cases hrp
          obtain ⟨S, hS, -, hm, -⟩ := forall2_mem_lC P _ _ hsubs c hcin
          exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨S, hS, (hm y).2 hcy⟩)
    refine ⟨l :: subs.flatten, .mk l r subs hl (hsubs.imp (fun h => h.1)) ?_, hmem⟩
    refine List.nodup_cons.2 ⟨fun hlS => ?_, ?_⟩
    · obtain ⟨S, hS, hyS⟩ := List.mem_flatten.1 hlS
      obtain ⟨c, -, -, hm, rc, hrc, hpc⟩ := forall2_mem_rC P _ _ hsubs S hS
      have h1 := ancC_rk ns rk N hT c l ((hm l).1 hyS)
      have h2 := (hT.1 c rc hrc).2 (by rw [hpc]; exact hl0)
      rw [hpc] at h2; omega
    · refine nodup_flatten' _ (fun S hS => ?_) ?_
      · obtain ⟨c, -, hcS, -⟩ := forall2_mem_rC P _ _ hsubs S hS
        exact kidsTree_nodup ns c S hcS
      · refine forall2_pairwise P List.Disjoint ?_ r.cs subs hsubs hcnd
        intro a1 a2 b1 b2 hb1 hb2 hne y hy1 hy2
        obtain ⟨-, hm1, r1, hr1, hp1⟩ := hb1
        obtain ⟨-, hm2, r2, hr2, hp2⟩ := hb2
        exact hne (ancC_child_unique ns rk N hT l a1 a2 y r1 r2 hr1 hr2 hp1 hp2 hl0
          ((hm1 y).1 hy1) ((hm2 y).1 hy2))

/-- Every node is under the root (the only node without a parent). -/
theorem ancC_root (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (hT : treeH ns rk N) (rn : Loc)
    (hroot : ∀ l r, ns !! l = some r → r.nv.parent' = null → l = rn) :
    ∀ n l r, ns !! l = some r → N + 1 - rk l < n → ancC ns rn l := by
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
theorem kidsTree_root (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (hT : treeH ns rk N)
    (rn : Loc) (r0 : NRec) (h0 : ns !! rn = some r0)
    (hroot : ∀ l r, ns !! l = some r → r.nv.parent' = null → l = rn) :
    ∃ S, kidsTree ns rn S ∧ ∀ y, y ∈ S ↔ (ns !! y).isSome := by
  obtain ⟨S, hS, hm⟩ := kidsTree_of_treeH ns rk N hT (rk rn + 1) rn r0 h0 (by omega)
  refine ⟨S, hS, fun y => ⟨fun hy => ancC_some ns rk N hT rn y ((hm y).1 hy) (by rw [h0]; rfl),
    fun hy => ?_⟩⟩
  obtain ⟨ry, hry⟩ := Option.isSome_iff_exists.1 hy
  have := (hT.1 y ry hry).1
  exact (hm y).2 (ancC_root ns rk N hT rn hroot (N + 2 - rk y) y ry hry (by omega))

/-- A clean node is what `dereference` needs. -/
theorem derefOK_of_clean (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (l : Loc) (r : NRec)
    (h : nodeClean W hwm bl B l r) : derefOK bl r := by
  obtain ⟨h1, h2, -, h4, h5, -, -, -, -, h10, -⟩ := h
  refine ⟨h1, h2, fun w hw => ⟨(h5 w hw).1, (h5 w hw).2, h4 w hw⟩, ?_⟩
  rcases h10 with h | ⟨hk, hs⟩
  · exact Or.inl h
  · exact Or.inr ⟨hs, Or.inr hk⟩

/-- A clean, ranked bucket with a root node: its nodes are a tree from it, all fit for
`dereference`. -/
theorem bkt_live (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hc : bktClean W hwm bl B)
    (hk : rblKeysB W B bnd none) (hr : bktRanked B) (hrn : B.bv.rootNode' ≠ null) :
    ∃ S, liveNodesX B S ∧ ∀ l ∈ S, ∃ r, B.ns !! l = some r ∧ derefOK bl r := by
  obtain ⟨rk, N, hrk⟩ := hr
  have hcl := hc.2.2.2.2.2.2.2.1
  have h5 := hc.2.2.2.2.1
  have hT : treeH B.ns rk N := by
    refine ⟨hrk, fun l r h => ?_, fun l r h hp => ?_, fun l r h => ?_⟩
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15⟩ := hcl l r h
      exact h15
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h14, -⟩ := hcl l r h
      obtain ⟨rp, hrp, -, hin, -⟩ := h14 hp
      exact ⟨rp, hrp, hin⟩
    · obtain ⟨-, -, -, -, -, -, h7, -⟩ := hcl l r h
      exact (h5 _ _ h7).1
  obtain ⟨l0, hl0⟩ : ∃ r0, B.ns !! B.bv.rootNode' = some r0 := by
    obtain ⟨-, r0, hr0, -⟩ := h5 _ _ (hc.2.2.2.1 hrn)
    exact ⟨r0, hr0⟩
  have hroot : ∀ l r, B.ns !! l = some r → r.nv.parent' = null → l = B.bv.rootNode' := by
    intro l r h hp
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, -⟩ := hcl l r h
    exact (h13 hp).symm
  obtain ⟨S, hS, hm⟩ := kidsTree_root B.ns rk N hT B.bv.rootNode' l0 hl0 hroot
  have hp0 : l0.nv.parent' = null := hk.2.1 l0 hl0
  refine ⟨S, ⟨[B.bv.rootNode'], B.bv.rootNode', .self _ l0 hl0 hp0, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, hS,
    fun l hl hn => ?_⟩, fun l hl => ?_⟩
  · rw [List.mem_singleton] at hl; subst hl
    exact absurd ((hm _).2 (by rw [hl0]; rfl)) hn
  · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 ((hm l).1 hl)
    exact ⟨r, hr, derefOK_of_clean W hwm bl B l r (hcl l r hr)⟩

end tree

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [float_sem : go.FloatConvSemantics]

/-- The writer's view's pages, out of the database: slot-disjoint, below its high-water mark,
none at page 0 (a slot a view covers is at least 2: MVCC). -/
theorem dbWR_viewFacts (I : FLImpl (GF := GF)) (γd : DBNames) (W : WView) (txl : Loc)
    (txid : w64) (ρ : DBState) :
    dbWR I γd W txl txid ρ ⊢
      ⌜pagesDisjoint W.pages ∧ (∀ id pg, W.pages !! id = some pg → id < W.hwm) ∧
        W.pages !! 0 = none⌝ := by
  unfold dbWR
  iintro ⟨Hdb, %Hd⟩
  obtain ⟨-, -, -, -, -, w, hw, hwp, -, hwh, -, -⟩ := Hd
  isimp only [ownDB] at Hdb
  iNamed Hdb
  ipureintro
  have hr := writer_readerOK ρ v0 v1 Hok w hw
  have hm := (Hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 w hw).2
  rw [← hwp, ← hwh]
  refine ⟨hr.2.1, fun id pg h => ?_, ?_⟩
  · have h1 := (hr.2.2 id pg h).2
    have h2 := Nat.min_le_right ρ.nslots w.hwm
    unfold pageSpan at h1
    omega
  · cases h0 : w.pages !! 0 with
    | none => rfl
    | some pg =>
      have := (hm.2 0 ⟨0, pg, h0, Nat.le_refl _, by omega⟩).1
      omega

/-- The view with no dirty page. -/
theorem spillPages_nobufs (W : WView) (T : WTx) (id : Nat) :
    spillPages W { T with bufs := ∅ } !! id = W.pages !! id := by
  unfold spillPages
  rw [GMap.lookup_union, bufsN_lookup]
  split
  · simp
  · simp

/-- What `dereference` needs of the transaction, before the spill. -/
theorem derefReadyX_start (W : WView) (txl : Loc) (T : WTx) (ρ : DBState)
    (hcl : txClean W txl (structFieldRef Tx go!"root" txl) T)
    (hrk : ∀ c C, T.bs !! c = some C → bktRanked C)
    (hsh : ∀ bl B, T.bs !! bl = some B → rblKeys W B ∧ bktNested W T B)
    (hp : spillPre W txl T ρ) :
    derefReadyX T (structFieldRef Tx go!"root" txl) := by
  obtain ⟨-, -, -, -, -, -, hroot, hbs⟩ := hcl
  refine ⟨hroot, hp.1, hp.2.1, fun bl B hB => ⟨?_, (hbs bl B hB).2.2⟩⟩
  by_cases hrn : B.bv.rootNode' = null
  · exact Or.inl hrn
  · obtain ⟨bnd, hk⟩ := (hsh bl B hB).1
    exact Or.inr (bkt_live W _ bl B bnd (hbs bl B hB).2.1 hk (hrk bl B hB) hrn)

/-- From `rebalance`'s post (`rblTxOK`, `balancedFrom`, `freedOK`) and `spillPre` to
`Bucket.spill.spec`'s premises for the root bucket. The transaction's meta's high-water mark
times the page size is below 2^48 (`hpg`, as `Tx.allocate` needs; not among the facts given). -/
theorem spill_start (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8))
    (hrb : rblTxOK W (uint.nat T.mv.pgid') T)
    (hbal : balancedFrom T (structFieldRef Tx go!"root" txl))
    (hf : freedOK W ρ.fl txid F) (hp : spillPre W txl T ρ)
    (htx : T.mv.txid' = txid) (hpg : uint.Z T.mv.pgid' * W.ps < 2 ^ 48) :
    ownWriteTx W txl T ∗ txShapeR γ W T ∗ dbWR I γd W txl txid ρ ∗ pgToks γ F ⊢
      ∃ (T0 : WTx) (B : BRec) (Bs : List Loc),
        spillR I γd γ W txl txid T0 ρ F (fun _ => false) ∗
        ([∗list] c ∈ Bs, ∃ C, ⌜T0.bs !! c = some C⌝ ∗ bktToks γ W C) ∗
        ⌜spillG (hG := hG) W txl txid T0 ρ F ∧ T0.bs = T.bs ∧ T0.t = T.t ∧ T0.mv = T.mv ∧
          T0.bs !! structFieldRef Tx go!"root" txl = some B ∧ Bs.Nodup ∧
          (∀ c, c ∈ Bs ↔ bktReach T0 (structFieldRef Tx go!"root" txl) c) ∧
          (∀ c C, c ∈ Bs → T0.bs !! c = some C → bucketU W T0 (fun _ => false) c C) ∧
          W.ps < 2 ^ 20 ∧ bmUnique T0 ∧ W.pages !! 0 = none⌝ := by
  have hb : txBalanced T := txBalanced_of_reach T _ hp.1 hbal
  have hrk : ∀ c C, T.bs !! c = some C → bktRanked C :=
    fun c C hC => bktRanked_of_acyc C (hrb c C hC).2.2.1
  iintro ⟨Hown, Hsh, Hdb, HF⟩
  icases (persistent_entails_left (dbWR_viewFacts I γd W txl txid ρ)) $$ Hdb with ⟨Hdb, %Hvf⟩
  icases (persistent_entails_left (dbWR_allocUnseen I γd W txl txid ρ hp.2.2.2.2.1)) $$ Hdb
    with ⟨Hdb, %Hau⟩
  unfold ownWriteTx
  icases Hown with ⟨HG, Hv, %Hok⟩
  obtain ⟨hv, hcl⟩ := Hok
  unfold txShapeR
  icases Hsh with ⟨%M, Ha, %Hdom, Hbs, %Hfacts⟩
  have hcl' := hcl
  obtain ⟨hw, hdb, hdbn, hpm, -, hwh, hroot, hbs⟩ := hcl'
  have hDR := derefReadyX_start W txl T ρ hcl hrk Hfacts hp
  -- the transaction without dirty pages
  have hG0 : ownWriteTxG (GF := GF) W txl T ⊢ ownWriteTxG W txl { T with bufs := ∅ } := by
    unfold ownWriteTxG
    iintro ⟨Ht, Hm, Hpm, Hbufs, Hbs⟩
    iframe Ht Hm Hpm Hbs
    rw [hpm]
    iapply BigSepM.bigSepM_empty.2; iempintro
  ihave HG := hG0 $$ HG
  icases (ownWriteTxG_X W txl { T with bufs := ∅ }).1 $$ HG with ⟨HG, Hcaps⟩
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 hroot
  ihave Hl := map_list (fun _ C => bktToks (GF := GF) γ W C) T.bs.domList T.bs
    (GMap.nodup_dom_list T.bs) (fun l hl => (GMap.mem_dom_list T.bs l).1 hl) $$ Hbs
  iexists { T with bufs := ∅ }, B, T.bs.domList
  isplitl [Hdb HG Hv Hcaps Ha HF]
  · unfold spillR
    iframe
    ipureintro
    intro id
    rw [spillPages_nobufs]
    exact Hdom id
  isplitl [Hl]
  · iexact Hl
  ipureintro
  refine ⟨⟨hv, Hvf.1, Hvf.2.1, hwh, hpg, htx, hw, hdb, hdbn, fun bl B' hB' => (hbs bl B' hB').1,
      spillDirty_empty ρ W _ hpm rfl, Hau, hf, derefReadyX_bs T _ _ rfl hDR⟩,
    rfl, rfl, rfl, hB, GMap.nodup_dom_list T.bs, fun c => ?_, fun c C _ hC => ?_, hp.2.2.2.1,
    hp.2.2.2.2.2, Hvf.2.2⟩
  · rw [GMap.mem_dom_list]
    constructor
    · intro hc
      exact bktReach_bs T { T with bufs := ∅ } _ rfl c (hp.1 c hc)
    · intro hr
      induction hr with
      | root => exact hroot
      | child bl B' name c' _ hB' hc' _ => exact (hbs bl B' hB').2.2 name c' hc'
  · have hbC := hbs c C hC
    obtain ⟨hlp, hin, hthr⟩ := hp.2.2.1 c C hC
    have hcln := hbC.2.1.2.2.2.2.2.2.2.1
    refine ⟨hbC.2.1, (Hfacts c C hC).1, (Hfacts c C hC).2, hrk c C hC, hlp,
      (hrb c C hC).2.2.2, fun l r hr => ?_, hthr⟩
    obtain ⟨-, -, -, -, -, h6, -⟩ := hcln l r hr
    exact ⟨hb c C hC l r hr, h6, rfl, hin l r hr⟩

/-- After the root bucket's spill (`Bucket.spill.spec`'s post): its root page `r'` and its
written tree over the view's and the dirty pages (`spillPages`), below the high-water mark. -/
theorem spill_tree (γ : GName) (W : WView) (txl : Loc) (T T' : WTx) (B B' : BRec)
    (hvs : pagesStrict W.pages) (hpd : pagesDisjoint (spillPages W T'))
    (hpb : ∀ id pg, spillPages W T' !! id = some pg → id < uint.nat T'.mv.pgid')
    (hB : T.bs !! structFieldRef Tx go!"root" txl = some B)
    (hB' : T'.bs !! structFieldRef Tx go!"root" txl = some B')
    (hc : bktClean W (uint.nat T.mv.pgid') (structFieldRef Tx go!"root" txl) B)
    (hk : ∃ bnd, rblKeysB W B bnd none) (hht : rblHt W B) (hr0 : B.ib.root' ≠ W64 0) :
    ((⌜B.bv.rootNode' = null ∧ B'.bv = B.bv ∧ B'.ib = B.ib⌝ ∗ oldToks γ W B.ib) ∨
      (∃ (pid : w64) (top : Loc) (Q : GMap Nat (List w8)),
        ⌜B'.bv = { B.bv with rootNode' := top } ∧ B'.ib = { B.ib with root' := pid } ∧
          pid ≠ W64 0 ∧ (T'.bufs !! pid).isSome ∧ Q ⊆ spillPages W T'⌝ ∗
        wtreeQ (GF := GF) γ Q (uint.nat pid) none none)) ⊢
    wtree γ (spillPages W T') (uint.nat T'.mv.pgid') (uint.nat B'.ib.root') none none := by
  iintro (⟨%Hu, Ho⟩ | ⟨%pid, %top, %Q, %Hc, HQ⟩)
  · obtain ⟨hrn, -, hib⟩ := Hu
    rw [hib]
    unfold oldToks
    rw [if_neg hr0]
    obtain ⟨-, h2, -⟩ := hc
    obtain ⟨-, hwf⟩ := h2 hr0
    have hwf' := hwf hrn
    obtain ⟨bnd, hk1, -, -⟩ := hk
    have hkeys := hk1 hrn hr0
    have hb64 : uint.nat T.mv.pgid' ≤ 2 ^ 64 := by
      have := T.mv.pgid'.isLt; unfold uint.nat; simp; omega
    obtain ⟨-, pht, hph, -⟩ := hht
    ihave HQ := wtreeQ_old γ W.pages (uint.nat T.mv.pgid') (uint.nat B.ib.root') none none hwf'
      hvs hkeys hb64 pht hph $$ Ho
    icases HQ with ⟨HQ, -⟩
    iapply (wtree_of_Q γ _ _ _ _ none none ?_ hpd hpb) $$ HQ
    exact GMap.map_subseteq_trans (treePages_sub W.pages _) (GMap.map_union_subseteq_l _ _)
  · obtain ⟨-, hib, -, -, hsub⟩ := Hc
    rw [hib]
    iapply (wtree_of_Q γ Q _ _ _ none none hsub hpd hpb) $$ HQ

theorem spPages_eq (W W' : WView) (T : WTx) (h : W'.pages = W.pages) :
    spillPages W' T = spillPages W T := by
  unfold spillPages; rw [h]

/-- `tx.root.spill()` from `rebalance`'s post (`spill_start`, `Bucket.spill.spec`, `spill_tree`):
on success the root bucket's root page and its written tree over the view's and the dirty pages,
below the transaction's high-water mark, with the dirty pages' facts (`spillDirty`, for
`Tx.write`) and the stash of freed pages (`freedOK`); on an error, what the rollback needs. The
root bucket's root is not 0 (`hr0`: it is the meta's root page). -/
theorem spill_root (hspill : Bucket.spill.spec (GF := GF) (hG := hG))
    (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (hFS : I.FreeSpec)
    (hrb : rblTxOK W (uint.nat T.mv.pgid') T)
    (hbal : balancedFrom T (structFieldRef Tx go!"root" txl))
    (hf : freedOK W ρ.fl txid F) (hp : spillPre W txl T ρ)
    (htx : T.mv.txid' = txid) (hpg : uint.Z T.mv.pgid' * W.ps < 2 ^ 48)
    (hr0 : ∀ B, T.bs !! structFieldRef Tx go!"root" txl = some B → B.ib.root' ≠ W64 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWriteTx W txl T ∗
        txShapeR γ W T ∗ dbWR I γd W txl txid ρ ∗ pgToks γ F }}
      (App (Val (structFieldRef Tx go!"root" txl @!! go.GoType.PointerType Bucket.ty @!! go!"spill"))
        (Val #()))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ (W' : WView) (T' : WTx) (ρ' : DBState)
            (F' : GMap Nat (List w8)) (K' : Loc → Bool) (B' : BRec),
          spillR I γd γ W' txl txid T' ρ' F' K' ∗
          wtree γ (spillPages W' T') (uint.nat T'.mv.pgid') (uint.nat B'.ib.root') none none ∗
          ⌜spillG (hG := hG) W' txl txid T' ρ' F' ∧ W'.pages = W.pages ∧
            T'.bs !! structFieldRef Tx go!"root" txl = some B' ∧ spillDirty ρ' W' T' ∧
            freedOK W' ρ'.fl txid F'⌝) ∨
        (⌜err ≠ interface.nil⌝ ∗ spillErr I γd txl txid) }} := by
  iintro %Φ ⟨#Hpkg, Hpre⟩ HΦ
  icases (spill_start I γd γ W txl txid T ρ F hrb hbal hf hp htx hpg) $$ Hpre with
    ⟨%T0, %B, %Bs, HR, HBs, %Hfs⟩
  obtain ⟨hg, hbs0, -, hmv0, hB, hnd, hre, hU, hps, hbm, hp0⟩ := Hfs
  have hr0B : B.ib.root' ≠ W64 0 := hr0 B (by rw [← hbs0]; exact hB)
  have hroot : structFieldRef Tx go!"root" txl ∈ Bs := (hre _).2 bktReach.root
  obtain ⟨hc, hk, -, -, -, hht, -⟩ := hU _ B hroot hB
  iapply (hspill I γd γ W txl txid T0 ρ F (fun _ => false) _ B Bs hFS hg hbm hB hnd hre hU hps hp0)
    $$ [HR HBs]
  · iframe; iframe #
  inext
  iintro %err Hpost
  iapply HΦ
  icases Hpost with (⟨%He, %W', %T', %ρ', %F', %K', %B', HR, %Hpf, Hres⟩ | Herr)
  · ileft
    isplitr
    · ipureintro; exact He
    obtain ⟨hg', -, hWp, hB', -⟩ := Hpf
    have hg'' := hg'
    obtain ⟨hv', hvd', hvb', hwh', -, -, -, -, -, -, hdir', -, hfr', -⟩ := hg''
    obtain ⟨hpd, hpb⟩ := spillPages_disjoint ρ' W' T' hdir' hvd' hvb' hwh'
    rw [spPages_eq W W' T' hWp] at hpd hpb
    have hvs : pagesStrict W.pages := by rw [← hWp]; exact hv'.2.2.2.2
    iexists W', T', ρ', F', K', B'
    iframe HR
    rw [spPages_eq W W' T' hWp]
    isplitl [Hres]
    · iapply (spill_tree γ W txl T0 T' B B' hvs hpd hpb hB hB' hc hk hht hr0B)
      icases Hres with (Hu | ⟨%pid, %top, %Q, %Hc, HQ⟩)
      · ileft; iexact Hu
      · iright
        obtain ⟨h1, h2, -, h4, h5, h6, -⟩ := Hc
        iexists pid, top, Q
        iframe HQ
        ipureintro
        exact ⟨h1, h2, h4, h5, h6⟩
    · ipureintro
      exact ⟨hg', hWp, hB', hdir', hfr'⟩
  · iright; iexact Herr

end own

end bbolt
end EtcdGrove
end Perennial
