/-
`node.spill`'s part step (`Proof/go_etcd_io/bbolt/SpillNodeCore.lean`): the lemmas it needs.

**Freeing the node's old page** (`spDbWR_free_acc`): the freelist's state lent to `Free` (out of
the database's predicate), and back with the page pending for the writer and its token in the
stash, as `node.free` does (`Proof/go_etcd_io/bbolt/node__free_s.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.SpillNodeParts
public import Proof.go_etcd_io.bbolt.Words
public import Proof.go_etcd_io.bbolt.RebalanceDB
public import Proof.go_etcd_io.bbolt.RebalanceFree
public import Proof.go_etcd_io.bbolt.DBFree
public import Proof.go_etcd_io.bbolt.WriteDerefB
public import Spec.go_etcd_io.bbolt.internal.common.WriteInodeToPage_x

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

theorem spFree_uZN (pgid : w64) (ps : Nat) (hps : ps < 2 ^ 32)
    (h : uint.nat pgid * ps < 281474976710655) :
    uint.Z (pgid * W64 (ps : Int)) = ((uint.nat pgid * ps : Nat) : Int) := by
  have hu : uint.Z (pgid * W64 (ps : Int)) = (uint.Z pgid * uint.Z (W64 (ps : Int))) % 2 ^ 64 := by
    unfold uint.Z; rw [BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul, Int.natCast_pow]; rfl
  have e1 : uint.Z pgid = ((uint.nat pgid : Nat) : Int) := by unfold uint.nat uint.Z; simp
  have e2 : uint.Z (W64 (ps : Int)) = (ps : Int) := by word
  rw [hu, e1, e2, ← Int.natCast_mul]
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem spFree_ovN (pg : List w8) :
    uint.nat (pageOf pg).overflow' + 1 = 1 + pageOverflow pg := by
  have := rb_pageOverflow_lt pg
  simp only [pageOf]
  have : uint.nat (W32 ((pageOverflow pg : Nat) : Int)) = pageOverflow pg := by
    unfold uint.nat; rw [toNat_W32 _ this]
  omega

/-- The header of a fresh page: its id, no flags, no elements. -/
theorem spFresh_pageOf (id : w64) (n ps : Nat) (hn : 0 < n) (h32 : n ≤ 2 ^ 32) (hps : 16 ≤ ps) :
    (pageOf (freshPage id n ps)).id' = id ∧ (pageOf (freshPage id n ps)).flags' = W16 0 ∧
      (pageOf (freshPage id n ps)).count' = W16 0 := by
  have hid : pageId (freshPage id n ps) = uint.nat id := by
    unfold freshPage pageId
    rw [List.append_assoc, List.append_assoc,
      leAt_app_left _ _ 0 8 (by rw [leBytes_length']; omega),
      show uint.Z id = ((uint.nat id : Nat) : Int) from rfl,
      leAt_leBytes 8 _ (by have := id.isLt; simpa using this)]
  have h8 : (leBytes 8 (uint.Z id)).length = 8 := by rw [leBytes_length']
  have hz : ∀ k, k + 2 ≤ 4 → leAt (leBytes 4 0 ++ (leBytes 4 (((n - 1 : Nat) : Int)) ++
      List.replicate (n * ps - 16) 0)) k 2 = leAt (leBytes 4 0) k 2 := fun k hk =>
    leAt_app_left _ _ _ _ (by rw [leBytes_length']; omega)
  have hfl : pageFlags (freshPage id n ps) = 0 := by
    unfold pageFlags freshPage
    rw [List.append_assoc, List.append_assoc, leAt_app_right _ _ 8 2 (by rw [h8]; omega), h8, hz _ (by omega)]
    decide
  have hcn : pageCount (freshPage id n ps) = 0 := by
    unfold pageCount freshPage
    rw [List.append_assoc, List.append_assoc, leAt_app_right _ _ 10 2 (by rw [h8]; omega), h8, hz _ (by omega)]
    decide
  refine ⟨?_, by simp only [pageOf]; rw [hfl]; rfl, by simp only [pageOf]; rw [hcn]; rfl⟩
  simp only [pageOf]; rw [hid]
  unfold uint.nat; word

/-- The old key a part puts into its parent under: its key, or (none) its first entry's. -/
def spPartOldKey (rx : NRec) : List w8 :=
  if rx.nv.key' = slice.nil then (wHead rx.ws).key else rx.key

/-- What a part's step does to the bucket for a parent `par`: `par.put(oldKey, firstKey, nil,
pgid pg, 0)` (an entry for the part, searched at `idx`), then the part's key its first key. -/
def spParentPut (x par : Loc) (pg : w64) (B B' : BRec) : Prop :=
  B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.nm = B.nm ∧ B'.bm = B.bm ∧
  (∀ y, y ≠ x → y ≠ par → B'.ns !! y = B.ns !! y) ∧
  ∃ (rx rx' rp rp' : NRec) (idx : Nat), B.ns !! x = some rx ∧ B.ns !! par = some rp ∧
    B'.ns !! x = some rx' ∧ B'.ns !! par = some rp' ∧
    rx'.nv = { rx.nv with key' := rx'.nv.key' } ∧ rx'.ins = rx.ins ∧ rx'.cs = rx.cs ∧
    rx'.key = (wHead rx.ws).key ∧ rx'.ws.map ownFresh = rx.ws.map ownFresh ∧ wsLive rx'.ws ∧
    rx'.ksrc ≠ Src.stale ∧ rx'.nv.key' ≠ slice.nil ∧
    rp'.nv = { rp.nv with inodes' := rp'.nv.inodes' } ∧ rp'.cs = rp.cs ∧ rp'.key = rp.key ∧
    rp'.ksrc = rp.ksrc ∧ rp'.ins.length = rp'.ws.length ∧ wsLive rp'.ws ∧
    idx ≤ rp.ws.length ∧ (∀ k < idx, go.GoStringLt (wKey rp.ws k) (spPartOldKey rx)) ∧
    (idx < rp.ws.length → ¬ go.GoStringLt (wKey rp.ws idx) (spPartOldKey rx)) ∧
    rp'.ws.map ownFresh = (putList rp.ws idx
      (decide (idx < rp.ws.length ∧ wKey rp.ws idx = spPartOldKey rx))
      (⟨W32 0, pg, (wHead rx.ws).key, [], Src.own (DFrac.own 1), Src.own (DFrac.own 1)⟩ : WEntry)).map
      ownFresh

theorem spKidsTree_mem (ns : GMap Loc NRec) (t : Loc) (S : List Loc) (h : kidsTree ns t S) :
    t ∈ S ∧ S.Nodup := by
  cases h with
  | mk _ r subs hr hf hnd => exact ⟨List.mem_cons_self .., hnd⟩

/-- A node is not its own child. -/
theorem spKids_notin (ns : GMap Loc NRec) (n : Loc) (cs : List Loc) (sub : Loc → List Loc)
    (hk : kidsTree ns n (n :: (cs.map sub).flatten)) (hc : ∀ c ∈ cs, kidsTree ns c (sub c)) :
    n ∉ cs := by
  intro hm
  have hnd := (spKidsTree_mem _ _ _ hk).2
  have h1 := (spKidsTree_mem _ _ _ (hc n hm)).1
  have : n ∈ (cs.map sub).flatten := List.mem_flatten.2 ⟨sub n, List.mem_map_of_mem hm, h1⟩
  exact (List.nodup_cons.1 hnd).1 this

/-- The children of a node in its children loop: records with entries (what `sort.Sort` reads). -/
theorem spKids_ok (W : WView) (bl : Loc) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (kd : Loc → Nat) (K : Loc → Bool) (N : Nat) (n : Loc) (r : NRec) (sp : Loc → Bool)
    (sub : Loc → List Loc) (hnn : n ≠ null) (hL : nodeL W bl B bnd kd n r)
    (hch : ∀ c ∈ r.cs, kidsTree B.ns c (sub c) ∧ (sp c = true → spilledN bl B c) ∧
      (sp c = false → (sub c).length < N ∧ subU W bl B bnd kd K c (sub c)))
    (hne : ∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → 0 < r.ws.length) :
    ∀ c ∈ r.cs, ∃ rc, B.ns !! c = some rc ∧ 0 < rc.ws.length ∧ rc.ins.length = rc.ws.length ∧
      wsLive rc.ws := by
  intro c hc
  cases hsp : sp c with
  | false =>
    obtain ⟨hkt, hU⟩ := ((hch c hc).2.2 hsp).2
    obtain ⟨-, rc, hrc, hu⟩ := hU c (spKidsTree_mem _ _ _ hkt).1
    refine ⟨rc, hrc, ?_, hu.2.2.1, hu.2.2.2.2.2.1⟩
    cases hl : r.nv.isLeaf' with
    | false =>
      obtain ⟨-, -, -, hmap, hcs⟩ := hL.2.2.2.2.2.2.2.2.2 hl
      rcases hcs c hc with ⟨i, w, hw, hnm⟩ | hspl
      · obtain ⟨rc', hrc', hpar, -⟩ := hmap i w c hw hnm
        rw [hrc] at hrc'; cases hrc'
        exact hne c rc hrc (by rw [hpar]; exact hnn)
      · obtain ⟨rc', hrc', hs, -⟩ := hspl
        rw [hrc] at hrc'; cases hrc'; rw [hu.2.1] at hs; cases hs
    | true => rw [hL.2.2.2.2.2.2.2.2.1 hl] at hc; cases hc
  | true =>
    obtain ⟨rc, hrc, -, -, -, hpos, hlen, hd⟩ := (hch c hc).2.1 hsp
    exact ⟨rc, hrc, by omega, hlen, fun w hw => ⟨(hd.1.2.2.1 w hw).1, (hd.1.2.2.1 w hw).2.1⟩⟩

/-- A node's children are distinct. -/
theorem spCs_nodup (W : WView) (bl : Loc) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (kd : Loc → Nat) (n : Loc) (r : NRec) (hL : nodeL W bl B bnd kd n r) : r.cs.Nodup := by
  cases hl : r.nv.isLeaf' with
  | false => exact (hL.2.2.2.2.2.2.2.2.2 hl).2.2.1
  | true => rw [hL.2.2.2.2.2.2.2.2.1 hl]; exact List.nodup_nil

/-- A node is in none of its children's trees. -/
theorem spKids_notsub (ns : GMap Loc NRec) (n : Loc) (cs : List Loc) (sub : Loc → List Loc)
    (hk : kidsTree ns n (n :: (cs.map sub).flatten)) : ∀ c ∈ cs, n ∉ sub c := by
  intro c hc hm
  have hnd := (spKidsTree_mem _ _ _ hk).2
  exact (List.nodup_cons.1 hnd).1 (List.mem_flatten.2 ⟨sub c, List.mem_map_of_mem hc, hm⟩)

theorem spF2_mem_r {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ b ∈ l2, ∃ a ∈ l1, R a b
  | [], [], .nil, b, h => by simp at h
  | a :: _, _ :: _, .cons hab ht, b, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨a, List.mem_cons_self .., hab⟩
    · obtain ⟨a', ha', hr⟩ := spF2_mem_r ht b h
      exact ⟨a', List.mem_cons_of_mem _ ha', hr⟩

theorem spF2_mem_l {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ a ∈ l1, ∃ b ∈ l2, R a b
  | [], [], .nil, a, h => by simp at h
  | _ :: _, b :: _, .cons hab ht, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨b, List.mem_cons_self .., hab⟩
    · obtain ⟨b', hb', hr⟩ := spF2_mem_l ht a h
      exact ⟨b', List.mem_cons_of_mem _ hb', hr⟩

theorem spF2_imp_mem {α β : Type} {R R' : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → (∀ a b, b ∈ l2 → R a b → R' a b) →
      List.Forall₂ R' l1 l2
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons hab ht, h =>
    .cons (h _ _ (List.mem_cons_self ..) hab)
      (spF2_imp_mem ht (fun a b hb hr => h a b (List.mem_cons_of_mem _ hb) hr))

theorem spF2_exists {α β : Type} {R R' : α → β → Prop} {P : β → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
      (∀ a b, b ∈ l2 → R a b → ∃ b', R' a b' ∧ P b b') →
      ∃ l2', List.Forall₂ R' l1 l2' ∧ List.Forall₂ P l2 l2'
  | [], [], .nil, _ => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, .cons hab ht, h => by
    obtain ⟨b', h1, h2⟩ := h _ _ (List.mem_cons_self ..) hab
    obtain ⟨l', h3, h4⟩ := spF2_exists ht (fun a b hb hr => h a b (List.mem_cons_of_mem _ hb) hr)
    exact ⟨b' :: l', .cons h1 h3, .cons h2 h4⟩

theorem spF2_perm {α β : Type} {R : α → β → Prop} {l1' l1 : List α} (hp : l1'.Perm l1) :
    ∀ {l2 : List β}, List.Forall₂ R l1 l2 → ∃ l2', List.Forall₂ R l1' l2' ∧ l2'.Perm l2 := by
  induction hp with
  | nil => intro l2 h; cases h; exact ⟨[], .nil, .nil⟩
  | cons x _ ih =>
    intro l2 h
    cases h with
    | cons hab ht =>
      obtain ⟨l', h1, h2⟩ := ih ht
      exact ⟨_, .cons hab h1, h2.cons _⟩
  | swap x y l =>
    intro l2 h
    cases h with
    | cons hab ht =>
      cases ht with
      | cons hab' ht' => exact ⟨_, .cons hab' (.cons hab ht'), List.Perm.swap _ _ _⟩
  | trans _ _ ih1 ih2 =>
    intro l2 h
    obtain ⟨l', h1, h2⟩ := ih2 h
    obtain ⟨l'', h3, h4⟩ := ih1 h1
    exact ⟨l'', h3, h4.trans h2⟩

theorem spF2_perm_flatten {α : Type} : ∀ {l1 l2 : List (List α)}, List.Forall₂ List.Perm l1 l2 →
    l1.flatten.Perm l2.flatten
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hab ht => by
    simp only [List.flatten_cons]; exact hab.append (spF2_perm_flatten ht)

theorem spLen_le_flatten {α : Type} : ∀ (L : List (List α)) (x : List α), x ∈ L →
    x.length ≤ L.flatten.length
  | [], _, h => by simp at h
  | a :: L, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp only [List.flatten_cons, List.length_append]; omega
    · have := spLen_le_flatten L x h; simp only [List.flatten_cons, List.length_append]; omega

/-- A node's children are in its tree. -/
theorem spKidsTree_cs (ns : GMap Loc NRec) : ∀ (N : Nat) (t : Loc) (S : List Loc), S.length ≤ N →
    kidsTree ns t S → ∀ x ∈ S, ∀ rx, ns !! x = some rx → ∀ c ∈ rx.cs, c ∈ S := by
  intro N
  induction N with
  | zero => intro t S hl hk; cases hk with | mk _ r subs hr hf hnd => simp at hl
  | succ N ih =>
    intro t S hl hk
    cases hk with
    | mk _ r subs hr hf hnd =>
      intro x hx rx hrx c hc
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hr] at hrx; cases hrx
        obtain ⟨s, hs, hks⟩ := spF2_mem_l hf c hc
        exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨s, hs, (spKidsTree_mem _ _ _ hks).1⟩)
      · obtain ⟨s, hs, hxs⟩ := List.mem_flatten.1 hx
        obtain ⟨c0, -, hk0⟩ := spF2_mem_r hf s hs
        have hsl : s.length ≤ N := by
          have := spLen_le_flatten subs s hs; simp only [List.length_cons] at hl; omega
        exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨s, hs, ih c0 s hsl hk0 x hxs rx hrx c hc⟩)

/-- A tree of nodes kept when a node outside it changes. -/
theorem spKidsTree_ins (ns : GMap Loc NRec) (n : Loc) (x : NRec) (t : Loc) (S : List Loc)
    (hk : kidsTree ns t S) (hn : n ∉ S) : kidsTree (<[n := x]> ns) t S := by
  obtain ⟨S', hk', hg⟩ := kidsTree_graft ns (<[n := x]> ns) n [] (fun y hy => by simp at hy)
    List.nodup_nil S.length t S (Nat.le_refl _) hk
    (fun l _ hne r h => ⟨r, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact h, rfl⟩)
    (fun h => absurd h hn) (fun y hy => by simp at hy)
  rw [hg.2 hn] at hk'; exact hk'

/-- A tree of nodes, a node's children permuted: the same nodes. -/
theorem spKidsTree_perm (ns : GMap Loc NRec) (n : Loc) (r : NRec) (ys : List Loc)
    (hn : ns !! n = some r) (hp : ys.Perm r.cs) :
    ∀ (N : Nat) (t : Loc) (S : List Loc), S.length ≤ N → kidsTree ns t S →
      ∃ S', kidsTree (<[n := { r with cs := ys }]> ns) t S' ∧ S'.Perm S := by
  intro N
  induction N with
  | zero => intro t S hl hk; cases hk with | mk _ r subs hr hf hnd => simp at hl
  | succ N ih =>
    intro t S hl hk
    cases hk with
    | mk _ rt subs hr hf hnd =>
      by_cases e : t = n
      · subst e
        rw [hn] at hr; cases hr
        have hns : ∀ s ∈ subs, t ∉ s := fun s hs hm =>
          (List.nodup_cons.1 hnd).1 (List.mem_flatten.2 ⟨s, hs, hm⟩)
        have hf' : List.Forall₂ (kidsTree (<[t := { r with cs := ys }]> ns)) r.cs subs :=
          spF2_imp_mem hf (fun a b hb hk => spKidsTree_ins ns t _ a b hk (hns b hb))
        obtain ⟨subs', h1, h2⟩ := spF2_perm hp hf'
        have hpf : (t :: subs'.flatten).Perm (t :: subs.flatten) := (List.Perm.flatten h2).cons t
        refine ⟨t :: subs'.flatten, kidsTree.mk t _ subs' (GMap.lookup_insert _ _ _) h1
          (hpf.nodup_iff.2 hnd), hpf⟩
      · have hf2 : ∀ a b, b ∈ subs → kidsTree ns a b →
            ∃ b', kidsTree (<[n := { r with cs := ys }]> ns) a b' ∧ List.Perm b b' := by
          intro a b hb hk
          have hbl : b.length ≤ N := by
            have := spLen_le_flatten subs b hb; simp only [List.length_cons] at hl; omega
          obtain ⟨b', h1, h2⟩ := ih a b hbl hk
          exact ⟨b', h1, h2.symm⟩
        obtain ⟨subs', h1, h2⟩ := spF2_exists hf hf2
        have hpf : (t :: subs'.flatten).Perm (t :: subs.flatten) := ((spF2_perm_flatten h2).symm).cons t
        refine ⟨t :: subs'.flatten, kidsTree.mk t rt subs' ?_ h1 (hpf.nodup_iff.2 hnd), hpf⟩
        rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hr

/-- A node in its children loop is readable by `dereference`. -/
theorem spDerefOK_nodeL (W : WView) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (kd : Loc → Nat) (n : Loc) (r : NRec)
    (hL : nodeL W bl B bnd kd n r) : derefOK bl r := by
  obtain ⟨h1, -, h3, -, h5, h6, h7, -⟩ := hL
  refine ⟨h1, h3, fun w hw => ⟨(h6 w hw).1, (h6 w hw).2, (h5 w hw).1⟩, ?_⟩
  rcases h7 with h | ⟨hk, hs⟩
  · exact Or.inl h
  · exact Or.inr ⟨hs, Or.inr hk⟩

/-- A part's layout (`layoutOf`), from its entries' bytes. -/
def spLayoutW (ws : List WEntry) : Nat :=
  16 + 16 * ws.length + (ws.map (fun w => w.key.length + w.value.length)).sum

theorem spLayoutW_fresh (ws : List WEntry) : spLayoutW (ws.map ownFresh) = spLayoutW ws := by
  unfold spLayoutW; simp only [List.length_map, List.map_map]; rfl

theorem spLayout_eq : ∀ (ins : List Inode) (ws : List WEntry), ins.length = ws.length →
    (∀ (i : Nat) (it : Inode) (w : WEntry), ins[i]? = some it → ws[i]? = some w →
      uint.nat it.key'.len = w.key.length ∧ uint.nat it.value'.len = w.value.length) →
    layoutOf ins = spLayoutW ws
  | [], [], _, _ => rfl
  | it :: ins, w :: ws, hl, h => by
    have ih := spLayout_eq ins ws (by simpa using hl) (fun i it' w' h1 h2 => h (i + 1) it' w' h1 h2)
    have h0 := h 0 it w rfl rfl
    unfold layoutOf at ih ⊢; unfold spLayoutW at ih ⊢
    simp only [List.length_cons, List.map_cons, List.sum_cons, inodeKV] at ih ⊢
    omega
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem spSizeFrom_nat : ∀ (ins : List Inode) (off : w64),
    uint.nat off + 16 * ins.length + (ins.map inodeKV).sum < 2 ^ 64 →
    uint.nat (sizeFrom (W64 16) off ins) = uint.nat off + 16 * ins.length + (ins.map inodeKV).sum
  | [], off, _ => by simp [sizeFrom]
  | it :: ins, off, h => by
    have e : sizeFrom (W64 16) off (it :: ins) =
        sizeFrom (W64 16) (off + (W64 16 + it.key'.len + it.value'.len)) ins := rfl
    simp only [List.length_cons, List.map_cons, List.sum_cons] at h
    have hkv : inodeKV it = uint.nat it.key'.len + uint.nat it.value'.len := rfl
    have hstep : uint.nat (off + (W64 16 + it.key'.len + it.value'.len)) =
        uint.nat off + 16 + uint.nat it.key'.len + uint.nat it.value'.len := by
      rw [hkv] at h; unfold uint.nat at h ⊢; word
    rw [e, spSizeFrom_nat ins _ (by rw [hstep]; omega), hstep]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- The pages of a part of layout `S` (`(S + ps - 1) / ps`): at least one, and they fit. -/
theorem spCount_bounds (sz : w64) (ps S : Nat) (hsz : uint.nat sz = S) (h16 : 16 ≤ S)
    (hS : S ≤ 2147483647) (hp16 : 16 ≤ ps) (hps : ps < 2 ^ 20) :
    0 < sint.Z (BitVec.sdiv (sz + W64 (ps : Int) - W64 1) (W64 (ps : Int))) ∧
    sint.Z (BitVec.sdiv (sz + W64 (ps : Int) - W64 1) (W64 (ps : Int))) ≤ 2 ^ 32 ∧
    sint.Z (BitVec.sdiv (sz + W64 (ps : Int) - W64 1) (W64 (ps : Int))) * ps < 2 ^ 47 ∧
    (S : Int) ≤ sint.Z (BitVec.sdiv (sz + W64 (ps : Int) - W64 1) (W64 (ps : Int))) * ps := by
  have ha : sint.Z (sz + W64 (ps : Int) - W64 1) = ((S + ps - 1 : Nat) : Int) := by
    unfold uint.nat at hsz; word
  have hb : sint.Z (W64 (ps : Int)) = (ps : Int) := by word
  rw [sint_sdiv _ _ (by rw [ha]; omega) (by rw [hb]; omega), ha, hb]
  rw [← Int.natCast_ediv]
  have h1 : 0 < (S + ps - 1) / ps := Nat.div_pos (by omega) (by omega)
  have h2 : (S + ps - 1) / ps ≤ S + ps - 1 := Nat.div_le_self _ _
  have h3 : (S + ps - 1) / ps * ps ≤ S + ps - 1 := Nat.div_mul_le_self _ _
  have h4 := Nat.div_add_mod (S + ps - 1) ps
  have h5 := Nat.mod_lt (S + ps - 1) (show ps > 0 by omega)
  have hc : ps * ((S + ps - 1) / ps) = (S + ps - 1) / ps * ps := Nat.mul_comm _ _
  generalize hq : (S + ps - 1) / ps = q at h1 h2 h3 h4 hc
  generalize hr : (S + ps - 1) % ps = rr at h4 h5
  generalize hm : q * ps = m at h3 hc
  rw [hc] at h4
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [← Int.natCast_mul, hm]; omega
  · rw [← Int.natCast_mul, hm]; omega

/-- The top's root path, its children sorted. -/
theorem spTopP (B : BRec) (n : Loc) (r : NRec) (ys : List Loc) (p : List Loc)
    (hn : B.ns !! n = some r) (hperm : ys.Perm r.cs) (hu : upPath B.ns B.bv.rootNode' p n)
    (hdom : ∀ l, (B.ns !! l).isSome → l ∈ p ∨ l ∈ r.cs)
    (hpv : ∀ l ∈ p, l = n ∨ l ∈ r.cs ∨ ∃ r', B.ns !! l = some r' ∧ noViewRec r') :
    upPath (setN B n { r with cs := ys }).ns B.bv.rootNode' p n ∧
    (∀ l, ((setN B n { r with cs := ys }).ns !! l).isSome → l ∈ p ∨ l ∈ ys) ∧
    (∀ l ∈ p, l = n ∨ l ∈ ys ∨ ∃ r', (setN B n { r with cs := ys }).ns !! l = some r' ∧ noViewRec r') := by
  have hne : ∀ l, l ≠ n → (setN B n { r with cs := ys }).ns !! l = B.ns !! l := fun l e =>
    GMap.lookup_insert_ne _ _ (Ne.symm e)
  refine ⟨upPath_par _ _ hu (fun x _ rx hrx => ?_), fun l hl => ?_, fun l hl => ?_⟩
  · by_cases e : x = n
    · subst e; rw [hn] at hrx; cases hrx
      exact ⟨_, GMap.lookup_insert _ _ _, rfl⟩
    · exact ⟨rx, by rw [hne x e]; exact hrx, rfl⟩
  · by_cases e : l = n
    · subst e; exact Or.inl (upPath_last_mem _ hu)
    · rw [hne l e] at hl
      rcases hdom l hl with h | h
      · exact Or.inl h
      · exact Or.inr (hperm.mem_iff.2 h)
  · rcases hpv l hl with h | h | ⟨r', hr', hv⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl (hperm.mem_iff.2 h))
    · by_cases e : l = n
      · exact Or.inl e
      · exact Or.inr (Or.inr ⟨r', by rw [hne l e]; exact hr', hv⟩)

/-- The first part's page id, its record (possibly dereferenced): the node's. -/
theorem spFirstPart (bl n : Loc) (rc : NRec) (xs : List (Loc × node × List Inode)) (par : Loc)
    (Bs : BRec) (ws0 : List WEntry) (i0 : Nat) (hst : startP bl n rc xs par Bs ws0 i0) (x : Loc)
    (hx : (xs[0]?).map (fun x => x.1) = some x) (rs rx : NRec) (hrs : Bs.ns !! x = some rs)
    (hdn : dnK rs rx) : rx.nv.pgid' = rc.nv.pgid' := by
  obtain ⟨-, -, -, -, -, -, -, hpr, -, hhd, -⟩ := hst
  obtain ⟨xe, hxe, rfl⟩ : ∃ xe, xs[0]? = some xe ∧ xe.1 = x := by
    cases h : xs[0]? with
    | none => rw [h] at hx; cases hx
    | some xe => rw [h] at hx; cases hx; exact ⟨xe, rfl, rfl⟩
  have h1 := hpr 0 xe hxe
  rw [hrs] at h1; cases h1
  have hh := hhd xe (by rw [List.head?_eq_getElem?]; exact hxe)
  have hpg : (partRec rc 0 xe ((chunksOf rc xs).getD 0 [])).nv.pgid' = rc.nv.pgid' := by
    simp only [partRec, ↓reduceIte]; rw [hh]
  rcases hdn with h | ⟨-, hnv⟩
  · rw [h]; exact hpg
  · rw [hnv]; exact hpg

/-- A relation of the inodes and the entries, pointwise, holds of each piece and its chunk. -/
theorem spChunk_rel {R : Inode → WEntry → Prop} : ∀ (L : List (List Inode)) (ws : List WEntry),
    (∀ (i : Nat) (it : Inode) (w : WEntry), L.flatten[i]? = some it → ws[i]? = some w → R it w) →
    ∀ (j : Nat) (part : List Inode), L[j]? = some part →
      ∀ (i : Nat) (it : Inode) (w : WEntry), part[i]? = some it →
        ((wsChunks ws (L.map List.length)).getD j [])[i]? = some w → R it w
  | [], _, _, j, part, h, _, _, _, _, _ => by simp at h
  | p :: L, ws, h, 0, part, hj, i, it, w, hit, hw => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
    simp only [List.map_cons, wsChunks, List.getD_cons_zero] at hw
    have hi : i < p.length := (List.getElem?_eq_some_iff.1 hit).1
    simp only [List.getElem?_take, hi, ↓reduceIte] at hw
    refine h i it w ?_ hw
    simp only [List.flatten_cons]; rw [List.getElem?_append_left hi]; exact hit
  | p :: L, ws, h, j + 1, part, hj, i, it, w, hit, hw => by
    simp only [List.getElem?_cons_succ] at hj
    simp only [List.map_cons, wsChunks, List.getD_cons_succ] at hw
    refine spChunk_rel L (ws.drop p.length) (fun i' it' w' h1 h2 => ?_) j part hj i it w hit hw
    refine h (p.length + i') it' w' ?_ ?_
    · simp only [List.flatten_cons]
      rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]; exact h1
    · rw [List.getElem?_drop] at h2; exact h2

theorem spUpPath_head (ns : GMap Loc NRec) {l : Loc} {p : List Loc} {t : Loc} (h : upPath ns l p t) :
    ∃ r, ns !! l = some r := by
  cases h with
  | self _ r hr _ => exact ⟨r, hr⟩
  | up _ r _ _ hr _ _ => exact ⟨r, hr⟩

/-- An allocation (possibly a remap first): a live node of the bucket kept, dereferenced. -/
theorem spAllocPart (bl x : Loc) (T3 T0 : WTx) (B3 : BRec) (rx3 : NRec) (S : List Loc)
    (hT3 : T3.bs !! bl = some B3) (hx3 : B3.ns !! x = some rx3)
    (hT0 : T0 = T3 ∨ (derefRelX T3 T0 ∧ derefKeep T3 T0))
    (hlv : liveNodesX B3 S) (hok : ∀ l ∈ S, ∃ r, B3.ns !! l = some r ∧ derefOK bl r) (hxS : x ∈ S)
    (hrn : B3.bv.rootNode' ≠ null) (hnvS : ∀ l r, B3.ns !! l = some r → l ∉ S → noViewRec r) :
    ∃ B4 rx4, T0.bs !! bl = some B4 ∧ B4.ns !! x = some rx4 ∧ dnK rx3 rx4 ∧ liveNodesX B4 S ∧
      (∀ l ∈ S, ∃ r, B4.ns !! l = some r ∧ derefOK bl r) ∧
      B4.bv = B3.bv ∧ B4.ib = B3.ib ∧ B4.nm = B3.nm ∧ B4.bm = B3.bm ∧
      (∀ l r4, B4.ns !! l = some r4 → ∃ r, B3.ns !! l = some r ∧ dnK r r4) ∧
      (∀ l r3, B3.ns !! l = some r3 → ∃ r4, B4.ns !! l = some r4 ∧ dnK r3 r4) ∧
      (∀ l r, B4.ns !! l = some r → l ∉ S → noViewRec r) := by
  rcases hT0 with rfl | ⟨hd, hk⟩
  · exact ⟨B3, rx3, hT3, hx3, Or.inl rfl, hlv, hok, rfl, rfl, rfl, rfl,
      fun l r4 h => ⟨r4, h, Or.inl rfl⟩, fun l r3 h => ⟨r3, h, Or.inl rfl⟩, hnvS⟩
  · obtain ⟨B0, hB0⟩ := Option.isSome_iff_exists.1 ((hd.2.2.2.2.1 bl).1 (by rw [hT3]; rfl))
    have hdb := hd.2.2.2.2.2 bl B3 B0 hT3 hB0
    obtain ⟨hlv0, hall⟩ := live_deref bl B3 B0 hdb hrn S hlv hok
    obtain ⟨r, r0, hr, hr0, -, hdx⟩ := hall x hxS
    rw [hx3] at hr; cases hr
    have hkp := hk bl B3 B0 x rx3 r0 hT3 hB0 hx3 hr0
    have hback : ∀ l r4, B0.ns !! l = some r4 → ∃ r, B3.ns !! l = some r ∧ dnK r r4 := by
      intro l r4 h4
      obtain ⟨r, hr, hdx'⟩ := hdb.2.2.2.2.2.2.1 l r4 h4
      have := hk bl B3 B0 l r r4 hT3 hB0 hr h4
      refine ⟨r, hr, ?_⟩
      by_cases hl : l ∈ S
      · obtain ⟨r', r0', hr', h0', -, hdl⟩ := hall l hl
        rw [hr] at hr'; cases hr'
        rw [h4] at h0'; cases h0'
        rcases hdl with h | ⟨rfl, -⟩
        · exact Or.inr ⟨h, this⟩
        · exact Or.inl rfl
      · rcases hdx' with h | ⟨rfl, -⟩ | rfl
        · exact Or.inr ⟨h, this⟩
        · exact Or.inl rfl
        · exact Or.inl (staleRec_of_noView r (hnvS l r hr hl))
    refine ⟨B0, r0, hB0, hr0, ?_, hlv0, fun l hl => ?_, hdb.1, hdb.2.1, hdb.2.2.1, hdb.2.2.2.1,
      hback, fun l r3 h3 => ?_, fun l r4 h4 hl => ?_⟩
    · rcases hdx with h | ⟨rfl, -⟩
      · exact Or.inr ⟨h, hkp⟩
      · exact Or.inl rfl
    · obtain ⟨_, r0', -, h, hok', -⟩ := hall l hl
      exact ⟨r0', h, hok'⟩
    · obtain ⟨r4, h4⟩ := Option.isSome_iff_exists.1 (hdb.2.2.2.2.2.2.2.2 l (by rw [h3]; rfl))
      obtain ⟨r, hr, hd'⟩ := hback l r4 h4
      rw [h3] at hr; cases hr
      exact ⟨r4, h4, hd'⟩
    · obtain ⟨r, hr, hdx'⟩ := hdb.2.2.2.2.2.2.1 l r4 h4
      exact dnX3_noView r r4 hdx'

/-- The current part's record (its split record, possibly dereferenced): its chunk's entries. -/
theorem spCurPart (bl n : Loc) (rc : NRec) (xs : List (Loc × node × List Inode)) (par : Loc)
    (Bs : BRec) (ws0 : List WEntry) (i0 : Nat) (hst : startP bl n rc xs par Bs ws0 i0)
    (hil : rc.ins.length = rc.ws.length) (hlive : wsLive rc.ws) (j : Nat)
    (xe : Loc × node × List Inode) (hxe : xs[j]? = some xe) (rs rx : NRec)
    (hrs : Bs.ns !! xe.1 = some rs) (hdn : dnK rs rx) :
    rx.ws.map ownFresh = ((chunksOf rc xs).getD j []).map ownFresh ∧ wsLive rx.ws ∧
      rx.ins.length = rx.ws.length ∧ rx.ws.length = xe.2.2.length ∧
      ∀ w ∈ (chunksOf rc xs).getD j [], w ∈ rc.ws := by
  obtain ⟨-, -, -, hflat, -, -, -, hpr, -⟩ := hst
  have h1 := hpr j xe hxe
  rw [hrs] at h1; cases h1
  have hws : (partRec rc j xe ((chunksOf rc xs).getD j [])).ws = (chunksOf rc xs).getD j [] := by
    unfold partRec; split <;> rfl
  have hins : (partRec rc j xe ((chunksOf rc xs).getD j [])).ins = xe.2.2 := by
    unfold partRec; split <;> rfl
  have hsum : (xs.map (fun x => x.2.2.length)).sum ≤ rc.ws.length := by
    rw [← hil, ← hflat.1, List.length_flatten, List.map_map]; exact Nat.le_refl _
  have hk : (xs.map (fun x => x.2.2.length))[j]? = some xe.2.2.length := by
    rw [List.getElem?_map, hxe]; rfl
  obtain ⟨hlen, hmem⟩ := wsChunks_get rc.ws _ j _ hk hsum
  have hlen' : ((chunksOf rc xs).getD j []).length = xe.2.2.length := hlen
  have hmem' : ∀ w ∈ (chunksOf rc xs).getD j [], w ∈ rc.ws := hmem
  rcases hdn with h | ⟨⟨⟨-, hws', -, -, -, -, hil'⟩, -⟩, -⟩
  · rw [h]
    refine ⟨by rw [hws], fun w hw => hlive w (hmem' w (by rw [hws] at hw; exact hw)), ?_, ?_⟩
    · rw [hins, hws, hlen']
    · exact ⟨by rw [hws, hlen'], hmem'⟩
  · refine ⟨?_, fun w hw => ?_, hil', ?_⟩
    · rw [hws', hws, List.map_map]; rfl
    · rw [hws'] at hw
      obtain ⟨w0, -, rfl⟩ := List.mem_map.1 hw
      exact ⟨nofun, nofun⟩
    · exact ⟨by rw [hws', List.length_map, hws, hlen'], hmem'⟩

/-- What a node kept or dereferenced (`dnK`) keeps. -/
theorem spDnK_facts (r r' : NRec) (h : dnK r r') :
    (wsLive r.ws → wsLive r'.ws) ∧ (r.ins.length = r.ws.length → r'.ins.length = r'.ws.length) ∧
    r'.ws.map ownFresh = r.ws.map ownFresh ∧ r'.nv = { r.nv with key' := r'.nv.key' } ∧
    r'.cs = r.cs ∧ r'.key = r.key ∧ r'.ws.length = r.ws.length ∧
    (r.ksrc ≠ Src.stale → r'.ksrc ≠ Src.stale) ∧ (r.nv.key' = slice.nil → r'.nv.key' = slice.nil) := by
  rcases h with rfl | ⟨⟨⟨-, hws, hcs, hkey, hkn, hks, hil⟩, -⟩, hnv⟩
  · exact ⟨id, id, rfl, rfl, rfl, rfl, rfl, id, id⟩
  · refine ⟨fun _ w hw => ?_, fun _ => hil, ?_, hnv, hcs, hkey, by rw [hws, List.length_map],
      fun _ => by rw [hks]; exact nofun, hkn⟩
    · rw [hws] at hw
      obtain ⟨w0, -, rfl⟩ := List.mem_map.1 hw
      exact ⟨nofun, nofun⟩
    · rw [hws, List.map_map]; rfl

theorem spBorrowEs_length : ∀ (ws : List WEntry) (q : Qp), (borrowEs ws q).length = ws.length
  | [], _ => rfl
  | w :: ws, q => by simp only [borrowEs, List.length_cons, spBorrowEs_length ws q.half]

/-- The entries' keys and values' bytes, `kvLen` of them. -/
theorem spKvLen : ∀ (ws : List WEntry),
    kvLen (ws.map WEntry.key) (ws.map WEntry.value) ws.length =
      (ws.map (fun w => w.key.length + w.value.length)).sum
  | [] => rfl
  | w :: ws => by
    have ih := spKvLen ws
    unfold kvLen at ih ⊢
    simp only [List.map_cons, List.zipWith_cons_cons, List.length_cons, List.take_succ_cons,
      List.sum_cons] at ih ⊢
    rw [ih]

theorem spBorrowEs_kv : ∀ (ws : List WEntry) (q : Qp),
    (borrowEs ws q).map NodeEntry.key = ws.map WEntry.key ∧
      (borrowEs ws q).map NodeEntry.value = ws.map WEntry.value
  | [], _ => ⟨rfl, rfl⟩
  | w :: ws, q => by
    obtain ⟨h1, h2⟩ := spBorrowEs_kv ws q.half
    simp only [borrowEs, List.map_cons, h1, h2]; exact ⟨trivial, trivial⟩

theorem spFresh_key (ws : List WEntry) : (ws.map ownFresh).map WEntry.key = ws.map WEntry.key := by
  rw [List.map_map]; rfl

theorem spFresh_value (ws : List WEntry) :
    (ws.map ownFresh).map WEntry.value = ws.map WEntry.value := by
  rw [List.map_map]; rfl

theorem spFresh_pgid (ws : List WEntry) : (ws.map ownFresh).map WEntry.pgid = ws.map WEntry.pgid := by
  rw [List.map_map]; rfl

/-- Every part of the split is a leaf if the node is. -/
theorem spPartLeaf (bl n : Loc) (rc rp : NRec) (xs : List (Loc × node × List Inode)) (T : WTx)
    (B : BRec) (K : Loc → Bool) (Ts : WTx) (Bs : BRec) (Ks : Loc → Bool) (par : Loc)
    (hsr : splitRes bl n rc rp xs T B K Ts Bs Ks par) :
    ∀ x ∈ xs, x.2.1.isLeaf' = rc.nv.isLeaf' := by
  intro x hx
  rcases hsr with ⟨rfl, -⟩ | ⟨pv', pcs', st, -, hsp, -⟩
  · simp at hx; subst hx; rfl
  · obtain ⟨-, ⟨x0, rest, rfl, -, h0, hrest⟩, -⟩ := hsp
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [h0]
    · rw [(hrest x hx).2]

theorem spGetD_pos (l : List (List w8)) (h : ∀ k ∈ l, 0 < k.length) :
    ∀ i < l.length, 0 < (l.getD i []).length := by
  intro i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact h _ (List.getElem_mem hi)

/-- The current part (its split record, possibly dereferenced) is a leaf if the node is. -/
theorem spCurPartLeaf (bl n : Loc) (rc rp : NRec) (xs : List (Loc × node × List Inode)) (par : Loc)
    (Bs : BRec) (ws0 : List WEntry) (i0 : Nat) (T : WTx) (B : BRec) (K : Loc → Bool) (Ts : WTx)
    (Ks : Loc → Bool) (hst : startP bl n rc xs par Bs ws0 i0)
    (hsr : splitRes bl n rc rp xs T B K Ts Bs Ks par) (j : Nat) (xe : Loc × node × List Inode)
    (hxe : xs[j]? = some xe) (rs rx : NRec) (hrs : Bs.ns !! xe.1 = some rs) (hdn : dnK rs rx) :
    rx.nv.isLeaf' = rc.nv.isLeaf' := by
  obtain ⟨-, -, -, -, -, -, -, hpr, -⟩ := hst
  have h1 := hpr j xe hxe
  rw [hrs] at h1; cases h1
  have hnv : (partRec rc j xe ((chunksOf rc xs).getD j [])).nv = xe.2.1 := by
    unfold partRec; split <;> rfl
  have hl := spPartLeaf bl n rc rp xs T B K Ts Bs Ks par hsr xe (List.mem_of_getElem? hxe)
  rcases hdn with h | ⟨-, hnv'⟩
  · rw [h, hnv, hl]
  · rw [hnv', hnv, hl]

/-- A branch part's inodes' page ids are its chunk's entries'. -/
theorem spBranchPgids (ins : List Inode) (ws ch : List WEntry) (id : w64)
    (hfp : ∀ (i : Nat) (it : Inode) (w : WEntry), ins[i]? = some it → ws[i]? = some w →
      it.flags' = w.flags ∧ it.pgid' = w.pgid)
    (hil : ins.length = ws.length) (hws : ws.map ownFresh = ch.map ownFresh)
    (hch : ∀ w ∈ ch, w.pgid ≠ id) :
    ∀ i < ins.length, (ins.getD i (zero_val Inode)).pgid' ≠ id := by
  intro i hi
  have hiw : i < ws.length := by rw [← hil]; exact hi
  have hic : i < ch.length := by
    have := congrArg List.length hws; simp only [List.length_map] at this; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [(hfp i _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hiw)).2]
  have e : (ws.map ownFresh)[i]? = (ch.map ownFresh)[i]? := by rw [hws]
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hiw,
    List.getElem?_eq_getElem hic] at e
  simp only [Option.map_some, Option.some.injEq] at e
  have hp : ws[i].pgid = ch[i].pgid := by
    have := congrArg WEntry.pgid e; exact this
  rw [hp]; exact hch _ (List.getElem_mem hic)

/-- The current part's struct: its split struct (but for its key). -/
theorem spCurPartNv (bl n : Loc) (rc : NRec) (xs : List (Loc × node × List Inode)) (par : Loc)
    (Bs : BRec) (ws0 : List WEntry) (i0 : Nat) (hst : startP bl n rc xs par Bs ws0 i0) (j : Nat)
    (xe : Loc × node × List Inode) (hxe : xs[j]? = some xe) (rs rx : NRec)
    (hrs : Bs.ns !! xe.1 = some rs) (hdn : dnK rs rx) :
    rx.nv = { xe.2.1 with key' := rx.nv.key' } ∧ xe.2.1.parent' = par := by
  obtain ⟨-, -, -, -, -, -, -, hpr, hpar, -⟩ := hst
  have h1 := hpr j xe hxe
  rw [hrs] at h1; cases h1
  have hnv : (partRec rc j xe ((chunksOf rc xs).getD j [])).nv = xe.2.1 := by
    unfold partRec; split <;> rfl
  refine ⟨?_, hpar xe (List.mem_of_getElem? hxe)⟩
  rcases hdn with h | ⟨-, hnv'⟩
  · rw [h, hnv]
  · rw [hnv', hnv]

/-- The current part's key, if it has one: non-empty, its source live (only the first part has one). -/
theorem spCurPartKey (bl n : Loc) (rc : NRec) (xs : List (Loc × node × List Inode)) (par : Loc)
    (Bs : BRec) (ws0 : List WEntry) (i0 : Nat) (hst : startP bl n rc xs par Bs ws0 i0) (j : Nat)
    (xe : Loc × node × List Inode) (hxe : xs[j]? = some xe) (rs rx : NRec)
    (hrs : Bs.ns !! xe.1 = some rs) (hdn : dnK rs rx)
    (hrc0 : rc.nv.key' = slice.nil ∨ (0 < rc.key.length ∧ rc.ksrc ≠ Src.stale)) :
    rx.nv.key' ≠ slice.nil → 0 < rx.key.length ∧ rx.ksrc ≠ Src.stale := by
  intro hk
  obtain ⟨-, -, -, -, -, hkey, -, hks, hkn⟩ := spDnK_facts rs rx hdn
  obtain ⟨-, -, -, -, -, -, -, hpr, -, hhd, hdrop⟩ := hst
  have h1 := hpr j xe hxe
  rw [hrs] at h1; cases h1
  have hk' : (partRec rc j xe ((chunksOf rc xs).getD j [])).nv.key' ≠ slice.nil := fun h => hk (hkn h)
  cases j with
  | zero =>
    have hh := hhd xe (by rw [List.head?_eq_getElem?]; exact hxe)
    simp only [partRec, ↓reduceIte] at hk' hks hkey ⊢
    rw [hh] at hk'
    rcases hrc0 with h | ⟨h1, h2⟩
    · exact absurd h hk'
    · exact ⟨by rw [hkey]; exact h1, hks h2⟩
  | succ j =>
    have hx : xe ∈ xs.drop 1 := by
      rw [List.mem_iff_getElem?]; exact ⟨j, by rw [List.getElem?_drop]; simpa [Nat.add_comm] using hxe⟩
    simp only [partRec, Nat.add_one_ne_zero, ↓reduceIte] at hk'
    exact absurd (hdrop xe hx).2 hk'

/-- A part under a parent: some inodes. -/
theorem spPartNonempty (bl n : Loc) (rc rp : NRec) (xs : List (Loc × node × List Inode)) (T : WTx)
    (B : BRec) (K : Loc → Bool) (Ts : WTx) (Bs : BRec) (Ks : Loc → Bool) (par : Loc)
    (hsr : splitRes bl n rc rp xs T B K Ts Bs Ks par) (hil : rc.ins.length = rc.ws.length)
    (hrcne : rc.nv.parent' ≠ null → 0 < rc.ws.length) (xe : Loc × node × List Inode)
    (hxe : xe ∈ xs) (hp : xe.2.1.parent' ≠ null) : 0 < xe.2.2.length := by
  rcases hsr with ⟨rfl, -⟩ | ⟨-, -, -, h2, hsp, -⟩
  · simp at hxe; subst hxe; show 0 < rc.ins.length; rw [hil]; exact hrcne hp
  · have := hsp.2.2 h2 xe hxe; omega

/-- A parent kept or dereferenced: its entries live, sorted, its bucket. -/
theorem spDnK_par (bl : Loc) (r r' : NRec) (h : dnK r r') (hl : wsLive r.ws)
    (hil : r.ins.length = r.ws.length) (hs : wsSorted r.ws) (hb : r.nv.bucket' = bl) :
    wsLive r'.ws ∧ r'.ins.length = r'.ws.length ∧ wsSorted r'.ws ∧ r'.nv.bucket' = bl := by
  rcases h with rfl | ⟨⟨⟨-, hws, -, -, -, -, hil'⟩, -⟩, hnv⟩
  · exact ⟨hl, hil, hs, hb⟩
  · refine ⟨fun w hw => ?_, hil', ?_, by rw [hnv]; exact hb⟩
    · rw [hws] at hw
      obtain ⟨w0, -, rfl⟩ := List.mem_map.1 hw
      exact ⟨nofun, nofun⟩
    · unfold wsSorted at hs ⊢; rw [hws, wKey_fresh, List.length_map]; exact hs

theorem spWsChunks_length (ws : List WEntry) : ∀ (ks : List Nat), (wsChunks ws ks).length = ks.length
  | [] => rfl
  | k :: ks => by simp only [wsChunks, List.length_cons, spWsChunks_length (ws.drop k) ks]

theorem spWHead_key (ws ch : List WEntry) (h : ws.map ownFresh = ch.map ownFresh) :
    (wHead ws).key = (wHead ch).key := by
  cases ws with
  | nil => cases ch with
    | nil => rfl
    | cons c ch => simp at h
  | cons w ws => cases ch with
    | nil => simp at h
    | cons c ch =>
      simp only [List.map_cons, List.cons.injEq] at h
      have := congrArg WEntry.key h.1
      exact this

theorem spSub_insert {V : Type} (m : GMap w64 V) (k : w64) (v : V) (h : m !! k = none) :
    m ⊆ <[k := v]> m := by
  intro k' v' h'
  have hne : k ≠ k' := fun e => by rw [e] at h; rw [h] at h'; cases h'
  rw [GMap.lookup_insert_ne _ _ hne]; exact h'

/-- An empty part: the bucket's root, an empty leaf, its only part, no parent. -/
theorem spEmptyRoot (bl n : Loc) (rc rp : NRec) (xs : List (Loc × node × List Inode)) (T : WTx)
    (B : BRec) (K : Loc → Bool) (Ts : WTx) (Bs : BRec) (Ks : Loc → Bool) (par : Loc)
    (hsr : splitRes bl n rc rp xs T B K Ts Bs Ks par) (hil : rc.ins.length = rc.ws.length)
    (hrcne : rc.nv.parent' ≠ null → 0 < rc.ws.length)
    (hbr2 : rc.nv.isLeaf' = false → 2 ≤ rc.ws.length) (xe : Loc × node × List Inode)
    (hxe : xe ∈ xs) (hxe0 : xe.2.2 = []) (hpxe : xe.2.1.parent' = par) :
    par = null ∧ rc.nv.isLeaf' = true ∧ chunksOf rc xs = [[]] ∧ xs.length = 1 := by
  have hpar : par = null := by
    apply Classical.byContradiction; intro hp
    have := spPartNonempty bl n rc rp xs T B K Ts Bs Ks par hsr hil hrcne xe hxe (by rw [hpxe]; exact hp)
    rw [hxe0] at this; simp at this
  rcases hsr with ⟨hxs1, -⟩ | ⟨-, -, -, h2, hsp, -⟩
  · subst hxs1
    simp at hxe; subst hxe
    simp only at hxe0
    have hw0 : rc.ws = [] := by
      apply List.length_eq_zero_iff.1; rw [← hil, hxe0]; rfl
    refine ⟨hpar, ?_, ?_, rfl⟩
    · cases hl : rc.nv.isLeaf' with
      | true => rfl
      | false => have := hbr2 hl; rw [hw0] at this; simp at this
    · unfold chunksOf; simp [wsChunks, hxe0]
  · have := hsp.2.2 h2 xe hxe; rw [hxe0] at this; simp at this

theorem spWKey_take (l : List WEntry) (m i : Nat) (h : i < m) : wKey (l.take m) i = wKey l i := by
  unfold wKey; rw [List.getElem?_take_of_lt h]

theorem spWKey_drop (l : List WEntry) (m i : Nat) : wKey (l.drop m) i = wKey l (m + i) := by
  unfold wKey; rw [List.getElem?_drop]

theorem spSorted_take (ws : List WEntry) (k : Nat) (hs : wsSorted ws) : wsSorted (ws.take k) := by
  intro i j hij hj
  rw [List.length_take] at hj
  rw [spWKey_take _ _ _ (by omega), spWKey_take _ _ _ (by omega)]
  exact hs _ _ hij (by omega)

theorem spSorted_drop (ws : List WEntry) (k : Nat) (hs : wsSorted ws) : wsSorted (ws.drop k) := by
  intro i j hij hj
  rw [List.length_drop] at hj
  rw [spWKey_drop, spWKey_drop]
  exact hs _ _ (by omega) (by omega)

theorem spWKey_mem (ws : List WEntry) (w : WEntry) (h : w ∈ ws) :
    ∃ i, i < ws.length ∧ wKey ws i = w.key := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, hi, by unfold wKey; rw [List.getElem?_eq_getElem hi]; rfl⟩

theorem spWHead_wKey (l : List WEntry) (h : l ≠ []) : (wHead l).key = wKey l 0 := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => rfl

theorem spChunks_sorted : ∀ (ls : List Nat) (ws : List WEntry) (j : Nat), wsSorted ws →
    wsSorted ((wsChunks ws ls).getD j [])
  | [], ws, j, _ => by
    intro i k _ hk; simp [wsChunks] at hk
  | k :: ks, ws, 0, hs => by
    simp only [wsChunks, List.getD_cons_zero]; exact spSorted_take ws k hs
  | k :: ks, ws, j + 1, hs => by
    simp only [wsChunks, List.getD_cons_succ]; exact spChunks_sorted ks _ j (spSorted_drop ws k hs)

theorem spChunks_sub : ∀ (ls : List Nat) (ws : List WEntry) (j : Nat) (w : WEntry),
    w ∈ (wsChunks ws ls).getD j [] → w ∈ ws
  | [], ws, j, w, h => by simp [wsChunks] at h
  | k :: ks, ws, 0, w, h => by
    simp only [wsChunks, List.getD_cons_zero] at h; exact List.mem_of_mem_take h
  | k :: ks, ws, j + 1, w, h => by
    simp only [wsChunks, List.getD_cons_succ] at h; exact List.mem_of_mem_drop (spChunks_sub ks _ j w h)

theorem spHiAt_succ (a : List WEntry) (L : List (List WEntry)) (hi : Option (List w8)) (j : Nat) :
    hiAt (a :: L) hi (j + 1) = hiAt L hi j := by
  unfold hiAt; rfl

theorem spChunks_hi : ∀ (ls : List Nat) (ws : List WEntry) (hi : Option (List w8)) (j : Nat),
    wsSorted ws → (∀ w ∈ ws, keyLt w.key hi) → (∀ c ∈ wsChunks ws ls, c ≠ []) →
    ∀ w ∈ (wsChunks ws ls).getD j [], keyLt w.key (hiAt (wsChunks ws ls) hi j)
  | [], ws, hi, j, _, _, _ => by intro w hw; simp [wsChunks] at hw
  | k :: ks, ws, hi, j + 1, hs, hh, hne => by
    intro w hw
    simp only [wsChunks, List.getD_cons_succ] at hw
    simp only [wsChunks]; rw [spHiAt_succ]
    exact spChunks_hi ks (ws.drop k) hi j (spSorted_drop ws k hs) (fun w hw => hh w (List.mem_of_mem_drop hw))
      (fun c hc => hne c (by simp only [wsChunks]; exact List.mem_cons_of_mem _ hc)) w hw
  | k :: ks, ws, hi, 0, hs, hh, hne => by
    intro w hw
    simp only [wsChunks, List.getD_cons_zero] at hw
    cases ks with
    | nil =>
      show keyLt w.key hi
      exact hh w (List.mem_of_mem_take hw)
    | cons k' ks' =>
      have hc1 := hne ((ws.drop k).take k') (by simp [wsChunks])
      show keyLt w.key (some (wHead ((ws.drop k).take k')).key)
      have hkl : k < ws.length := by
        apply Classical.byContradiction; intro hk
        apply hc1; rw [List.drop_eq_nil_of_le (by omega), List.take_nil]
      have hk'0 : 0 < k' := by
        apply Classical.byContradiction; intro hk
        apply hc1; rw [show k' = 0 by omega]; rfl
      rw [spWHead_wKey _ hc1, spWKey_take _ _ _ hk'0, spWKey_drop, Nat.add_zero]
      obtain ⟨i, hi', hwi⟩ := spWKey_mem _ w hw
      rw [List.length_take] at hi'
      rw [spWKey_take _ _ _ (by omega)] at hwi
      intro h e; cases e
      rw [← hwi]; exact hs _ _ (by omega) hkl

theorem spChunk_lo (ch : List WEntry) (hs : wsSorted ch) (w : WEntry) (hw : w ∈ ch) :
    keyGe (some (wHead ch).key) w.key := by
  intro l e; cases e
  have hne : ch ≠ [] := List.ne_nil_of_mem hw
  rw [spWHead_wKey _ hne]
  obtain ⟨i, hi, hwi⟩ := spWKey_mem _ w hw
  rw [← hwi]
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0; exact goStringLt_irrefl_w _
  · intro hlt
    exact goStringLt_irrefl_w _ (goStringLt_trans hlt (hs 0 i h0 hi))

/-- A part's entries: sorted, in `[its first key, the next part's first key or hi)`. -/
theorem spChunkKeysOf (bl n : Loc) (rc rp : NRec) (xs : List (Loc × node × List Inode)) (T : WTx)
    (B : BRec) (K : Loc → Bool) (Ts : WTx) (Bs : BRec) (Ks : Loc → Bool) (par : Loc)
    (ws0 : List WEntry) (i0 : Nat) (hst : startP bl n rc xs par Bs ws0 i0)
    (hsr : splitRes bl n rc rp xs T B K Ts Bs Ks par) (hil : rc.ins.length = rc.ws.length)
    (hs : wsSorted rc.ws) (lo hi : Option (List w8))
    (hkb : ∀ w ∈ rc.ws, 0 < w.key.length ∧ keyIn lo hi w.key) (j : Nat)
    (hne : (chunksOf rc xs).getD j [] ≠ []) :
    wsSorted ((chunksOf rc xs).getD j []) ∧ ∀ w ∈ (chunksOf rc xs).getD j [], 0 < w.key.length ∧
      keyIn (some (wHead ((chunksOf rc xs).getD j [])).key) (hiAt (chunksOf rc xs) hi j) w.key := by
  have hsum : (xs.map (fun x => x.2.2.length)).sum ≤ rc.ws.length := by
    rw [← hil, ← hst.2.2.2.1.1, List.length_flatten, List.map_map]; exact Nat.le_refl _
  have hcl : (chunksOf rc xs).length = xs.length := by
    unfold chunksOf; rw [spWsChunks_length, List.length_map]
  have hall : ∀ c ∈ chunksOf rc xs, c ≠ [] := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have hgd : (chunksOf rc xs).getD k [] = (chunksOf rc xs)[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
    rcases hsr with ⟨hxs1, -⟩ | ⟨-, -, -, h2, hsp, -⟩
    · have hl : (chunksOf rc xs).length = 1 := by rw [hcl, hxs1]; rfl
      have hj : j < 1 := by
        apply Classical.byContradiction; intro hj; apply hne
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [← hgd, show k = 0 by omega, ← show j = 0 by omega]; exact hne
    · have hkx : k < xs.length := by rw [← hcl]; exact hk
      have hk' : (xs.map (fun x => x.2.2.length))[k]? = some xs[k].2.2.length := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hkx]; rfl
      obtain ⟨hlen, -⟩ := wsChunks_get rc.ws _ k _ hk' hsum
      have hx := hsp.2.2 h2 xs[k] (List.getElem_mem hkx)
      intro h
      have hlen' : ((chunksOf rc xs).getD k []).length = xs[k].2.2.length := hlen
      rw [hgd, h] at hlen'; simp at hlen'; omega
  refine ⟨spChunks_sorted _ _ j hs, fun w hw => ?_⟩
  have hwr := spChunks_sub _ _ j w hw
  exact ⟨(hkb w hwr).1, spChunk_lo _ (spChunks_sorted _ _ j hs) w hw,
    spChunks_hi _ rc.ws hi j hs (fun w hw => (hkb w hw).2.2) hall w hw⟩

/-- A branch's part has at least two entries. -/
theorem spChunkLen2 (bl n : Loc) (rc rp : NRec) (xs : List (Loc × node × List Inode)) (T : WTx)
    (B : BRec) (K : Loc → Bool) (Ts : WTx) (Bs : BRec) (Ks : Loc → Bool) (par : Loc)
    (ws0 : List WEntry) (i0 : Nat) (hst : startP bl n rc xs par Bs ws0 i0)
    (hsr : splitRes bl n rc rp xs T B K Ts Bs Ks par) (hil : rc.ins.length = rc.ws.length)
    (hbr2 : rc.nv.isLeaf' = false → 2 ≤ rc.ws.length) (j : Nat) (hj : j < xs.length)
    (hl : rc.nv.isLeaf' = false) : 2 ≤ ((chunksOf rc xs).getD j []).length := by
  have hsum : (xs.map (fun x => x.2.2.length)).sum ≤ rc.ws.length := by
    rw [← hil, ← hst.2.2.2.1.1, List.length_flatten, List.map_map]; exact Nat.le_refl _
  have hk' : (xs.map (fun x => x.2.2.length))[j]? = some xs[j].2.2.length := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  obtain ⟨hlen, -⟩ := wsChunks_get rc.ws _ j _ hk' hsum
  have hlen' : ((chunksOf rc xs).getD j []).length = xs[j].2.2.length := hlen
  rw [hlen']
  rcases hsr with ⟨hxs1, -⟩ | ⟨-, -, -, h2, hsp, -⟩
  · subst hxs1
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    show 2 ≤ rc.ins.length
    rw [hil]; exact hbr2 hl
  · exact hsp.2.2 h2 xs[j] (List.getElem_mem hj)

theorem spPutList_mem {α : Type} (l : List α) (i : Nat) (b : Bool) (x y : α) (h : y ∈ putList l i b x) :
    y = x ∨ y ∈ l := by
  unfold putList at h
  split at h
  · rcases List.mem_or_eq_of_mem_set h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · simp only [List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact Or.inr (List.mem_of_mem_take h)
    · exact Or.inl h
    · exact Or.inr (List.mem_of_mem_drop h)

theorem spPutList_length {α β : Type} (l1 : List α) (l2 : List β) (i : Nat) (b : Bool) (x : α) (y : β)
    (h : l1.length = l2.length) : (putList l1 i b x).length = (putList l2 i b y).length := by
  unfold putList; split <;> simp [h]

theorem spPutList_map {α β : Type} (f : α → β) (l : List α) (i : Nat) (b : Bool) (x : α) :
    (putList l i b x).map f = putList (l.map f) i b (f x) := by
  unfold putList; split <;> simp [List.map_set, List.map_take, List.map_drop]

theorem spWHead_of (l : List WEntry) (w : WEntry) (h : l[0]? = some w) : wHead l = w := by
  cases l with
  | nil => simp at h
  | cons a l => simp at h; subst h; rfl

theorem spFresh_set0 (ws : List WEntry) (w0 : WEntry) (h : ws[0]? = some w0) (s1 : Src) :
    (ws.set 0 { w0 with ks := s1 }).map ownFresh = ws.map ownFresh := by
  cases ws with
  | nil => simp at h
  | cons a l => simp at h; subst h; rfl

theorem spLive_put (l : List WEntry) (i : Nat) (b : Bool) (e : WEntry) (hl : wsLive l)
    (he : e.ks ≠ Src.stale ∧ e.vs ≠ Src.stale) : wsLive (putList l i b e) := by
  intro w hw
  rcases spPutList_mem _ _ _ _ _ hw with rfl | hw
  · exact he
  · exact hl w hw

theorem spLive_set0 (l : List WEntry) (e : WEntry) (hl : wsLive l)
    (he : e.ks ≠ Src.stale ∧ e.vs ≠ Src.stale) : wsLive (l.set 0 e) := by
  intro w hw
  rcases List.mem_or_eq_of_mem_set hw with hw | rfl
  · exact hl w hw
  · exact he

theorem spDerefOK_put (bl : Loc) (rp : NRec) (h : derefOK bl rp) (s' : GoSlice) (idx : Nat) (bx : Bool)
    (it : Inode) (e : WEntry) (he : e.ks ≠ Src.stale ∧ e.vs ≠ Src.stale ∧ 0 < e.key.length) :
    derefOK bl (NRec.mk ({ rp.nv with inodes' := s' } : node) (putList rp.ins idx bx it)
      (putList rp.ws idx bx e) rp.cs rp.key rp.ksrc) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, spPutList_length _ _ _ _ _ _ h2, fun w hw => ?_, h4⟩
  rcases spPutList_mem _ _ _ _ _ hw with rfl | hw
  · exact he
  · exact h3 w hw

theorem spDerefOK_set0 (bl : Loc) (rx : NRec) (h : derefOK bl rx) (k : GoSlice) (w : WEntry)
    (hw : w.ks ≠ Src.stale ∧ w.vs ≠ Src.stale ∧ 0 < w.key.length) (key : List w8) (hk : 0 < key.length)
    (s3 : Src) (hs3 : s3 ≠ Src.stale) :
    derefOK bl (NRec.mk ({ rx.nv with key' := k } : node) rx.ins (rx.ws.set 0 w) rx.cs key s3) := by
  obtain ⟨h1, h2, h3, -⟩ := h
  refine ⟨h1, by rw [List.length_set]; exact h2, fun w' hw' => ?_, Or.inr ⟨hs3, Or.inr hk⟩⟩
  rcases List.mem_or_eq_of_mem_set hw' with hw' | rfl
  · exact h3 w' hw'
  · exact hw

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The freelist lent to `Free` of the view's page `id` (its token to the stash). -/
theorem spDbWR_free_acc (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (ρ : DBState) (F : GMap Nat (List w8)) (id : Nat) (pg : List w8)
    (hv : viewOK W) (hF : freedOK W ρ.fl txid F) (hpg : W.pages !! id = some pg) :
    dbWR I γd W txl txid ρ ∗ pgToks γ F ∗ (id ↪[γ] () : IProp GF) ⊢ ∃ fls,
      ⌜W.fli = I.iface ∧ ρ.fl.canFree txid (W64 id) (1 + pageOverflow pg) ∧
        freedOK W (ρ.fl.freePages txid (W64 id) (1 + pageOverflow pg)) txid (<[id := pg]> F)⌝ ∗
      ownFL I fls ρ.fl ∗
      (ownFL I fls (ρ.fl.freePages txid (W64 id) (1 + pageOverflow pg)) -∗
        dbWR I γd W txl txid { ρ with fl := ρ.fl.freePages txid (W64 id) (1 + pageOverflow pg) } ∗
        pgToks γ (<[id := pg]> F)) := by
  iintro ⟨Hdbw, HFt, Htok⟩
  icases dbWR_view_keep I γd W txl txid ρ $$ Hdbw with ⟨Hdbw, %Hdisj⟩
  icases pgToks_fresh γ F id $$ [HFt Htok] with ⟨HFt, Htok, %HFn⟩
  · iframe
  unfold dbWR
  icases Hdbw with ⟨Hdb, %Hdw⟩
  obtain ⟨hAl, hrw, hdata, hps, hfli, w, hw, hwp, hwq, hwh, htx, htb⟩ := Hdw
  have Hpgw : w.pages !! id = some pg := by rw [hwp]; exact hpg
  have Hnew := freedOK_hnew W hv ρ.fl txid F hF Hdisj.1 id pg hpg HFn
  icases ownDB_free I W.dbl γd ρ w hw txid htx htb id pg Hpgw Hnew $$ Hdb
    with ⟨%fls, %hcan, Hfl, Hdbback⟩
  iexists fls
  iframe Hfl
  isplitr
  · ipureintro; exact ⟨hfli, hcan, freedOK_free W hv ρ.fl txid F hF id pg hpg HFn⟩
  iintro Hfl
  ihave Hdb := Hdbback $$ Hfl
  ihave HFt := pgToks_insert γ F id pg HFn $$ [HFt Htok]
  · iframe
  iframe
  ipureintro
  exact ⟨hAl, hrw, hdata, hps, hfli, w, hw, hwp, hwq, hwh, htx, htb⟩

/-- The header of the dirty page `id` (at `p`, bytes `b`) out of the page buffers, and back. -/
theorem spBufsHdr (T : WTx) (id : w64) (p : Loc) (b : List w8)
    (hp : T.pm !! id = some p) (hb : T.bufs !! id = some b) (h16 : 16 ≤ b.length)
    (hc : p.locCar ≠ 0) :
    bufsOwn (GF := GF) T ⊢
      (p ↦ pageOf b : IProp GF) ∗ bytesPointsto (p +ₗ 16) (DFrac.own 1) (b.drop 16) ∗
      (∀ (hdr : Page) (rest : List w8), (p ↦ hdr : IProp GF) -∗
        bytesPointsto (p +ₗ 16) (DFrac.own 1) rest -∗
        bufsOwn { T with bufs := <[id := pageBytes hdr ++ rest]> T.bufs }) := by
  unfold bufsOwn
  iintro Hbufs
  icases (BigSepM.bigSepM_delete (M := GMap w64)
      (Φ := fun i q => iprop(∃ bs, ⌜T.bufs !! i = some bs⌝ ∗ bytesPointsto (GF := GF) q (DFrac.own 1) bs))
      (show Std.get? T.pm id = some p from hp)).1 $$ Hbufs with ⟨⟨%bs, %Hbs', Hp⟩, Hrest⟩
  rw [hb] at Hbs'
  cases Hbs'
  icases (page_header_bytes p (DFrac.own 1) b h16 hc).1 $$ Hp with ⟨Hh, Hr⟩
  iframe Hh Hr
  iintro %hdr %rest Hh Hr
  iapply (BigSepM.bigSepM_delete (M := GMap w64)
      (Φ := fun i q => iprop(∃ bs, ⌜(<[id := pageBytes hdr ++ rest]> T.bufs) !! i = some bs⌝ ∗
        bytesPointsto (GF := GF) q (DFrac.own 1) bs))
      (show Std.get? T.pm id = some p from hp)).2
  isplitl [Hh Hr]
  · iexists (pageBytes hdr ++ rest)
    isplitr
    · ipureintro; exact GMap.lookup_insert _ _ _
    iapply (bytesPointsto_app _ _ _ _).2
    have hl : (pageBytes hdr).length = 16 := by unfold pageBytes; simp [leBytes_length']
    rw [hl]
    ihave Hh := (Page_bytes (hG := hG) p hdr (DFrac.own 1) hc).1 $$ Hh
    iframe
  iapply (BigSepM.bigSepM_mono (M := GMap w64)
    (Φ := fun i q => iprop(∃ bs, ⌜T.bufs !! i = some bs⌝ ∗ bytesPointsto (GF := GF) q (DFrac.own 1) bs))
    (Ψ := fun i q => iprop(∃ bs, ⌜(<[id := pageBytes hdr ++ rest]> T.bufs) !! i = some bs⌝ ∗
        bytesPointsto (GF := GF) q (DFrac.own 1) bs)) ?_) $$ Hrest
  intro i q hi
  have hne : i ≠ id := by
    intro e; subst e
    change (GMap.delete i T.pm) !! i = some q at hi
    rw [GMap.lookup_delete] at hi; cases hi
  iintro ⟨%bs, %hbs, H⟩
  iexists bs
  iframe
  ipureintro
  rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hbs

/-- A node's struct and inodes, out of the bucket's nodes, and back. -/
theorem spSpillR_nodeIns (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (n : Loc) (r : NRec) (hB : T.bs !! bl = some B) (hn : B.ns !! n = some r) :
    spillR I γd γ W txl txid T ρ F K ⊢
      n ↦ r.nv ∗ r.nv.inodes' ↦* r.ins ∗
      (n ↦ r.nv -∗ r.nv.inodes' ↦* r.ins -∗ spillR I γd γ W txl txid T ρ F K) := by
  unfold spillR ownWriteTxGX
  iintro ⟨Hdb, ⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩, Hv, Hcaps, Hgh, HF⟩
  icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun bl B => bktOwnX (GF := GF) W bl B)
    (show Std.get? T.bs bl = some B from hB)).1 $$ Hbs with ⟨Hb, Hbback⟩
  unfold bktOwnX
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
    (show Std.get? B.ns n = some r from hn)).1 $$ Hns with ⟨Hnd, Hnsback⟩
  unfold nodeOwnX
  icases Hnd with ⟨Hn, Hins, Hrest2⟩
  iframe Hn Hins
  iintro Hn Hins
  iframe
  iapply Hbback
  iframe
  iapply Hnsback
  iframe

/-- A free (pending for the writer) keeps the spill's facts. -/
theorem spSpillG_free (W : WView) (txl : Loc) (txid : w64) (T : WTx) (ρ : DBState)
    (F F' : GMap Nat (List w8)) (id : w64) (k : Nat) (hg : spillG (hG := hG) W txl txid T ρ F)
    (hok : ∃ v0 v1, dbOK ρ v0 v1)
    (hf : freedOK W (ρ.fl.freePages txid id k) txid F') :
    spillG (hG := hG) W txl txid T { ρ with fl := ρ.fl.freePages txid id k } F' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, htx, hd, hu, -, hr⟩ := hg
  obtain ⟨hd', hu'⟩ := spillDirty_free ρ W T txid id k hok hd hu
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, htx, hd', hu', hf, hr⟩

/-- A node's record changed but its children, parent, entries' sources and key source (its
live nodes as they were): the spill's facts kept. -/
theorem spSpillG_setN (W : WView) (txl : Loc) (txid : w64) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (bl : Loc) (B : BRec) (x : Loc) (r r' : NRec)
    (hg : spillG (hG := hG) W txl txid T ρ F) (hB : T.bs !! bl = some B) (hx : B.ns !! x = some r)
    (hcs : r'.cs = r.cs) (hpar : r'.nv.parent' = r.nv.parent')
    (hnv : noViewRec r → noViewRec r') (hok : derefOK bl r → derefOK bl r') :
    spillG (hG := hG) W txl txid (setB T bl (setN B x r')) ρ F := by
  have hag : ∀ l, nAgree B.ns (setN B x r').ns l := by
    intro l rl hl
    by_cases e : l = x
    · subst e; rw [hx] at hl; cases hl
      exact ⟨r', GMap.lookup_insert _ _ _, hcs, hpar⟩
    · exact ⟨rl, by show (<[x := r']> B.ns) !! l = some rl; rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl, rfl, rfl⟩
  have hlk : ∀ l rl', (setN B x r').ns !! l = some rl' → (l = x ∧ rl' = r') ∨ (l ≠ x ∧ B.ns !! l = some rl') := by
    intro l rl' h
    change (<[x := r']> B.ns) !! l = some rl' at h
    by_cases e : l = x
    · subst e; rw [GMap.lookup_insert] at h; cases h; exact Or.inl ⟨rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h; exact Or.inr ⟨e, h⟩
  apply spillG_setB W txl txid T ρ F bl B (setN B x r') hg hB rfl rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hr⟩ := hg
  rcases (hr.2.2.2 bl B hB).1 with h0 | ⟨S, ⟨p, top, hup, hnd, hkt, hpv⟩, hdok⟩
  · exact Or.inl h0
  · right
    refine ⟨S, ⟨p, top, upPath_mono _ _ hup (fun l _ => hag l), hnd,
      kidsTree_mono _ _ S.length top S (Nat.le_refl _) (fun l _ => hag l) hkt, fun l hl hlS => ?_⟩,
      fun l hl => ?_⟩
    · obtain ⟨rl, hrl, hnvl⟩ := hpv l hl hlS
      by_cases e : l = x
      · subst e; rw [hx] at hrl; cases hrl
        exact ⟨r', GMap.lookup_insert _ _ _, hnv hnvl⟩
      · exact ⟨rl, by show (<[x := r']> B.ns) !! l = some rl; rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hrl, hnvl⟩
    · obtain ⟨rl, hrl, hdl⟩ := hdok l hl
      by_cases e : l = x
      · subst e; rw [hx] at hrl; cases hrl
        exact ⟨r', GMap.lookup_insert _ _ _, hok hdl⟩
      · exact ⟨rl, by show (<[x := r']> B.ns) !! l = some rl; rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hrl, hdl⟩

theorem spSrcOwn_len (W : WView) (sl : GoSlice) (src : Src) (bs : List w8) :
    srcOwn (GF := GF) W sl src bs ⊢ ⌜src ≠ Src.stale → uint.nat sl.len = bs.length⌝ := by
  cases src with
  | view =>
    unfold srcOwn
    iintro %h
    ipureintro; intro _
    obtain ⟨-, hl, hlen, -⟩ := h
    rw [hlen]; unfold uint.nat; word
  | own d =>
    unfold srcOwn
    iintro H
    ihave %h := ownSlice_len _ _ _ $$ H
    ipureintro; intro _
    obtain ⟨h1, h2⟩ := h
    rw [h1]; unfold uint.nat sint.nat; word
  | stale =>
    iintro -; ipureintro; intro h; exact absurd rfl h

/-- The inodes' slices are their entries' bytes long. -/
theorem spWOwns_len (W : WView) : ∀ (ins : List Inode) (ws : List WEntry),
    ([∗list] it;w ∈ ins;ws, wOwn (GF := GF) W it w) ⊢
      ⌜∀ (i : Nat) (it : Inode) (w : WEntry), ins[i]? = some it → ws[i]? = some w →
        (w.ks ≠ Src.stale → uint.nat it.key'.len = w.key.length) ∧
        (w.vs ≠ Src.stale → uint.nat it.value'.len = w.value.length)⌝
  | [], _ => by
    iintro -; ipureintro; intro i it w h; simp at h
  | it :: ins, [] => by
    iintro -; ipureintro; intro i it' w _ h; simp at h
  | it :: ins, w :: ws => by
    iintro H
    icases BigSepL2.bigSepL2_cons.1 $$ H with ⟨Hw, H⟩
    isimp only [wOwn] at Hw
    icases Hw with ⟨-, Hk, Hv⟩
    ihave %hk := spSrcOwn_len W _ _ _ $$ Hk
    ihave %hv := spSrcOwn_len W _ _ _ $$ Hv
    ihave %h := spWOwns_len W ins ws $$ H
    ipureintro
    intro i it' w' h1 h2
    cases i with
    | zero => simp at h1 h2; subst h1; subst h2; exact ⟨hk, hv⟩
    | succ i => exact h i it' w' (by simpa using h1) (by simpa using h2)

/-- The inodes' slices of a node of the spill state are its entries' bytes long. -/
theorem spSpillR_lens (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (n : Loc) (r : NRec) (hB : T.bs !! bl = some B) (hn : B.ns !! n = some r) :
    spillR I γd γ W txl txid T ρ F K ⊢
      ⌜∀ (i : Nat) (it : Inode) (w : WEntry), r.ins[i]? = some it → r.ws[i]? = some w →
        (w.ks ≠ Src.stale → uint.nat it.key'.len = w.key.length) ∧
        (w.vs ≠ Src.stale → uint.nat it.value'.len = w.value.length)⌝ := by
  unfold spillR ownWriteTxGX
  iintro ⟨-, ⟨-, -, -, -, Hbs⟩, -⟩
  icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun bl B => bktOwnX (GF := GF) W bl B)
    (show Std.get? T.bs bl = some B from hB)).1 $$ Hbs with ⟨Hb, -⟩
  unfold bktOwnX
  icases Hb with ⟨-, -, -, -, -, Hns⟩
  icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
    (show Std.get? B.ns n = some r from hn)).1 $$ Hns with ⟨Hnd, -⟩
  unfold nodeOwnX
  icases Hnd with ⟨-, -, Hents, -⟩
  iapply spWOwns_len W r.ins r.ws
  iexact Hents

/-- The transaction's database field and the page size, out of the spill state. -/
theorem spSpillR_dbps (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool)
    (hdb : T.t.db' = W.dbl) :
    spillR I γd γ W txl txid T ρ F K ⊢
      structFieldRef Tx go!"db" txl ↦ W.dbl ∗
      (structFieldRef DB go!"pageSize" W.dbl ↦□ W64 (W.ps : Int) : IProp GF) ∗
      (structFieldRef Tx go!"db" txl ↦ W.dbl -∗ spillR I γd γ W txl txid T ρ F K) := by
  unfold spillR ownWriteTxGX TxW_rest_root wView
  rw [hdb]
  iintro ⟨Hdb, ⟨⟨Hwr, Hman, Hdbf, Hrest⟩, Hm, Hpm, Hbufs, Hbs⟩, ⟨Hd, #Hps, Hv⟩, Hcaps, Hgh, HF⟩
  iframe Hdbf
  isplitr
  · iexact Hps
  iintro Hdbf
  iframe
  iframe #

/-- A default entry. -/
def spNeDflt : NodeEntry := ⟨W32 0, W64 0, [], [], DFrac.own 1, DFrac.own 1⟩

/-- The inodes' bytes as `node.write` takes them, out of their entries. -/
theorem spInodesOwn_dataF : ∀ (ins : List Inode) (es : List NodeEntry), ins.length = es.length →
    inodesOwn (GF := GF) ins es ⊢
      inodeDataF ins (es.map NodeEntry.key) (es.map NodeEntry.value)
        (fun i => (es.getD i spNeDflt).kq) (fun i => (es.getD i spNeDflt).vq) ∗
      (inodeDataF ins (es.map NodeEntry.key) (es.map NodeEntry.value)
        (fun i => (es.getD i spNeDflt).kq) (fun i => (es.getD i spNeDflt).vq) -∗ inodesOwn ins es)
  | [], [], _ => by
    unfold inodesOwn inodeDataF
    iintro H
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iintro -
    iexact H
  | it :: ins, e :: es, hl => by
    have ih := spInodesOwn_dataF ins es (by simpa using hl)
    unfold inodesOwn at ih ⊢
    unfold inodeDataF at ih ⊢
    iintro H
    icases BigSepL2.bigSepL2_cons.1 $$ H with ⟨He, H⟩
    isimp only [inodeIs] at He
    icases He with ⟨%hf, Hk, Hv⟩
    icases ih $$ H with ⟨Hd, Hback⟩
    isplitl [Hk Hv Hd]
    · iapply BigSepL.bigSepL_cons.2
      simp only [List.map_cons, List.getD_cons_zero, List.getD_cons_succ]
      iframe
    iintro Hd
    icases BigSepL.bigSepL_cons.1 $$ Hd with ⟨⟨Hk, Hv⟩, Hd⟩
    simp only [List.map_cons, List.getD_cons_zero, List.getD_cons_succ]
    iapply BigSepL2.bigSepL2_cons.2
    isplitl [Hk Hv]
    · unfold inodeIs; iframe; ipureintro; exact hf
    iapply Hback
    iexact Hd
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl

/-- A dirty page rewritten: the ghost map's domain the same. -/
theorem spGhostOK_write (γ : GName) (W : WView) (T : WTx) (id : w64) (b b' : List w8)
    (hb : T.bufs !! id = some b) :
    ghostOK (GF := GF) γ W T ⊢ ghostOK γ W { T with bufs := <[id := b']> T.bufs } := by
  unfold ghostOK
  iintro ⟨%M, Ha, %hM⟩
  iexists M
  iframe
  ipureintro
  intro k
  rw [hM k]
  unfold spillPages
  simp only [GMap.lookup_union]
  cases hw : W.pages !! k with
  | some _ => simp
  | none =>
    simp only [Option.none_or]
    unfold bufsN
    show (if k < 2 ^ 64 then T.bufs !! W64 (k : Int) else none).isSome ↔
      (if k < 2 ^ 64 then (<[id := b']> T.bufs) !! W64 (k : Int) else none).isSome
    split
    · by_cases e : id = W64 (k : Int)
      · rw [← e, GMap.lookup_insert, hb]; rfl
      · rw [GMap.lookup_insert_ne _ _ e]
    · rfl

/-- A dirty page rewritten (same length, id, overflow): the spill's facts kept. -/
theorem spSpillG_write (W : WView) (txl : Loc) (txid : w64) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (id : w64) (b b' : List w8) (hg : spillG (hG := hG) W txl txid T ρ F)
    (hb : T.bufs !! id = some b) (hl : b'.length = b.length) (hi : pageId b' = pageId b)
    (ho : pageOverflow b' = pageOverflow b) :
    spillG (hG := hG) W txl txid { T with bufs := <[id := b']> T.bufs } ρ F := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, htx, hd, hu, hf, hr⟩ := hg
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, htx, spillDirty_write ρ W T id b b' hd hb hl hi ho,
    hu, hf, derefReadyX_bs T _ _ rfl hr⟩

/-- A term of a proposition named. -/
theorem spName_eq {α : Type} (P : α → IProp GF) (a : α) : P a ⊢ ∃ b, ⌜b = a⌝ ∗ P b := by
  iintro H
  iexists a
  iframe
  ipureintro; rfl

/-- Every fraction halves. -/
theorem spDfrac_halve : ∀ d : DFrac, ∃ d' : DFrac, d' • d' = d
  | .own q => ⟨.own q.half, by show DFrac.own (q.half + q.half) = _; rw [Qp.half_add_half]⟩
  | .discard => ⟨.discard, rfl⟩
  | .ownDiscard q => ⟨.ownDiscard q.half, by
      show DFrac.ownDiscard (q.half + q.half) = _; rw [Qp.half_add_half]⟩

/-- A slice's bytes from a source, shared three ways (the view's stays the view's). -/
theorem spSrcOwn_three (W : WView) (s : GoSlice) (src : Src) (bs : List w8) (hns : src ≠ Src.stale) :
    srcOwn (GF := GF) W s src bs ⊢ ∃ s1 s2 s3, ⌜s1 ≠ Src.stale ∧ s2 ≠ Src.stale ∧ s3 ≠ Src.stale ∧
      (src ≠ Src.view → s1 ≠ Src.view ∧ s2 ≠ Src.view ∧ s3 ≠ Src.view)⌝ ∗
      srcOwn W s s1 bs ∗ srcOwn W s s2 bs ∗ srcOwn W s s3 bs := by
  cases src with
  | stale => exact absurd rfl hns
  | view =>
    unfold srcOwn
    iintro %h
    iexists Src.view, Src.view, Src.view
    isplitr
    · ipureintro; exact ⟨nofun, nofun, nofun, fun h => absurd rfl h⟩
    dsimp only
    isplitr
    · ipureintro; exact h
    isplitr
    · ipureintro; exact h
    ipureintro; exact h
  | own d =>
    obtain ⟨d1, hd1⟩ := spDfrac_halve d
    obtain ⟨d2, hd2⟩ := spDfrac_halve d1
    unfold srcOwn
    iintro H
    have e1 := (ownSlice_dfractional (GF := GF) s bs).dfractional d1 d1
    have e2 := (ownSlice_dfractional (GF := GF) s bs).dfractional d2 d2
    rw [hd1] at e1
    rw [hd2] at e2
    icases e1.1 $$ H with ⟨H1, H2⟩
    icases e2.1 $$ H2 with ⟨H2, H3⟩
    iexists Src.own d1, Src.own d2, Src.own d2
    isplitr
    · ipureintro; exact ⟨nofun, nofun, nofun, fun _ => ⟨nofun, nofun, nofun⟩⟩
    dsimp only
    iframe

theorem spRr_to (l : Loc) (dq : DFrac) (t : Tx) (rv : Bucket) :
    TxW_rest_root (GF := GF) l dq t ⊢ TxW_rest_root l dq { t with root' := rv } := by
  rw [TxW_rest_root_root]; exact .rfl

theorem spRr_of (l : Loc) (dq : DFrac) (t : Tx) (rv : Bucket) :
    TxW_rest_root (GF := GF) l dq { t with root' := rv } ⊢ TxW_rest_root l dq t := by
  rw [TxW_rest_root_root]

/-- The transaction's struct at half (its root bucket's struct: `bl`'s, or another bucket's of
`othersOwn`), with the half of `bl`'s, lent (what `node.put` reads). -/
theorem spTx_halves (W : WView) (txl bl : Loc) (bs : GMap Loc BRec) (K : Loc → Bool) (bv : Bucket)
    (t : Tx) (hroot : (bs !! structFieldRef Tx go!"root" txl).isSome) :
    (bl ↦ bv : IProp GF) ∗ othersOwn W bs bl K ∗ TxW_rest_root txl (DFrac.own 1) t ⊢
      ∃ rv, txl ↦{DFrac.own halfQ} ({ t with root' := rv } : Tx) ∗ bl ↦{DFrac.own halfQ} bv ∗
        (txl ↦{DFrac.own halfQ} ({ t with root' := rv } : Tx) -∗ bl ↦{DFrac.own halfQ} bv -∗
          (bl ↦ bv : IProp GF) ∗ othersOwn W bs bl K ∗ TxW_rest_root txl (DFrac.own 1) t) := by
  iintro ⟨Hbv, Ho, Hrest⟩
  icases (TxW_rest_root_halves txl t).1 $$ Hrest with ⟨Hr1, Hr2⟩
  icases (pt_halves bl bv).1 $$ Hbv with ⟨Hb1, Hb2⟩
  by_cases hrl : bl = structFieldRef Tx go!"root" txl
  · iexists bv
    ihave Htx : txl ↦{DFrac.own halfQ} ({ t with root' := bv } : Tx) $$ [Hb2 Hr1]
    · iapply (TxW_split_root txl (DFrac.own halfQ) _).2
      ihave Hr1 := (spRr_to txl _ t bv) $$ Hr1
      rw [← hrl]
      iframe
    iframe Htx Hb1
    iintro Htx Hb1
    icases (TxW_split_root txl _ _).1 $$ Htx with ⟨Hb2, Hr1⟩
    ihave Hr1 := (spRr_of txl _ t bv) $$ Hr1
    ihave Hb2 : bl ↦{DFrac.own halfQ} bv $$ [Hb2]
    · rw [hrl]; iexact Hb2
    ihave Hbv := (pt_halves bl bv).2 $$ [Hb1 Hb2]
    · iframe
    iframe
    iapply (TxW_rest_root_halves txl t).2
    iframe
  · obtain ⟨C, hC⟩ : ∃ C, bs !! structFieldRef Tx go!"root" txl = some C := by
      cases h : bs !! structFieldRef Tx go!"root" txl with
      | none => rw [h] at hroot; cases hroot
      | some C => exact ⟨C, rfl⟩
    have hC' : Std.get? (Std.delete bs bl) (structFieldRef Tx go!"root" txl) = some C := by
      show (GMap.delete bl bs) !! _ = some C
      rw [GMap.lookup_delete_ne _ hrl]; exact hC
    unfold othersOwn
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc)
      (Φ := fun b C => iprop(bktOwnX (GF := GF) W b C ∗ capsB C K)) hC').1 $$ Ho with ⟨⟨HC, Hcs⟩, Hoback⟩
    unfold bktOwnX
    icases HC with ⟨Hcv, HCrest⟩
    icases (pt_halves _ C.bv).1 $$ Hcv with ⟨Hc1, Hc2⟩
    iexists C.bv
    ihave Htx : txl ↦{DFrac.own halfQ} ({ t with root' := C.bv } : Tx) $$ [Hc2 Hr1]
    · iapply (TxW_split_root txl (DFrac.own halfQ) _).2
      ihave Hr1 := (spRr_to txl _ t C.bv) $$ Hr1
      iframe
    iframe Htx Hb1
    iintro Htx Hb1
    icases (TxW_split_root txl _ _).1 $$ Htx with ⟨Hc2, Hr1⟩
    ihave Hr1 := (spRr_of txl _ t C.bv) $$ Hr1
    ihave Hcv := (pt_halves _ C.bv).2 $$ [Hc1 Hc2]
    · iframe
    ihave Hbv := (pt_halves bl bv).2 $$ [Hb1 Hb2]
    · iframe
    iframe Hbv
    isplitl [Hoback Hcv HCrest Hcs]
    · iapply Hoback
      iframe
    iapply (TxW_rest_root_halves txl t).2
    iframe

/-- What a part's `parent.put(oldKey, firstKey, nil, pgid, 0)` reads, lent: the parent's inodes,
the part's first key (shared three ways: the part's entry, the parent's new entry, the part's
key) and the old key (the part's first key again, `same`, or its key `os`); and back, with the
parent's entry for the part. -/
theorem spPut_lend (W : WView) (hc : W.data.locCar ≠ 0) (ins : List Inode) (ws : List WEntry)
    (it0 : Inode) (w0 : WEntry) (h0i : ins[0]? = some it0) (h0w : ws[0]? = some w0)
    (hw0 : w0.ks ≠ Src.stale) (pins : List Inode) (pws : List WEntry) (hlive : wsLive pws)
    (hpl : pins.length = pws.length)
    (os : GoSlice) (osrc : Src) (okb : List w8) (P : Prop) [Decidable P] (hos : ¬ P → osrc ≠ Src.stale) :
    pagesView (GF := GF) W.data W.ps W.q W.pages ∗ ([∗list] it;w ∈ ins;ws, wOwn W it w) ∗
      ([∗list] it;w ∈ pins;pws, wOwn W it w) ∗ (if P then True else srcOwn W os osrc okb) ⊢
    ∃ (es : List NodeEntry) (s1 s2 s3 : Src) (dnk dok : DFrac),
      ⌜wMatch pws es ∧ s1 ≠ Src.stale ∧ s2 ≠ Src.stale ∧ s3 ≠ Src.stale ∧
        (w0.ks ≠ Src.view → s1 ≠ Src.view ∧ s2 ≠ Src.view ∧ s3 ≠ Src.view)⌝ ∗
      inodesOwn pins es ∗ it0.key' ↦*{dnk} w0.key ∗
      (if P then it0.key' else os) ↦*{dok} (if P then w0.key else okb) ∗
      (∀ (idx : Nat) (b : Bool) (pg : w64), ⌜b = true → idx < pins.length⌝ -∗
        inodesOwn (putList pins idx b (Inode.mk (W32 0) pg it0.key' slice.nil))
          (putList es idx b (NodeEntry.mk (W32 0) pg w0.key [] dnk (DFrac.own 1))) -∗
        (if b then (∃ (it : Inode) (e : NodeEntry), ⌜pins[idx]? = some it ∧ es[idx]? = some e⌝ ∗
          inodeIs it e) else True) -∗
        (if P then it0.key' else os) ↦*{dok} (if P then w0.key else okb) -∗
        pagesView W.data W.ps W.q W.pages ∗
        ([∗list] it;w ∈ ins;ws.set 0 { w0 with ks := s1 }, wOwn W it w) ∗ srcOwn W it0.key' s3 w0.key ∗
        [∗list] it;w ∈ putList pins idx b (Inode.mk (W32 0) pg it0.key' slice.nil);
          putList pws idx b (⟨W32 0, pg, w0.key, [], s2, Src.own (DFrac.own 1)⟩ : WEntry), wOwn W it w) := by
  iintro ⟨Hpv, Hxe, Hpe, Ho⟩
  have hq : W.q = W.q.half + (W.q.half.half + W.q.half.half) := by
    rw [Qp.half_add_half, Qp.half_add_half]
  icases (pagesView_split' W.data W.ps W.pages _ _ _ hq).1 $$ Hpv with ⟨Hp1, Hp23⟩
  icases (pagesView_split W.data W.ps W.pages _ _).1 $$ Hp23 with ⟨Hp2, Hp3⟩
  icases BigSepL2.bigSepL2_insert_acc (Φ := fun _ it w => wOwn (GF := GF) W it w) h0i h0w $$ Hxe
    with ⟨Hw0, Hxback⟩
  isimp only [wOwn] at Hw0
  icases Hw0 with ⟨%hfp, Hk0, Hv0⟩
  icases spSrcOwn_three W it0.key' w0.ks w0.key hw0 $$ Hk0 with ⟨%s1, %s2, %s3, %hs, Hk1, Hk2, Hk3⟩
  icases srcBorrowD W hc W.q.half.half it0.key' s2 w0.key hs.2.1 $$ [Hp2 Hk2] with ⟨Hn, Hnback⟩
  · iframe
  icases nodeBorrow W hc pws pins W.q.half hlive $$ [Hp1 Hpe] with ⟨%es, %hm, Hes, Hpback⟩
  · iframe
  have hil : pins.length = es.length := hpl.trans (wMatch_length hm)
  have hset : ins.set 0 it0 = ins := list_set_lookup_self ins 0 it0 h0i
  by_cases hP : P
  · simp only [hP, ↓reduceIte]
    icases srcBorrowD W hc W.q.half.half it0.key' s3 w0.key hs.2.2.1 $$ [Hp3 Hk3] with ⟨Hoo, Hooback⟩
    · iframe
    iexists es, s1, s2, s3, srcFrac s2 W.q.half.half, srcFrac s3 W.q.half.half
    iframe Hes Hn Hoo
    isplitr
    · ipureintro; exact ⟨hm, hs⟩
    iintro %idx %b %pg %hb Hes' Hold Hoo
    ihave Hes := inodesOwn_unput pins es idx b _ _ hil $$ [Hes' Hold]
    · iframe
    icases Hes with ⟨Hes, Hx⟩
    ihave Hpe := Hpback $$ Hes
    icases Hpe with ⟨Hp1, Hpe⟩
    isimp only [inodeIs] at Hx
    icases Hx with ⟨-, Hn, Hv⟩
    ihave Hk2 := Hnback $$ Hn
    icases Hk2 with ⟨Hp2, Hk2⟩
    ihave Hp3 := Hooback $$ Hoo
    icases Hp3 with ⟨Hp3, Hk3⟩
    ihave Hp23 := (pagesView_split W.data W.ps W.pages _ _).2 $$ [Hp2 Hp3]
    · iframe
    ihave Hpv := (pagesView_split' W.data W.ps W.pages _ _ _ hq).2 $$ [Hp1 Hp23]
    · iframe
    iframe Hpv Hk3
    isplitl [Hxback Hk1 Hv0]
    · ihave Hw : wOwn (GF := GF) W it0 { w0 with ks := s1 } $$ [Hk1 Hv0]
      · unfold wOwn; iframe; ipureintro; exact hfp
      ihave Hx := Hxback $$ %it0 %{ w0 with ks := s1 } Hw
      rw [hset]
      iexact Hx
    iapply bigSepL2_putList (fun it w => wOwn (GF := GF) W it w) pins pws idx b _ _ hpl hb
    iframe Hpe
    unfold wOwn srcOwn
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  · simp only [hP, ↓reduceIte]
    icases srcBorrowD W hc W.q.half.half os osrc okb (hos hP) $$ [Hp3 Ho] with ⟨Hoo, Hooback⟩
    · iframe
    iexists es, s1, s2, s3, srcFrac s2 W.q.half.half, srcFrac osrc W.q.half.half
    iframe Hes Hn Hoo
    isplitr
    · ipureintro; exact ⟨hm, hs⟩
    iintro %idx %b %pg %hb Hes' Hold Hoo
    ihave Hes := inodesOwn_unput pins es idx b _ _ hil $$ [Hes' Hold]
    · iframe
    icases Hes with ⟨Hes, Hx⟩
    ihave Hpe := Hpback $$ Hes
    icases Hpe with ⟨Hp1, Hpe⟩
    isimp only [inodeIs] at Hx
    icases Hx with ⟨-, Hn, Hv⟩
    ihave Hk2 := Hnback $$ Hn
    icases Hk2 with ⟨Hp2, Hk2⟩
    ihave Hp3 := Hooback $$ Hoo
    icases Hp3 with ⟨Hp3, -⟩
    ihave Hp23 := (pagesView_split W.data W.ps W.pages _ _).2 $$ [Hp2 Hp3]
    · iframe
    ihave Hpv := (pagesView_split' W.data W.ps W.pages _ _ _ hq).2 $$ [Hp1 Hp23]
    · iframe
    iframe Hpv Hk3
    isplitl [Hxback Hk1 Hv0]
    · ihave Hw : wOwn (GF := GF) W it0 { w0 with ks := s1 } $$ [Hk1 Hv0]
      · unfold wOwn; iframe; ipureintro; exact hfp
      ihave Hx := Hxback $$ %it0 %{ w0 with ks := s1 } Hw
      rw [hset]
      iexact Hx
    iapply bigSepL2_putList (fun it w => wOwn (GF := GF) W it w) pins pws idx b _ _ hpl hb
    iframe Hpe
    unfold wOwn srcOwn
    iframe
    ipureintro; exact ⟨rfl, rfl⟩

/-- The transaction's stats out of the spill's state, and back changed. -/
theorem spSpillR_stats (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) :
    spillR I γd γ W txl txid T ρ F K ⊢
      structFieldRef Tx go!"stats" txl ↦ T.t.stats' ∗
      (∀ st, structFieldRef Tx go!"stats" txl ↦ st -∗
        spillR I γd γ W txl txid { T with t := { T.t with stats' := st } } ρ F K) := by
  unfold spillR ownWriteTxGX TxW_rest_root
  iintro ⟨Hdb, ⟨⟨Hw, Hma, Hd, Hme, Hpg, Hst, Hch, Hwf, %Hn⟩, Hm, Hpm, Hbufs, Hbs⟩, Hv, Hcaps, Hgh, HF⟩
  iframe Hst
  iintro %st Hst
  have e1 : capsOwn (GF := GF) { T with t := { T.t with stats' := st } } K = capsOwn T K := rfl
  have e2 : spillPages W { T with t := { T.t with stats' := st } } = spillPages W T := rfl
  rw [e1, e2]
  iframe
  ipureintro; exact Hn

/-- The stats changed: the spill's facts kept. -/
theorem spSpillG_stats (W : WView) (txl : Loc) (txid : w64) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (st : TxStats) (hg : spillG (hG := hG) W txl txid T ρ F) :
    spillG (hG := hG) W txl txid { T with t := { T.t with stats' := st } } ρ F := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, htx, hd, hu, hf, hr⟩ := hg
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, htx, hd, hu, hf, derefReadyX_bs T _ _ rfl hr⟩

/-- Two nodes of a bucket's map, taken out (`a`, then `b`), put back changed. -/
theorem spBigSepM_ins2 (Φ : Loc → NRec → IProp GF) (m : GMap Loc NRec) (a b : Loc) (xa xb : NRec)
    (hab : a ≠ b) :
    Φ a xa ∗ Φ b xb ∗ ([∗map] k ↦ v ∈ Std.delete (Std.delete m a) b, Φ k v) ⊢
      [∗map] k ↦ v ∈ <[a := xa]> (<[b := xb]> m), Φ k v := by
  iintro ⟨Ha, Hb, H⟩
  ihave H := (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := Φ) (m := Std.delete m a) (i := b)
    (x := xb)).2 $$ [Hb H]
  · iframe
  iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := Φ) (m := <[b := xb]> m) (i := a)
    (x := xa)).2
  iframe Ha
  have e : Std.delete (<[b := xb]> m) a = Std.insert (Std.delete m a) b xb :=
    GMap.delete_insert_ne m xb hab
  rw [e]
  iexact H

/-- `spBigSepM_ins2`, taken out `b` first. -/
theorem spBigSepM_ins2' (Φ : Loc → NRec → IProp GF) (m : GMap Loc NRec) (a b : Loc) (xa xb : NRec)
    (hab : a ≠ b) :
    Φ a xa ∗ Φ b xb ∗ ([∗map] k ↦ v ∈ Std.delete (Std.delete m b) a, Φ k v) ⊢
      [∗map] k ↦ v ∈ <[a := xa]> (<[b := xb]> m), Φ k v := by
  have e : Std.delete (Std.delete m b) a = Std.delete (Std.delete m a) b := GMap.delete_commute m a b
  rw [e]
  exact spBigSepM_ins2 Φ m a b xa xb hab

/-- A node without children (`r.cs = []`): its struct out of the spill's state, and back with its
`children` nil. -/
theorem spSpillRNilKids (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (n : Loc) (r : NRec) (hB : T.bs !! bl = some B) (hn : B.ns !! n = some r)
    (hcs : r.cs = []) :
    spillR I γd γ W txl txid T ρ F K ⊢
      n ↦ r.nv ∗
      (n ↦ ({ r.nv with children' := slice.nil } : node) -∗
        spillR I γd γ W txl txid
          (setB T bl (setN B n { r with nv := { r.nv with children' := slice.nil } })) ρ F K) := by
  unfold spillR ownWriteTxGX capsOwn
  iintro ⟨Hdb, ⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩, Hv, Hcaps, Hgh, HF⟩
  have hB' : Std.get? T.bs bl = some B := hB
  have hn' : Std.get? B.ns n = some r := hn
  icases (BigSepM.bigSepM_insert_acc (M := GMap Loc) (Φ := fun bl B => bktOwnX (GF := GF) W bl B) hB')
    $$ Hbs with ⟨Hb, Hbback⟩
  unfold bktOwnX
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  icases (BigSepM.bigSepM_insert_acc (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r) hn')
    $$ Hns with ⟨Hnd, Hnsback⟩
  unfold nodeOwnX
  icases Hnd with ⟨Hn, Hins, Hents, Hch, Hcc, Hk⟩
  icases (BigSepM.bigSepM_insert_acc (M := GMap Loc)
    (Φ := fun _ B => iprop([∗map] l ↦ r ∈ B.ns, if K l then iprop(emp) else capOwn (GF := GF) r)) hB')
    $$ Hcaps with ⟨Hcb, Hcback⟩
  icases (BigSepM.bigSepM_insert_acc (M := GMap Loc)
    (Φ := fun l r => if K l then iprop(emp) else capOwn (GF := GF) r) hn') $$ Hcb with ⟨Hcn, Hcnback⟩
  iframe Hn
  iintro Hn
  ihave Hnd : nodeOwnX (GF := GF) W n { r with nv := { r.nv with children' := slice.nil } } $$
      [Hn Hins Hents Hk]
  · unfold nodeOwnX
    dsimp only
    rw [hcs]
    iframe
    isplitl []
    · iapply ownSlice_nil
    iapply ownSliceCap_nil
  ihave Hns := Hnsback $$ %({ r with nv := { r.nv with children' := slice.nil } } : NRec) [Hnd]
  · unfold nodeOwnX; iexact Hnd
  ihave Hb : bktOwnX (GF := GF) W bl (setN B n { r with nv := { r.nv with children' := slice.nil } }) $$
      [Hbv Hib Hnm Hbm Hpo Hns]
  · unfold bktOwnX setN
    rw [show pageOwn W { B with ns := <[n := { r with nv := { r.nv with children' := slice.nil } }]> B.ns } =
      pageOwn W B from rfl]
    unfold nodeOwnX
    dsimp only
    iframe
  ihave Hbs := Hbback $$ %(setN B n { r with nv := { r.nv with children' := slice.nil } }) [Hb]
  · unfold bktOwnX nodeOwnX; iexact Hb
  ihave Hcb := Hcnback $$ %({ r with nv := { r.nv with children' := slice.nil } } : NRec) [Hcn]
  · unfold capOwn; dsimp only; iexact Hcn
  ihave Hcaps := Hcback $$ %(setN B n { r with nv := { r.nv with children' := slice.nil } }) [Hcb]
  · unfold setN; iexact Hcb
  have e1 : spillPages W (setB T bl (setN B n { r with nv := { r.nv with children' := slice.nil } })) =
      spillPages W T := rfl
  rw [e1]
  unfold setB
  iframe

/-- A node's children sorted: the spill's facts kept. -/
theorem spSpillG_sort (W : WView) (txl : Loc) (txid : w64) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (bl : Loc) (B : BRec) (n : Loc) (r : NRec) (ys : List Loc)
    (hg : spillG (hG := hG) W txl txid T ρ F) (hB : T.bs !! bl = some B) (hn : B.ns !! n = some r)
    (hp : ys.Perm r.cs) :
    spillG (hG := hG) W txl txid (setB T bl (setN B n { r with cs := ys })) ρ F := by
  have hg0 := hg
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hd⟩ := hg0
  obtain ⟨-, -, -, hbk⟩ := hd
  have hlv := (hbk bl B hB).1
  apply spillG_setB W txl txid T ρ F bl B (setN B n { r with cs := ys }) hg hB rfl rfl
  have hfw : ∀ l rl, B.ns !! l = some rl → ∃ rl', (<[n := { r with cs := ys }]> B.ns) !! l = some rl' ∧
      rl'.nv = rl.nv ∧ rl'.ws = rl.ws ∧ rl'.ksrc = rl.ksrc ∧ rl'.ins = rl.ins ∧ rl'.key = rl.key := by
    intro l rl h
    by_cases e : l = n
    · subst e; rw [hn] at h; cases h
      exact ⟨_, GMap.lookup_insert _ _ _, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rl, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact h, rfl, rfl, rfl, rfl, rfl⟩
  rcases hlv with h0 | ⟨S, ⟨p, top, hup, hpn, hkt, hnv⟩, hok⟩
  · exact Or.inl h0
  · right
    obtain ⟨S', hk', hperm'⟩ := spKidsTree_perm B.ns n r ys hn hp S.length top S (Nat.le_refl _) hkt
    refine ⟨S', ⟨p, top, upPath_par _ _ hup (fun x _ rx hrx => ?_), hpn, hk', fun l hl hlS => ?_⟩,
      fun l hl => ?_⟩
    · obtain ⟨rl', h1, h2, -⟩ := hfw x rx hrx
      exact ⟨rl', h1, by rw [h2]⟩
    · obtain ⟨r0, hr0, hnv0⟩ := hnv l hl (fun h => hlS (hperm'.mem_iff.2 h))
      obtain ⟨rl', h1, -, h3, h4, -⟩ := hfw l r0 hr0
      refine ⟨rl', h1, fun w hw => ?_, by rw [h4]; exact hnv0.2⟩
      rw [h3] at hw; exact hnv0.1 w hw
    · obtain ⟨r0, hr0, hok0⟩ := hok l (hperm'.mem_iff.1 hl)
      obtain ⟨rl', h1, h2, h3, h4, h5, h6⟩ := hfw l r0 hr0
      refine ⟨rl', h1, ?_⟩
      unfold derefOK at hok0 ⊢
      rw [h2, h3, h4, h5, h6]; exact hok0

/-- A node's children sorted: the heights kept. -/
theorem spNodeHts_sort (B : BRec) (ht : Loc → Nat) (n : Loc) (r : NRec) (ys : List Loc)
    (hn : B.ns !! n = some r) (h : nodeHts B ht) : nodeHts (setN B n { r with cs := ys }) ht := by
  intro l rl hl hs
  change (<[n := { r with cs := ys }]> B.ns) !! l = some rl at hl
  by_cases e : l = n
  · subst e; rw [GMap.lookup_insert] at hl; cases hl
    exact h l r hn hs
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl
    exact h l rl hl hs

/-- The children loop's start: `node.spill`'s node, its children sorted to `ys`. -/
theorem spLoopStart (W : WView) (txl : Loc) (txid : w64) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat) (N : Nat) (n : Loc)
    (r : NRec) (sp : Loc → Bool) (sub : Loc → List Loc) (ys : List Loc)
    (hg : spillG (hG := hG) W txl txid T ρ F) (hB : T.bs !! bl = some B) (hn : B.ns !! n = some r)
    (hK : K n = false) (hL : nodeL W bl B bnd kd n r)
    (hch : ∀ c ∈ r.cs, kidsTree B.ns c (sub c) ∧ (sp c = true → spilledN bl B c) ∧
      (sp c = false → (sub c).length < N ∧ subU W bl B bnd kd K c (sub c)))
    (hkt : kidsTree B.ns n (n :: (r.cs.map sub).flatten))
    (hel : ∀ l r, B.ns !! l = some r → ∀ w ∈ r.ws, w.key.length + w.value.length ≤ 2 ^ 28)
    (hne : ∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → 0 < r.ws.length)
    (hP1 : ∀ l r, B.ns !! l = some r → l ≠ n → r.nv.isLeaf' = false → r.nv.pgid' ≠ W64 0)
    (hP2 : ∀ c l, B.nm !! c = some l → c = W64 0 ∨ (W.pages !! uint.nat c).isSome)
    (hP3 : ∀ l r w, B.ns !! l = some r → r.nv.isLeaf' = false → w ∈ r.ws →
      (spillPages W T !! uint.nat w.pgid).isSome)
    (hperm : ys.Perm r.cs) :
    loopP (hG := hG) bl bnd kd ht N n txl txid W T B r K (n :: (r.cs.map sub).flatten)
      W (setB T bl (setN B n { r with cs := ys })) ρ F K (setN B n { r with cs := ys })
      { r with cs := ys } 0 sp sub := by
  have hnc : n ∉ r.cs := spKids_notin B.ns n r.cs sub hkt (fun c hc => (hch c hc).1)
  have hcnd : r.cs.Nodup := spCs_nodup W bl B bnd kd n r hL
  have hnsub := spKids_notsub B.ns n r.cs sub hkt
  have hlk : ∀ l rl, (setN B n { r with cs := ys }).ns !! l = some rl →
      (l = n ∧ rl = { r with cs := ys }) ∨ (l ≠ n ∧ B.ns !! l = some rl) := by
    intro l rl h
    change (<[n := { r with cs := ys }]> B.ns) !! l = some rl at h
    by_cases e : l = n
    · subst e; rw [GMap.lookup_insert] at h; cases h; exact Or.inl ⟨rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h; exact Or.inr ⟨e, h⟩
  have hne' : ∀ l, l ≠ n → (setN B n { r with cs := ys }).ns !! l = B.ns !! l := fun l e =>
    GMap.lookup_insert_ne _ _ (Ne.symm e)
  have hS0 : (n :: ((r.cs.map sub).flatten)).Perm (n :: ((ys.map sub).flatten)) :=
    ((hperm.map sub).flatten).symm.cons n
  have hnd0 := (spKidsTree_mem _ _ _ hkt).2
  -- a child's tree in the sorted bucket
  have hsubU : ∀ c ∈ r.cs, ∀ S, kidsTree B.ns c S → n ∉ S → subU W bl B bnd kd K c S →
      subU W bl (setN B n { r with cs := ys }) bnd kd K c S := by
    intro c hc S hk hnS hU
    refine ⟨spKidsTree_ins B.ns n _ c S hk hnS, fun x hx => ?_⟩
    obtain ⟨hKx, rx, hrx, hux⟩ := hU.2 x hx
    have hxn : x ≠ n := fun e => hnS (e ▸ hx)
    refine ⟨hKx, rx, by rw [hne' x hxn]; exact hrx, ?_⟩
    refine nodeU_keep W W bl B _ bnd kd x rx rx rfl rfl (Or.inl rfl) (fun c' rc hc' hrc => ?_) hux
    have hc'S := spKidsTree_cs B.ns S.length c S (Nat.le_refl _) hk x hx rx hrx c' hc'
    exact ⟨rc, by rw [hne' c' (fun e => hnS (e ▸ hc'S))]; exact hrc, Or.inl rfl⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hL
  refine ⟨spSpillG_sort W txl txid T ρ F bl B n r ys hg hB hn hperm, GMap.lookup_insert _ _ _,
    GMap.lookup_insert _ _ _, hK, spillFrame_setB T bl _ (by rw [hB]; rfl), rfl, rfl,
    GMap.map_subseteq_refl _, rfl, rfl, rfl, rfl, rfl, rfl, fun h => h, Or.inl rfl, ?_, ?_,
    fun l rl hl e => ?_, Nat.zero_le _, hperm.nodup_iff.2 hcnd, fun h => hnc (hperm.mem_iff.1 h),
    fun j c h => absurd h (Nat.not_lt_zero _), fun c hc => ?_, ?_, fun x hx => ?_,
    fun c hc _ x hx => ?_, fun x rx hx hrx => ?_, fun x hx => ?_, fun x hx hs => ?_,
    ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩, fun hT => treeOK_perm_cs bl B n r ys hT hn hperm,
    spNodeHts_sort B ht n r ys hn, fun x hx => ?_, fun h _ => h⟩
  · -- nodeL
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun hl => ?_, fun hl => ?_⟩
    · show ys = []; rw [h9 hl] at hperm; exact List.perm_nil.1 hperm
    · obtain ⟨b1, b2, b3, b4, b5⟩ := h10 hl
      refine ⟨b1, b2, hperm.nodup_iff.2 b3, fun i w c hw hnm => ?_, fun c hc => ?_⟩
      · obtain ⟨rc, hrc, e1, e2, e3, e4, hcm, e5⟩ := b4 i w c hw hnm
        have hcn : c ≠ n := fun e => hnc (e ▸ hcm)
        exact ⟨rc, by rw [hne' c hcn]; exact hrc, e1, e2, e3, e4, hperm.mem_iff.2 hcm, e5⟩
      · have hc' : c ∈ r.cs := hperm.mem_iff.1 hc
        have hcn : c ≠ n := fun e => hnc (e ▸ hc')
        rcases b5 c hc' with h | hs
        · exact Or.inl h
        · obtain ⟨rc, hrc, -⟩ := id hs
          exact Or.inr (spilledN_keep bl B _ c rc rc hs hrc (by rw [hne' c hcn]; exact hrc) (Or.inl rfl) rfl)
  · -- nodesOK
    refine ⟨fun l rl hl => ?_, fun l rl hl => ?_, hP2, fun l rl w hl => ?_⟩
    · rcases hlk l rl hl with ⟨rfl, rfl⟩ | ⟨-, h⟩
      · exact hel _ r hn
      · exact hel l rl h
    · rcases hlk l rl hl with ⟨rfl, rfl⟩ | ⟨-, h⟩
      · exact hne _ r hn
      · exact hne l rl h
    · rcases hlk l rl hl with ⟨rfl, rfl⟩ | ⟨-, h⟩
      · exact hP3 _ r w hn
      · exact hP3 l rl w h
  · rcases hlk l rl hl with ⟨rfl, -⟩ | ⟨-, h⟩
    · exact absurd rfl e
    · exact hP1 l rl h e
  · -- the children's trees
    have hc' : c ∈ r.cs := hperm.mem_iff.1 (by simpa using hc)
    obtain ⟨hk, hs, hu⟩ := hch c hc'
    refine ⟨spKidsTree_ins B.ns n _ c (sub c) hk (hnsub c hc'), fun hsp => ?_, fun hsp => ?_⟩
    · have hsn := hs hsp
      obtain ⟨rc, hrc, -⟩ := id hsn
      have hcn : c ≠ n := fun e => hnc (e ▸ hc')
      exact spilledN_keep bl B _ c rc rc hsn hrc (by rw [hne' c hcn]; exact hrc) (Or.inl rfl) rfl
    · obtain ⟨hlt, hU⟩ := hu hsp
      exact ⟨hlt, hsubU c hc' (sub c) hk (hnsub c hc') hU⟩
  · simpa using hS0.nodup_iff.1 hnd0
  · left
    exact List.mem_cons_of_mem _ ((hperm.map sub).flatten.mem_iff.1 (by simpa using hx))
  · exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨sub c, List.mem_map_of_mem (hperm.mem_iff.1
      (by simpa using hc)), hx⟩)
  · have hxn : x ≠ n := fun e => hx (e ▸ List.mem_cons_self ..)
    exact ⟨rx, by rw [hne' x hxn]; exact hrx, Or.inl rfl⟩
  · by_cases e : x = n
    · subst e; left; rw [hn]; rfl
    · left; rw [← hne' x e]; exact hx
  · rcases List.mem_cons.1 hx with rfl | hx'
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (by simpa using ((hperm.map sub).flatten.mem_iff.2 hx')))
  · have hx' : x ∈ r.cs := hperm.mem_iff.1 hx
    exact Or.inl (List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨sub x, List.mem_map_of_mem hx',
      (spKidsTree_mem _ _ _ (hch x hx').1).1⟩))

/-- The parts all written: the first part `n`, spilled under `par`, and the parent. -/
theorem spPartsExit (bl txl : Loc) (txid : w64) (n : Loc) (rc : NRec)
    (xs : List (Loc × node × List Inode)) (par : Loc) (ws0 : List WEntry) (i0 : Nat)
    (lo hi : Option (List w8)) (Ws : WView) (Ts : WTx) (Bs : BRec) (Ks : Loc → Bool)
    (W : WView) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (B : BRec)
    (ps : List (w64 × List w8))
    (hpp : partsP (hG := hG) bl txl txid n rc xs par ws0 i0 lo hi Ws Ts Bs Ks W T ρ F K B ps)
    (hst : startP bl n rc xs par Bs ws0 i0) (hpx : ps.length = xs.length) :
    ∃ rn5, B.ns !! n = some rn5 ∧ rn5.nv.parent' = par ∧ rn5.cs = [] ∧
      (par ≠ null → ∃ rq, B.ns !! par = some rq ∧ par ≠ n) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hw, -, -, -, -, hparc, -⟩ := hpp
  obtain ⟨hne, -, hhd, -⟩ := hst
  obtain ⟨x0, rest, rfl⟩ : ∃ x0 rest, xs = x0 :: rest := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons x0 rest => exact ⟨x0, rest, rfl⟩
  have hx0 : x0.1 = n := by simpa using hhd
  have h0 : 0 < ps.length := by rw [hpx]; simp
  obtain ⟨-, rx, p, hrx, -, hcs, -, -, -, -, -, hpar, -, -⟩ := hw 0 n h0 (by simp [hx0])
  refine ⟨rx, hrx, hpar, hcs, fun hp => ?_⟩
  obtain ⟨rq, hrq, -, -, -, -, -, -, hnot, -⟩ := hparc hp
  refine ⟨rq, hrq, fun e => hnot ?_⟩
  rw [e]; exact List.mem_map.2 ⟨x0, List.mem_cons_self .., hx0⟩

/-- The parent of a node at its children loop's end: present (kept or dereferenced), not a child,
with the node's entry. -/
theorem spParentAtCut (bl : Loc) (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat)
    (N : Nat) (n txl : Loc) (txid : w64) (W : WView) (T : WTx) (B : BRec) (r : NRec)
    (K : Loc → Bool) (S0 : List Loc) (W' : WView) (T' : WTx) (ρ' : DBState)
    (F' : GMap Nat (List w8)) (K' : Loc → Bool) (B' : BRec) (rn : NRec) (i : Nat)
    (sp : Loc → Bool) (sub : Loc → List Loc)
    (hlp : loopP (hG := hG) bl bnd kd ht N n txl txid W T B r K S0 W' T' ρ' F' K' B' rn i sp sub)
    (hn : B.ns !! n = some r) (hL : nodeL W bl B bnd kd n r) (hnS : n ∈ S0) (pl : Loc) (rp0 : NRec)
    (hrp0 : B.ns !! pl = some rp0) (hplS : pl ∉ S0) (hLp : nodeL W bl B bnd kd pl rp0)
    (hbr : rp0.nv.isLeaf' = false) (hin : n ∈ rp0.cs) :
    ∃ rp, B'.ns !! pl = some rp ∧ wsLive rp.ws ∧ rp.ins.length = rp.ws.length ∧ wsSorted rp.ws ∧
      rp.nv.bucket' = bl ∧ pl ∉ rn.cs ∧ pl ≠ n ∧
      ∃ (i : Nat) (w : WEntry), rp.ws[i]? = some w ∧ w.key = r.key ∧ w.pgid = r.nv.pgid' ∧
        r.nv.key' ≠ slice.nil ∧ bndIn (bnd n) (entryBnd (bnd pl) rp.ws i) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hkeep, -, -, -, -, -,
    hI1, -⟩ := hlp
  obtain ⟨rp, hrp, hdn⟩ := hkeep pl rp0 hplS hrp0
  have hplc : pl ∉ rn.cs := fun h => (hI1 pl h).elim hplS (fun h' => by rw [hrp0] at h'; cases h')
  have hpln : pl ≠ n := fun e => hplS (e ▸ hnS)
  obtain ⟨h1, -, h3, h4, -, h6, -, -, -, h10⟩ := hLp
  obtain ⟨-, -, -, hmap, hcov⟩ := h10 hbr
  obtain ⟨j, w, hw, hnm⟩ : ∃ (j : Nat) (w : WEntry), rp0.ws[j]? = some w ∧ B.nm !! w.pgid = some n := by
    rcases hcov n hin with h | ⟨r1, hr1, hs1, -⟩
    · exact h
    · rw [hn] at hr1; cases hr1; rw [hL.2.1] at hs1; cases hs1
  obtain ⟨rc, hrc, -, hpg, hk, hkn, -, -, hbnd⟩ := hmap j w n hw hnm
  rw [hn] at hrc; cases hrc
  rcases hdn with rfl | ⟨⟨⟨-, hws, -, -, -, -, hil⟩, -⟩, hnv⟩
  · exact ⟨_, hrp, h6, h3, h4, h1, hplc, hpln, j, w, hw, hk.symm, hpg.symm, hkn, hbnd⟩
  · refine ⟨rp, hrp, fun w' hw' => ?_, hil, ?_, by rw [hnv]; exact h1, hplc, hpln, j, ownFresh w,
      by rw [hws, List.getElem?_map, hw]; rfl, hk.symm, hpg.symm, hkn, ?_⟩
    · rw [hws] at hw'
      obtain ⟨w0, -, rfl⟩ := List.mem_map.1 hw'
      exact ⟨nofun, nofun⟩
    · unfold wsSorted at h4 ⊢; rw [hws, wKey_fresh, List.length_map]; exact h4
    · rw [hws]; unfold entryBnd; rw [wKey_fresh, List.length_map]; exact hbnd

/-- A page of the view is not dirty. -/
theorem spDirty_pm_none (ρ : DBState) (W : WView) (T : WTx) (id : w64) (pg : List w8)
    (hd : spillDirty ρ W T) (hw : W.pages !! uint.nat id = some pg) : T.pm !! id = none := by
  cases h : T.pm !! id with
  | none => rfl
  | some p =>
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ((hd.1 id).1 (by rw [h]; rfl))
    obtain ⟨-, -, -, -, hk⟩ := hd.2.1 id b hb
    exact absurd ⟨uint.nat id, pg, hw, Nat.le_add_right _ _, by omega⟩ (hk 0 (dspan_pos b)).2.2.1

/-- The split's parts fit a page write (`split_fit`), as their chunks of entries. -/
theorem spSplitLayout [go.FloatConvSemantics] (rc : NRec) (xs : List (Loc × node × List Inode)) (thr ps : w64)
    (hthr : uint.Z thr ≤ uint.Z ps) (hps : uint.Z ps < 2 ^ 20) (hidx : splitIdxOK thr xs)
    (hlast : lastFits ps xs) (hflat : (xs.map (fun x => x.2.2)).flatten = rc.ins)
    (hil : rc.ins.length = rc.ws.length)
    (hlens : ∀ (i : Nat) (it : Inode) (w : WEntry), rc.ins[i]? = some it → rc.ws[i]? = some w →
      uint.nat it.key'.len = w.key.length ∧ uint.nat it.value'.len = w.value.length)
    (hel : ∀ w ∈ rc.ws, w.key.length + w.value.length ≤ 2 ^ 28) (hlen : rc.ins.length < 2 ^ 64) :
    ∀ (j : Nat) (xe : Loc × node × List Inode), xs[j]? = some xe →
      spLayoutW ((chunksOf rc xs).getD j []) ≤ 2147483647 ∧ xe.2.2.length < 65535 := by
  have hel' : ∀ x ∈ xs, ∀ it ∈ x.2.2, inodeKV it ≤ 2 ^ 28 := by
    intro x hx it hit
    have hm : it ∈ rc.ins := by rw [← hflat]; exact List.mem_flatten.2 ⟨x.2.2, List.mem_map_of_mem hx, hit⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
    have hil' : i < rc.ws.length := by rw [← hil]; exact (List.getElem?_eq_some_iff.1 hi).1
    obtain ⟨h1, h2⟩ := hlens i it _ hi (List.getElem?_eq_getElem hil')
    have := hel _ (List.getElem_mem hil')
    unfold inodeKV; omega
  have hlen' : ∀ x ∈ xs, x.2.2.length < 2 ^ 64 := by
    intro x hx
    have := spLen_le_flatten (xs.map (fun x => x.2.2)) x.2.2 (List.mem_map_of_mem hx)
    rw [hflat] at this; omega
  have hfit := split_fit thr ps hthr hps xs hidx hlast hel' hlen'
  have hmap : (xs.map (fun x => x.2.2)).map List.length = xs.map (fun x => x.2.2.length) := by
    rw [List.map_map]; rfl
  have hsum : (xs.map (fun x => x.2.2.length)).sum ≤ rc.ws.length := by
    rw [← hil, ← hflat, List.length_flatten, hmap]; exact Nat.le_refl _
  intro j xe hxe
  obtain ⟨hl65, hlay⟩ := hfit xe (List.mem_of_getElem? hxe)
  have hk : (xs.map (fun x => x.2.2.length))[j]? = some xe.2.2.length := by
    rw [List.getElem?_map, hxe]; rfl
  obtain ⟨hcl, -⟩ := wsChunks_get rc.ws _ j _ hk hsum
  have hrel := spChunk_rel (R := fun it w => uint.nat it.key'.len = w.key.length ∧
      uint.nat it.value'.len = w.value.length) (xs.map (fun x => x.2.2)) rc.ws
    (by rw [hflat]; exact hlens) j xe.2.2 (by rw [List.getElem?_map, hxe]; rfl)
  rw [hmap] at hrel
  have heq := spLayout_eq xe.2.2 ((chunksOf rc xs).getD j []) hcl.symm hrel
  rw [← heq]; exact ⟨hlay, hl65⟩

/-- The inodes' flags and page ids, the entries'. -/
theorem spWOwns_fp (W : WView) : ∀ (ins : List Inode) (ws : List WEntry),
    ([∗list] it;w ∈ ins;ws, wOwn (GF := GF) W it w) ⊢
      ⌜∀ (i : Nat) (it : Inode) (w : WEntry), ins[i]? = some it → ws[i]? = some w →
        it.flags' = w.flags ∧ it.pgid' = w.pgid⌝
  | [], _ => by
    iintro -; ipureintro; intro i it w h; simp at h
  | it :: ins, [] => by
    iintro -; ipureintro; intro i it' w _ h; simp at h
  | it :: ins, w :: ws => by
    iintro H
    icases BigSepL2.bigSepL2_cons.1 $$ H with ⟨Hw, H⟩
    isimp only [wOwn] at Hw
    icases Hw with ⟨%h0, -⟩
    ihave %h := spWOwns_fp W ins ws $$ H
    ipureintro
    intro i it' w' h1 h2
    cases i with
    | zero => simp at h1 h2; subst h1; subst h2; exact h0
    | succ i => exact h i it' w' (by simpa using h1) (by simpa using h2)

theorem spSpillPages_mono (W W' : WView) (T T' : WTx) (hp : W'.pages = W.pages)
    (hb : T.bufs ⊆ T'.bufs) : spillPages W T ⊆ spillPages W' T' := by
  intro k v h
  unfold spillPages at h ⊢
  rw [hp]
  simp only [GMap.lookup_union] at h ⊢
  cases hw : W.pages !! k with
  | some pg => rw [hw] at h; exact h
  | none =>
    rw [hw] at h
    simp only [Option.none_or] at h ⊢
    rw [bufsN_lookup] at h ⊢
    split at h
    · rw [if_pos ‹_›]; exact hb _ _ h
    · cases h

theorem spSpillPages_buf_at (W : WView) (T : WTx) (id : w64) (b : List w8)
    (hw : W.pages !! uint.nat id = none) (hb : T.bufs !! id = some b) :
    spillPages W T !! uint.nat id = some b := by
  unfold spillPages
  simp only [GMap.lookup_union]
  rw [hw]
  simp only [Option.none_or]
  rw [bufsN_lookup, if_pos (by unfold uint.nat; word)]
  have e : W64 ((uint.nat id : Nat) : Int) = id := by unfold uint.nat; word
  rw [e]; exact hb

end own

end bbolt
end EtcdGrove
end Perennial
