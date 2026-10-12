/-
A leaf's entries changed (`Bucket.Put`, `Bucket.Delete`: `node.put`, `node.del` on the leaf a
cursor found): the bucket stays clean (`bktClean_leafSet`), the entries stay sorted
(`wsSorted_putList`, `wsSorted_eraseIdx`), and the node's ownership is rebuilt from what the
node specs give back (`inodesOwn_unput`, `inodesOwn_undel`, `wOwnL_put`, `wOwnL_del`).
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxClean

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section order

theorem goStringLt_irrefl_w : ∀ (a : List w8), ¬ go.GoStringLt a a
  | [], h => by cases h
  | x :: xs, h => by
    cases h with
    | cons h' => exact goStringLt_irrefl_w xs h'
    | rel h' => exact Int.lt_irrefl _ h'

theorem goStringLt_trichot : ∀ (a b : List w8), go.GoStringLt a b ∨ a = b ∨ go.GoStringLt b a
  | [], [] => Or.inr (Or.inl rfl)
  | [], _ :: _ => Or.inl List.Lex.nil
  | _ :: _, [] => Or.inr (Or.inr List.Lex.nil)
  | x :: xs, y :: ys => by
    rcases Int.lt_trichotomy (uint.Z x) (uint.Z y) with h | h | h
    · exact Or.inl (List.Lex.rel h)
    · have hxy : x = y := by
        have := congrArg Int.toNat h
        apply BitVec.eq_of_toNat_eq; simpa [uint.Z] using this
      subst hxy
      rcases goStringLt_trichot xs ys with h' | h' | h'
      · exact Or.inl (List.Lex.cons h')
      · exact Or.inr (Or.inl (by rw [h']))
      · exact Or.inr (Or.inr (List.Lex.cons h'))
    · exact Or.inr (Or.inr (List.Lex.rel h))

end order

section sorted
variable [ext : FfiSyntax]

theorem wKey_get (ws : List WEntry) (i : Nat) (h : i < ws.length) : wKey ws i = ws[i].key := by
  unfold wKey; rw [List.getElem?_eq_getElem h]; rfl

theorem wsSorted_iff (ws : List WEntry) :
    wsSorted ws ↔ ws.Pairwise (fun a b => go.GoStringLt a.key b.key) := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij
    have := h i j hij hj
    rwa [wKey_get ws i hi, wKey_get ws j hj] at this
  · intro h i j hij hj
    rw [wKey_get ws i (by omega), wKey_get ws j hj]
    exact h i j (by omega) hj hij

theorem wsSorted_eraseIdx (ws : List WEntry) (i : Nat) (h : wsSorted ws) :
    wsSorted (ws.eraseIdx i) := by
  rw [wsSorted_iff] at h ⊢
  exact h.sublist (List.eraseIdx_sublist ws i)

/-- Putting an entry at a search index of its key keeps the entries sorted. -/
theorem wsSorted_putList (ws : List WEntry) (i : Nat) (x : WEntry) (hs : wsSorted ws)
    (hi : i ≤ ws.length) (hlt : ∀ k < i, go.GoStringLt (wKey ws k) x.key)
    (hge : i < ws.length → ¬ go.GoStringLt (wKey ws i) x.key) :
    wsSorted (putList ws i (decide (i < ws.length ∧ wKey ws i = x.key)) x) := by
  unfold putList
  by_cases hex : i < ws.length ∧ wKey ws i = x.key
  · rw [decide_eq_true hex, if_pos rfl]
    have hk : ∀ k, wKey (ws.set i x) k = wKey ws k := by
      intro k
      unfold wKey
      rw [List.getElem?_set]
      split
      · rename_i h; subst h
        rw [if_pos hex.1]; exact hex.2.symm
      · rfl
    intro a b hab hb
    rw [hk, hk]
    exact hs a b hab (by simpa using hb)
  · rw [decide_eq_false hex]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [wsSorted_iff] at hs ⊢
    have hsplit := hs
    rw [← List.take_append_drop i ws] at hsplit
    rw [List.pairwise_append] at hsplit
    obtain ⟨h1, h2, h3⟩ := hsplit
    rw [List.pairwise_append]
    refine ⟨h1, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, h2⟩
      intro b hb
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
      rw [List.getElem_drop]
      have hil : i < ws.length := by simp at hj; omega
      have hgt : go.GoStringLt x.key (wKey ws i) := by
        rcases goStringLt_trichot (wKey ws i) x.key with h | h | h
        · exact absurd h (hge hil)
        · exact absurd ⟨hil, h⟩ hex
        · exact h
      rw [wKey_get ws i hil] at hgt
      by_cases hj0 : j = 0
      · subst hj0; simpa using hgt
      · refine goStringLt_trans hgt ?_
        have := (List.pairwise_iff_getElem.1 hs) i (i + j) hil (by simp at hj; omega) (by omega)
        exact this
    · intro a ha b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
        have hkl : k < i := by simp at hk; omega
        have hk' : k < ws.length := by simp at hk; omega
        have hax := hlt k hkl
        rw [wKey_get ws k hk'] at hax
        rw [List.getElem_take]
        exact hax
      · exact h3 a ha b hb

theorem mem_putList {α : Type} (l : List α) (i : Nat) (ex : Bool) (x w : α)
    (h : w ∈ putList l i ex x) : w = x ∨ w ∈ l := by
  unfold putList at h
  split at h
  · rcases List.mem_or_eq_of_mem_set h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rcases List.mem_append.1 h with h | h
    · exact Or.inr (List.mem_of_mem_take h)
    · rcases List.mem_cons.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_of_mem_drop h)

theorem length_putList {α : Type} (l : List α) (i : Nat) (ex : Bool) (x : α) :
    (putList l i ex x).length = if ex then l.length else l.length + 1 := by
  unfold putList
  split
  · simp
  · simp; omega

end sorted

section leaf
variable [ext : FfiSyntax]

/-- A leaf's record replaced by one with other entries: the bucket stays clean. -/
theorem bktClean_leafSet (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (l : Loc) (r r' : NRec) (hr : B.ns !! l = some r) (hleaf : r.nv.isLeaf' = true)
    (e1 : r'.nv.isLeaf' = true) (e2 : r'.nv.bucket' = r.nv.bucket') (e3 : r'.nv.spilled' = r.nv.spilled')
    (e4 : r'.nv.pgid' = r.nv.pgid') (e5 : r'.nv.parent' = r.nv.parent') (e6 : r'.nv.key' = r.nv.key')
    (e7 : r'.key = r.key) (e8 : r'.ksrc = r.ksrc) (e9 : r'.cs = r.cs)
    (hlen : r'.ins.length = r'.ws.length) (hs : wsSorted r'.ws) (hk : ∀ w ∈ r'.ws, 0 < w.key.length)
    (hlive : wsLive r'.ws) (hbv : ∀ w ∈ r'.ws, isBktFlag w.flags → bvalOK W.pages hwm w.value ∧
      (w.vs = Src.view ∨ w.vs = Src.own DFrac.discard)) :
    bktClean W hwm bl { B with ns := <[l := r']> B.ns } := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc
  have hns : ∀ y, (<[l := r']> B.ns) !! y = if y = l then some r' else B.ns !! y := by
    intro y
    by_cases h : y = l
    · subst h; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), if_neg h]
  -- a branch is not `l`
  have hbr : ∀ y ry, B.ns !! y = some ry → ry.nv.isLeaf' = false → y ≠ l := by
    intro y ry hy hl h; subst h; rw [hr] at hy; cases hy; rw [hleaf] at hl; cases hl
  have hpar : ∀ y ry, B.ns !! y = some ry → ∃ ry', (<[l := r']> B.ns) !! y = some ry' ∧
      ry'.nv.parent' = ry.nv.parent' := by
    intro y ry hy
    rw [hns]
    by_cases h : y = l
    · subst h; rw [hr] at hy; cases hy; exact ⟨r', by rw [if_pos rfl], e5⟩
    · exact ⟨ry, by rw [if_neg h]; exact hy, rfl⟩
  have hpos : ∀ x i c, pagePosAt { B with ns := <[l := r']> B.ns } x i c ↔ pagePosAt B x i c := by
    intro x i c
    unfold pagePosAt
    constructor
    · rintro ⟨ry, w, hy, hl, hw, hp, hn⟩
      rw [hns] at hy
      by_cases h : x = l
      · rw [if_pos h] at hy; cases hy; rw [e1] at hl; cases hl
      · rw [if_neg h] at hy; exact ⟨ry, w, hy, hl, hw, hp, hn⟩
    · rintro ⟨ry, w, hy, hl, hw, hp, hn⟩
      have hx := hbr x ry hy hl
      exact ⟨ry, w, by show (<[l := r']> B.ns) !! x = _; rw [hns, if_neg hx]; exact hy, hl, hw, hp, hn⟩
  refine ⟨c1, c2, ?_, c4, ?_, c6, ?_, ?_, ?_, ?_⟩
  · intro h; rw [(c3 h).1] at hr; cases hr
  · intro c l0 h
    obtain ⟨hn, r0, h0, hp⟩ := c5 c l0 h
    refine ⟨hn, ?_⟩
    show ∃ r, (<[l := r']> B.ns) !! l0 = some r ∧ _
    rw [hns]
    by_cases hl0 : l0 = l
    · subst hl0; rw [hr] at h0; cases h0; exact ⟨r', by rw [if_pos rfl], e4.trans hp⟩
    · exact ⟨r0, by rw [if_neg hl0]; exact h0, hp⟩
  · intro h0 y ry hy
    change (<[l := r']> B.ns) !! y = some ry at hy
    rw [hns] at hy
    split at hy
    · cases hy; exact e1
    · exact c7 h0 y ry hy
  · intro y ry hy
    change (<[l := r']> B.ns) !! y = some ry at hy
    rw [hns] at hy
    split at hy
    · cases hy
      rename_i hyl
      subst hyl
      obtain ⟨h1, -, -, -, -, h6, h7, h8, h9, h10, -, -, h13, h14, h15, h16⟩ := c8 y r hr
      refine ⟨by rw [e2]; exact h1, hlen, hs, hk, hlive, by rw [e3]; exact h6, by rw [e4]; exact h7,
        by rw [e4]; exact h8, by rw [e4]; exact h9, by rw [e6, e7, e8]; exact h10,
        fun _ => hbv, fun h => absurd e1 (by rw [h]; nofun), fun h => h13 (by rw [← e5]; exact h), ?_,
        by rw [e9]; exact h15, ?_⟩
      · intro hp
        rw [e5] at hp ⊢
        obtain ⟨rp, hrp, hpl, hmem, w, hw, hwp⟩ := h14 hp
        refine ⟨rp, ?_, hpl, hmem, w, hw, by rw [e4]; exact hwp⟩
        show (<[y := r']> B.ns) !! r.nv.parent' = some rp
        rw [hns, if_neg (hbr _ rp hrp hpl)]; exact hrp
      · intro c hcm
        rw [e9] at hcm
        obtain ⟨rc, hrc, hpc⟩ := h16 c hcm
        obtain ⟨rc', hrc', hpc'⟩ := hpar c rc hrc
        exact ⟨rc', hrc', hpc'.trans hpc⟩
    · rename_i hyl
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := c8 y ry hy
      refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, h13, ?_, h15, ?_⟩
      · intro hl
        obtain ⟨a, b, hkids⟩ := h12 hl
        refine ⟨a, b, fun w hw => ?_⟩
        obtain ⟨k1, k2, k3⟩ := hkids w hw
        refine ⟨k1, fun l' hl' => ?_, k3⟩
        obtain ⟨r'', hr'', hp''⟩ := k2 l' hl'
        obtain ⟨r3, hr3, hp3⟩ := hpar l' r'' hr''
        exact ⟨r3, hr3, hp3.trans hp''⟩
      · intro hp
        obtain ⟨rp, hrp, hpl, hmem, w, hw, hwp⟩ := h14 hp
        refine ⟨rp, ?_, hpl, hmem, w, hw, hwp⟩
        show (<[l := r']> B.ns) !! ry.nv.parent' = some rp
        rw [hns, if_neg (hbr _ rp hrp hpl)]; exact hrp
      · intro c hcm
        obtain ⟨rc, hrc, hpc⟩ := h16 c hcm
        obtain ⟨rc', hrc', hpc'⟩ := hpar c rc hrc
        exact ⟨rc', hrc', hpc'.trans hpc⟩
  · intro l1 i1 c1' l2 i2 c2' h1 h2 hne
    exact c9 l1 i1 c1' l2 i2 c2' ((hpos _ _ _).1 h1) ((hpos _ _ _).1 h2) hne
  · intro x i c h
    exact c10 x i c ((hpos _ _ _).1 h)

end leaf

section rootnode
variable [ext : FfiSyntax]

/-- A bucket with no root node: its root position resolves to nothing. -/
theorem resolve_root_none (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (hrn : B.bv.rootNode' = null) : resolve B B.ib.root' = none := by
  unfold resolve
  split
  · simp [hrn]
  · rw [(hc.2.2.1 hrn).2]; rfl

/-- The root's page of a bucket with no node. -/
theorem rootPage_exists (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (hrn : B.bv.rootNode' = null) : ∃ p pg, wpageAt W B B.ib.root' = some (p, pg) := by
  by_cases hr : B.ib.root' = W64 0
  · exact ⟨_, _, by unfold wpageAt; rw [if_pos hr, if_pos hr]⟩
  · obtain ⟨pg, -, hpa, -⟩ := posOK_page W hwm B B.ib.root' hr (resolve_root_none W hwm bl B hc hrn)
      (posOK_root W hwm bl B hc)
    exact ⟨_, pg, hpa⟩

/-- Materializing the root of a bucket with no node keeps it clean. -/
theorem rootStep0 (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (hrn : B.bv.rootNode' = null) (p : Loc) (pg : List w8)
    (hpa : wpageAt W B B.ib.root' = some (p, pg)) (l : Loc) (B' : BRec)
    (st st' : go_etcd_io.bbolt.TxStats)
    (hres : nodeRes B bl B.ib.root' null p pg (if B.bv.page' = null then Src.view else B.isrc)
      l B' st st') :
    bktClean W hwm bl B' ∧ bktGrows B B' := by
  obtain ⟨hns0, hnm0⟩ := hc.2.2.1 hrn
  rcases hres with ⟨hk, -, -⟩ | ⟨-, -, hl, -, s, cs', src', hs1, hs2, rfl⟩
  · rw [hnm0] at hk; cases hk
  have hgrow : bktGrows B (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') :=
    ⟨rfl, rfl, rfl, l, by simp [nodeAdded]⟩
  by_cases hr : B.ib.root' = W64 0
  · obtain ⟨hpn, hsrc, hok⟩ := hc.1 hr hrn
    have hpa' := hpa
    unfold wpageAt at hpa'; rw [if_pos hr, if_pos hr] at hpa'
    cases hpa'
    rw [if_neg hpn] at hs1 hs2
    have hsrc' : src' = Src.view ∨ src' = Src.own DFrac.discard := by
      by_cases h : B.isrc = Src.view
      · exact Or.inl (hs1 h)
      · exact Or.inr (hs2 h)
    exact ⟨bktClean_addRoot W hwm bl B hv hc hrn l hl B.ipg (fun h => absurd hr h) (fun _ => rfl)
      B.bv.page' s cs' src' hsrc', hgrow⟩
  · have hpn : B.bv.page' = null := hc.2.2.2.2.2.1 hr
    rw [if_pos hpn] at hs1
    have hsv := hs1 rfl
    subst hsv
    have hpa' := hpa
    unfold wpageAt at hpa'; rw [if_neg hr] at hpa'
    obtain ⟨pg', hpg', heq⟩ := Option.map_eq_some_iff.1 hpa'
    cases heq
    exact ⟨bktClean_addRoot W hwm bl B hv hc hrn l hl pg (fun _ => hpg') (fun h => absurd h hr)
      _ s cs' Src.view (Or.inl rfl), hgrow⟩

/-- A bucket's header changed but its root: still clean. -/
theorem bktClean_ib (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (ib' : InBucket)
    (h : ib'.root' = B.ib.root') (hc : bktClean W hwm bl B) :
    bktClean W hwm bl { B with ib := ib' } := by
  obtain ⟨r', s'⟩ := ib'
  simp only at h
  subst h
  cases B with
  | mk bv ib nm bm ns ipg isrc =>
    cases ib
    exact hc

end rootnode

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem bigSepL2_take_drop {A B : Type} (Φ : A → B → IProp GF) (l1 : List A) (l2 : List B) (i : Nat)
    (hl : l1.length = l2.length) :
    ([∗list] a;b ∈ l1;l2, Φ a b) ⊣⊢
      ([∗list] a;b ∈ l1.take i;l2.take i, Φ a b) ∗ ([∗list] a;b ∈ l1.drop i;l2.drop i, Φ a b) := by
  conv => lhs; rw [← List.take_append_drop i l1, ← List.take_append_drop i l2]
  exact BigSepL2.bigSepL2_append (Or.inl (by simp [hl]))

/-- Putting an element in both lists (`putList`), with its part. -/
theorem bigSepL2_putList {A B : Type} (Φ : A → B → IProp GF) (l1 : List A) (l2 : List B) (i : Nat)
    (ex : Bool) (x : A) (y : B) (hl : l1.length = l2.length) (hi : ex = true → i < l1.length) :
    ([∗list] a;b ∈ l1;l2, Φ a b) ∗ Φ x y ⊢ [∗list] a;b ∈ putList l1 i ex x;putList l2 i ex y, Φ a b := by
  unfold putList
  cases ex with
  | true =>
    simp only [↓reduceIte]
    have hi1 := hi rfl
    iintro ⟨H, Hx⟩
    icases BigSepL2.bigSepL2_insert_acc (Φ := fun _ a b => Φ a b)
      (List.getElem?_eq_getElem hi1) (List.getElem?_eq_getElem (hl ▸ hi1)) $$ H with ⟨-, Hback⟩
    iapply Hback $$ %x %y Hx
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨H, Hx⟩
    icases (bigSepL2_take_drop Φ l1 l2 i hl).1 $$ H with ⟨H1, H2⟩
    iapply (BigSepL2.bigSepL2_append (Φ := fun _ a b => Φ a b) (Or.inl (by simp [hl]))).2
    iframe H1
    iapply BigSepL2.bigSepL2_cons.2
    iframe

/-- Dropping element `i` of both lists. -/
theorem bigSepL2_eraseIdx {A B : Type} (Φ : A → B → IProp GF) (l1 : List A) (l2 : List B) (i : Nat)
    (hl : l1.length = l2.length) (hi : i < l1.length) :
    ([∗list] a;b ∈ l1;l2, Φ a b) ⊢ [∗list] a;b ∈ l1.eraseIdx i;l2.eraseIdx i, Φ a b := by
  rw [List.eraseIdx_eq_take_drop_succ, List.eraseIdx_eq_take_drop_succ]
  have e1 : l1 = l1.take i ++ l1[i] :: l1.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have e2 : l2 = l2.take i ++ l2[i]'(hl ▸ hi) :: l2.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons (hl ▸ hi), List.take_append_drop]
  conv => lhs; rw [e1, e2]
  iintro H
  icases (BigSepL2.bigSepL2_append (Φ := fun _ a b => Φ a b) (Or.inl (by simp [hl]))).1 $$ H
    with ⟨H1, H2⟩
  icases BigSepL2.bigSepL2_cons.1 $$ H2 with ⟨-, H2⟩
  iapply (BigSepL2.bigSepL2_append (Φ := fun _ a b => Φ a b) (Or.inl (by simp [hl]))).2
  iframe

/-- What `node.put` gives back, as the old inodes and the new one. -/
theorem inodesOwn_unput (ins : List Inode) (es : List NodeEntry) (i : Nat) (ex : Bool) (X : Inode)
    (E : NodeEntry) (hl : ins.length = es.length) :
    inodesOwn (GF := GF) (putList ins i ex X) (putList es i ex E) ∗
      (if ex then (∃ (it : Inode) (e : NodeEntry), ⌜ins[i]? = some it ∧ es[i]? = some e⌝ ∗ inodeIs it e)
       else True) ⊢ inodesOwn ins es ∗ inodeIs X E := by
  unfold putList
  cases ex with
  | true =>
    simp only [↓reduceIte]
    iintro ⟨H, ⟨%it, %e, %h12, Hie⟩⟩
    obtain ⟨h1, h2⟩ := h12
    have hi1 := (List.getElem?_eq_some_iff.1 h1).1
    have hi2 := (List.getElem?_eq_some_iff.1 h2).1
    icases inodesOwn_replace (ins.set i X) (es.set i E) i X E it e
      (List.getElem?_set_self hi1) (List.getElem?_set_self hi2) $$ [H Hie] with ⟨H, Hx⟩
    · iframe
    rw [List.set_set, List.set_set, list_set_lookup_self ins i it h1, list_set_lookup_self es i e h2]
    iframe
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨H, -⟩
    icases (inodesOwn_app _ _ _ _ (by simp [hl])).1 $$ H with ⟨H1, H2⟩
    icases (inodesOwn_cons _ _ _ _).1 $$ H2 with ⟨Hx, H2⟩
    iframe Hx
    have e : inodesOwn (GF := GF) ins es = inodesOwn (ins.take i ++ ins.drop i) (es.take i ++ es.drop i) := by
      rw [List.take_append_drop, List.take_append_drop]
    rw [e]
    iapply (inodesOwn_app _ _ _ _ (by simp [hl])).2
    iframe

/-- What `node.del` gives back (it removed inode `i`), as the old inodes. -/
theorem inodesOwn_undel (ins : List Inode) (es : List NodeEntry) (i : Nat) (it : Inode) (e : NodeEntry)
    (h1 : ins[i]? = some it) (h2 : es[i]? = some e) :
    inodesOwn (GF := GF) (ins.eraseIdx i) (es.eraseIdx i) ∗ inodeIs it e ⊢ inodesOwn ins es := by
  have hi1 := (List.getElem?_eq_some_iff.1 h1).1
  have hi2 := (List.getElem?_eq_some_iff.1 h2).1
  rw [List.eraseIdx_eq_take_drop_succ, List.eraseIdx_eq_take_drop_succ]
  iintro ⟨H, Hie⟩
  icases (inodesOwn_app _ _ _ _ (by simp; omega)).1 $$ H with ⟨H1, H2⟩
  iapply (inodesOwn_split ins es i it e h1 h2).2
  iframe

end own

end bbolt
end EtcdGrove
end Perennial
