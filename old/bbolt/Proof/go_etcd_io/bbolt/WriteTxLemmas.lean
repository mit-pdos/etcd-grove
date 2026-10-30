/-
Lemmas about the write transaction's predicate (`WriteTxPred.lean`): a node read from a page
(`pageWs`: its entries, their bytes in the view or in a persistent heap copy), and the bytes of
the view lent out and back.
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxPred
public import Proof.go_etcd_io.bbolt.WriteTxDeref
public import Proof.go_etcd_io.bbolt.internal.common.Inodes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

theorem bytesAt_bytesAt (bs : List w8) (o L off n : Nat) (h : off + n ≤ L) :
    bytesAt (bytesAt bs o L) off n = bytesAt bs (o + off) n := by
  unfold bytesAt
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega), List.drop_drop]

/-- A part of bytes of the view is bytes of the view. -/
theorem inViewLoc_sub (W : WView) (p : Loc) (bs : List w8) (off n : Nat)
    (h : inViewLoc W p bs) (hb : off + n ≤ bs.length) :
    inViewLoc W (p +ₗ (off : Int)) (bytesAt bs off n) := by
  obtain ⟨id, PG, o, hpg, hle, hbytes, rfl⟩ := h
  have hl := bytesAt_length bs off n hb
  refine ⟨id, PG, o + off, hpg, by omega, ?_, ?_⟩
  · rw [hl, ← hbytes, bytesAt_bytesAt _ _ _ _ _ hb]
  · rw [loc_add_assoc]; congr 1; omega

/-- `n` bytes at `off` inside bytes of the view, as a slice. -/
theorem inViewAt_sub (W : WView) (p : Loc) (bs : List w8) (off n : Nat)
    (h : inViewLoc W p bs) (hb : off + n ≤ bs.length) (hn : n < 2 ^ 32) :
    inViewAt W (slice.mk (p +ₗ (off : Int)) (W64 (n : Int)) (W64 (n : Int))) (bytesAt bs off n) := by
  have hl := bytesAt_length bs off n hb
  refine ⟨inViewLoc_sub W p bs off n h hb, by omega, ?_, ?_⟩ <;> simp only [hl]

/-- The bytes of a page, in the view. -/
theorem inViewLoc_page (W : WView) (id : Nat) (pg : List w8) (h : W.pages !! id = some pg) :
    inViewLoc W (W.data +ₗ ((id * W.ps : Nat) : Int)) pg := by
  refine ⟨id, pg, 0, h, by omega, ?_, by simp⟩
  unfold bytesAt; simp

/-- The bytes a page's element reads are inside the page (it is readable). -/
theorem inode_key_bound (pg : List w8) (hr : pageReadable pg) (i : Nat) (hi : i < pageCount pg) :
    (pageFlags pg = leafPageFlag →
      elemOff i + leafPos pg i + leafKsize pg i + leafVsize pg i ≤ pg.length) ∧
    (pageFlags pg ≠ leafPageFlag → elemOff i + branchPos pg i + branchKsize pg i ≤ pg.length) := by
  obtain ⟨_, hl, hb⟩ := hr
  refine ⟨fun h => ((hl h).1.2.2.1 i hi).1, fun h => ((hb h).2 i hi).1⟩

/-- The inode `i` of a page of the view is its entry. -/
theorem inodeOf_inView (W : WView) (p : Loc) (pg : List w8) (h : inViewLoc W p pg)
    (hr : pageReadable pg) (i : Nat) (hi : i < pageCount pg) :
    (inodeOf p pg i).flags' = (pageW pg Src.view i).flags ∧
    (inodeOf p pg i).pgid' = (pageW pg Src.view i).pgid ∧
    inViewAt W (inodeOf p pg i).key' (pageW pg Src.view i).key ∧
    (pageFlags pg = leafPageFlag → inViewAt W (inodeOf p pg i).value' (pageW pg Src.view i).value) := by
  have hb := inode_key_bound pg hr i hi
  unfold inodeOf pageW
  by_cases hf : pageFlags pg = leafPageFlag
  · simp only [hf, ↓reduceIte]
    have h1 := hb.1 hf
    refine ⟨trivial, trivial, ?_, fun _ => ?_⟩
    · exact inViewAt_sub W p pg _ _ h (by omega) (leAt_lt _ _ 4)
    · exact inViewAt_sub W p pg _ _ h (by omega) (leAt_lt _ _ 4)
  · simp only [hf, ↓reduceIte]
    have h1 := hb.2 hf
    refine ⟨trivial, trivial, ?_, fun h' => h'.elim⟩
    exact inViewAt_sub W p pg _ _ h (by omega) (leAt_lt _ _ 4)

theorem wKey_pageWs (pg : List w8) (src : Src) (h : 0 < pageCount pg) :
    wKey (pageWs pg src) 0 = (pageW pg src 0).key := by
  unfold wKey pageWs
  rw [List.getElem?_map, List.getElem?_range h]
  rfl

theorem pageW_key (pg : List w8) (s1 s2 : Src) (i : Nat) :
    (pageW pg s1 i).key = (pageW pg s2 i).key := by
  unfold pageW; split <;> rfl

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The inodes of a page of the view are its entries (pure facts only). -/
theorem pageWs_view (W : WView) (p : Loc) (pg : List w8) (h : inViewLoc W p pg)
    (hr : pageReadable pg) :
    ⊢ ([∗list] it;w ∈ inodesOf p pg;pageWs pg Src.view, wOwn (GF := GF) W it w) := by
  unfold inodesOf pageWs
  iapply (BigSepL2.bigSepL2_map (inodeOf p pg) (pageW pg Src.view)).2
  iapply BigSepL2.bigSepL2_intro
  isplit
  · ipureintro; rfl
  imodintro
  iintro %k %x1 %x2 %h1 %h2
  rw [h1] at h2
  cases h2
  have hk := (List.mem_range.1 (List.mem_of_getElem? h1))
  obtain ⟨Hf, Hp, Hk, Hv⟩ := inodeOf_inView W p pg h hr x1 hk
  unfold wOwn
  isplitr
  · ipureintro; exact ⟨Hf, Hp⟩
  by_cases hf : pageFlags pg = leafPageFlag
  · have Hv' := Hv hf
    simp only [pageW, hf, ↓reduceIte] at Hk Hv' ⊢
    unfold srcOwn
    isplitr
    · ipureintro; exact Hk
    · ipureintro; exact Hv'
  · simp only [pageW, hf, ↓reduceIte] at Hk ⊢
    unfold srcOwn
    isplitr
    · ipureintro; exact Hk
    · have : (inodeOf p pg x1).value' = slice.nil := by simp [inodeOf, hf]
      rw [this]
      iapply ownSlice_nil

/-- The inodes of a page in persistent heap bytes are its entries, their bytes persistent. -/
theorem pageWs_disc (W : WView) (p : Loc) (pg : List w8) (hr : pageReadable pg)
    (hc : p.locCar ≠ 0) :
    bytesPointsto (GF := GF) p DFrac.discard pg ⊢
      ([∗list] it;w ∈ inodesOf p pg;pageWs pg (Src.own DFrac.discard), wOwn (GF := GF) W it w) := by
  haveI := (bytesPointsto_dfractional (GF := GF) p pg).dfractional_persistent
  iintro #H
  unfold inodesOf pageWs
  iapply (BigSepL2.bigSepL2_map (inodeOf p pg) (pageW pg (Src.own DFrac.discard))).2
  iapply BigSepL2.bigSepL2_intro
  isplit
  · ipureintro; rfl
  imodintro
  iintro %k %x1 %x2 %h1 %h2
  rw [h1] at h2
  cases h2
  have hk := (List.mem_range.1 (List.mem_of_getElem? h1))
  have hb := inode_key_bound pg hr x1 hk
  unfold wOwn
  by_cases hf : pageFlags pg = leafPageFlag
  · have h1' := hb.1 hf
    simp only [pageW, inodeOf, hf, ↓reduceIte]
    unfold srcOwn
    isplitr
    · ipureintro; simp
    isplitr
    · icases bytes_slice_acc (hG := hG) p DFrac.discard pg (elemOff x1 + leafPos pg x1)
        (leafKsize pg x1) (by omega) (leAt_lt _ _ 4) hc $$ H with ⟨Hk, -⟩
      unfold sliceAt leafKey
      iexact Hk
    · icases bytes_slice_acc (hG := hG) p DFrac.discard pg
        (elemOff x1 + leafPos pg x1 + leafKsize pg x1)
        (leafVsize pg x1) (by omega) (leAt_lt _ _ 4) hc $$ H with ⟨Hk, -⟩
      unfold sliceAt leafValue
      iexact Hk
  · have h1' := hb.2 hf
    simp only [pageW, inodeOf, hf, ↓reduceIte]
    unfold srcOwn
    isplitr
    · ipureintro; simp
    isplitr
    · icases bytes_slice_acc (hG := hG) p DFrac.discard pg (elemOff x1 + branchPos pg x1)
        (branchKsize pg x1) (by omega) (leAt_lt _ _ 4) hc $$ H with ⟨Hk, -⟩
      unfold sliceAt branchKey
      iexact Hk
    · iapply ownSlice_nil

/-- Bytes of the view, out of the view (and back). -/
theorem viewLoc_acc_q (W : WView) (q : Qp) (p : Loc) (bs : List w8) (h : inViewLoc W p bs) :
    pagesView (GF := GF) W.data W.ps q W.pages ⊢ bytesPointsto p (DFrac.own q) bs ∗
      (bytesPointsto p (DFrac.own q) bs -∗ pagesView W.data W.ps q W.pages) := by
  obtain ⟨id, PG, o, hpg, hle, hbytes, rfl⟩ := h
  unfold pagesView
  iintro H
  icases (BigSepM.bigSepM_lookup_acc (M := GMap Nat)
    (Φ := fun id pg => bytesPointsto (GF := GF) (W.data +ₗ ((id * W.ps : Nat) : Int)) (DFrac.own q) pg)
    (show Std.get? W.pages id = some PG from hpg)).1 $$ H with ⟨Hp, Hback⟩
  icases (bytesPointsto_around (W.data +ₗ ((id * W.ps : Nat) : Int)) (DFrac.own q) PG o
    bs.length hle).1 $$ Hp with ⟨Ha, Hm, Hb⟩
  have Hl : W.data +ₗ ((id * W.ps : Nat) : Int) +ₗ (o : Int) =
      W.data +ₗ ((id * W.ps + o : Nat) : Int) := by rw [loc_add_assoc]; congr 1
  rw [hbytes, Hl]
  iframe Hm
  iintro Hm
  iapply Hback
  iapply (bytesPointsto_around (W.data +ₗ ((id * W.ps : Nat) : Int)) (DFrac.own q) PG o
    bs.length hle).2
  rw [hbytes, Hl]
  iframe

/-- Two whole points-to of a pointer cell exclude each other. -/
theorem loc_ptsto_excl (l a b : Loc) : (l ↦ a : IProp GF) ∗ l ↦ b ⊢ False := by
  rw [typedPointsto_unseal_eq, typedPointsto_unseal_eq]
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  rw [typedPointstoDef_heap, typedPointstoDef_heap]
  icombine H1 H2 gives %H
  exfalso
  have Hv := H.1
  revert Hv
  simp [CMRA.op, DFrac.op, CMRA.Valid, DFrac.valid]
  grind

/-- Two whole points-to of a node exclude each other (a new node is not one of the bucket's). -/
theorem node_ptsto_excl (l : Loc) (a b : node) : (l ↦ a : IProp GF) ∗ l ↦ b ⊢ False := by
  rw [typedPointsto_unseal_eq, typedPointsto_unseal_eq]
  simp only [TypedPointsto.typedPointstoDef]
  iintro ⟨⟨⟨H1, -⟩, -⟩, ⟨⟨H2, -⟩, -⟩⟩
  iapply loc_ptsto_excl
  iframe

/-- A location whose node is held is not one of the nodes `ns`. -/
theorem ns_fresh (W : WView) (ns : GMap Loc NRec) (l : Loc) (v : node) :
    ⊢ ([∗map] l ↦ r ∈ ns, nodeOwn (GF := GF) W l r) -∗ l ↦ v -∗
      ([∗map] l ↦ r ∈ ns, nodeOwn (GF := GF) W l r) ∗ l ↦ v ∗ ⌜ns !! l = none⌝ := by
  iintro Hns Hl
  cases hl : ns !! l with
  | none => iframe; ipureintro; rfl
  | some r =>
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc)
      (Φ := fun l r => nodeOwn (GF := GF) W l r) (show Std.get? ns l = some r from hl)).1 $$ Hns
      with ⟨Hr, -⟩
    unfold nodeOwn
    icases Hr with ⟨Hr, -⟩
    iexfalso
    iapply node_ptsto_excl
    iframe

theorem pageOwn_congr_wand (W : WView) (B1 B2 : BRec) (h1 : B1.bv.page' = B2.bv.page')
    (h2 : B1.isrc = B2.isrc) (h3 : B1.ipg = B2.ipg) :
    pageOwn (GF := GF) W B2 ⊢ pageOwn W B1 := by
  unfold pageOwn; rw [h1, h2, h3]

theorem pageOwn_congr (W : WView) (B1 B2 : BRec) (h1 : B1.bv.page' = B2.bv.page')
    (h2 : B1.isrc = B2.isrc) (h3 : B1.ipg = B2.ipg) :
    pageOwn (GF := GF) W B1 = pageOwn W B2 := by
  unfold pageOwn; rw [h1, h2, h3]

/-- The flags and child of inode `i` are its entry's. -/
theorem wOwn_at (W : WView) (ins : List Inode) (ws : List WEntry) (i : Nat) (it : Inode)
    (w : WEntry) (h1 : ins[i]? = some it) (h2 : ws[i]? = some w) :
    ([∗list] it;w ∈ ins;ws, wOwn (GF := GF) W it w) ⊢
      ⌜it.flags' = w.flags ∧ it.pgid' = w.pgid⌝ ∗ [∗list] it;w ∈ ins;ws, wOwn (GF := GF) W it w := by
  iintro H
  icases BigSepL2.bigSepL2_lookup_acc (Φ := fun _ it w => wOwn (GF := GF) W it w) h1 h2 $$ H
    with ⟨Hi, Hback⟩
  unfold wOwn
  icases Hi with ⟨%Hp, Hk, Hv⟩
  isplitr
  · ipureintro; exact Hp
  iapply Hback
  iframe
  ipureintro; exact Hp

/-- The flags of entry `i` of a node's inodes are its record's. -/
theorem wOwn_flags_at (W : WView) (ins : List Inode) (ws : List WEntry) (i : Nat) :
    ([∗list] it;w ∈ ins;ws, wOwn (GF := GF) W it w) ⊢
      ⌜∀ it w, ins[i]? = some it → ws[i]? = some w → it.flags' = w.flags⌝ ∗
      [∗list] it;w ∈ ins;ws, wOwn (GF := GF) W it w := by
  cases h1 : ins[i]? with
  | none =>
    iintro H; iframe; ipureintro; intro it w h; cases h
  | some it =>
    cases h2 : ws[i]? with
    | none => iintro H; iframe; ipureintro; intro it w _ h; cases h
    | some w =>
      iintro H
      icases wOwn_at W ins ws i it w h1 h2 $$ H with ⟨%Hp, H⟩
      iframe
      ipureintro; intro it' w' e1 e2; cases e1; cases e2; exact Hp.1

/-- A node of a bucket, out of it (and back, possibly changed). -/
theorem bktOwn_node_acc (W : WView) (bl : Loc) (B : BRec) (nl : Loc) (r : NRec)
    (h : B.ns !! nl = some r) :
    bktOwn (GF := GF) W bl B ⊢ nodeOwn W nl r ∗
      (∀ r', nodeOwn W nl r' -∗ bktOwn W bl { B with ns := <[nl := r']> B.ns }) := by
  unfold bktOwn
  iintro ⟨Hbv, Hib, Hnm, Hbm, Hpg, Hns⟩
  icases (BigSepM.bigSepM_insert_acc (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
    (show Std.get? B.ns nl = some r from h)) $$ Hns with ⟨Hr, Hback⟩
  iframe Hr
  iintro %r' Hr'
  ihave Hns := Hback $$ %r' Hr'
  iframe
  iapply (pageOwn_congr_wand W { B with ns := <[nl := r']> B.ns } B rfl rfl rfl)
  iexact Hpg

theorem bktOwn_insert_same (W : WView) (bl : Loc) (B : BRec) (nl : Loc) (r : NRec)
    (h : B.ns !! nl = some r) :
    bktOwn (GF := GF) W bl { B with ns := <[nl := r]> B.ns } = bktOwn W bl B := by
  rw [GMap.insert_id _ _ _ h]

theorem viewLoc_acc (W : WView) (p : Loc) (bs : List w8) (h : inViewLoc W p bs) :
    pagesView (GF := GF) W.data W.ps W.q W.pages ⊢ bytesPointsto p (DFrac.own W.q) bs ∗
      (bytesPointsto p (DFrac.own W.q) bs -∗ pagesView W.data W.ps W.q W.pages) :=
  viewLoc_acc_q W W.q p bs h

theorem pv_split (data : Loc) (ps : Nat) (pages : GMap Nat (List w8)) (a b : Qp) :
    pagesView (GF := GF) data ps (a + b) pages ⊣⊢
      pagesView data ps a pages ∗ pagesView data ps b pages := by
  unfold pagesView
  rw [← BigSepM.bigSepM_sep_eq]
  exact ⟨BigSepM.bigSepM_mono_of_forall
      ((bytesPointsto_dfractional (GF := GF) _ _).dfractional (DFrac.own a) (DFrac.own b)).1,
    BigSepM.bigSepM_mono_of_forall
      ((bytesPointsto_dfractional (GF := GF) _ _).dfractional (DFrac.own a) (DFrac.own b)).2⟩

theorem pv_half (data : Loc) (ps : Nat) (pages : GMap Nat (List w8)) (q : Qp) :
    pagesView (GF := GF) data ps q pages ⊣⊢
      pagesView data ps q.half pages ∗ pagesView data ps q.half pages := by
  have := pv_split (GF := GF) data ps pages q.half q.half
  rw [Qp.half_add_half] at this
  exact this

theorem inViewAt_slice (W : WView) (s : GoSlice) (bs : List w8) (h : inViewAt W s bs) :
    s = sliceAt s.ptr 0 bs.length := by
  obtain ⟨-, -, h1, h2⟩ := h
  cases s; simp only at h1 h2; subst h1; subst h2; simp [sliceAt]

/-- A slice's bytes, lent out of its source (the view, at a fraction of it), and back. -/
theorem srcBorrow (W : WView) (hc : W.data.locCar ≠ 0) (q : Qp) (s : GoSlice) (src : Src)
    (bs : List w8) (hns : src ≠ Src.stale) :
    pagesView (GF := GF) W.data W.ps q W.pages ∗ srcOwn W s src bs ⊢ ∃ dq,
      ⌜∀ d, src = Src.own d → dq = d⌝ ∗ s ↦*{dq} bs ∗
      (s ↦*{dq} bs -∗ pagesView W.data W.ps q W.pages ∗ srcOwn W s src bs) := by
  iintro ⟨Hpv, Hs⟩
  cases src with
  | stale => exact absurd rfl hns
  | own d =>
    unfold srcOwn
    iexists d
    isplitr
    · ipureintro; intro d' h; cases h; rfl
    iframe Hs
    iintro Hs
    iframe
  | view =>
    unfold srcOwn
    icases Hs with %Hin
    have Hs := inViewAt_slice W s bs Hin
    obtain ⟨Hloc, Hn, -, -⟩ := Hin
    obtain ⟨id, PG, o, -, -, -, Hp⟩ := id Hloc
    have Hpc : s.ptr.locCar ≠ 0 := by rw [Hp]; simpa [Loc.add] using hc
    icases viewLoc_acc_q (GF := GF) W q s.ptr bs Hloc $$ Hpv with ⟨Hb, Hback⟩
    icases bytes_slice_acc (hG := hG) s.ptr (DFrac.own q) bs 0 bs.length (by omega) Hn Hpc $$ Hb
      with ⟨Hsl, Hsback⟩
    have Hba : bytesAt bs 0 bs.length = bs := by simp [bytesAt]
    rw [Hba, ← Hs]
    iexists DFrac.own q
    isplitr
    · ipureintro; intro d h; cases h
    iframe Hsl
    iintro Hsl
    ihave Hb := Hsback $$ Hsl
    ihave Hpv := Hback $$ Hb
    iframe
    ipureintro; exact ⟨Hloc, Hn, by rw [Hs]; rfl, by rw [Hs]; rfl⟩

/-- A node's inodes as `inodesOwn` (what the node specs take), their view bytes lent out of the
view (at fractions of `q`), and back. -/
theorem nodeBorrow (W : WView) (hc : W.data.locCar ≠ 0) :
    ∀ (ws : List WEntry) (ins : List Inode) (q : Qp), wsLive ws →
    pagesView (GF := GF) W.data W.ps q W.pages ∗ ([∗list] it;w ∈ ins;ws, wOwn W it w) ⊢
      ∃ es, ⌜wMatch ws es⌝ ∗ inodesOwn ins es ∗
        (inodesOwn ins es -∗ pagesView W.data W.ps q W.pages ∗
          [∗list] it;w ∈ ins;ws, wOwn W it w) := by
  intro ws
  induction ws with
  | nil =>
    intro ins q _
    iintro ⟨Hpv, Hl⟩
    ihave %Hlen := BigSepL2.bigSepL2_length $$ Hl
    have : ins = [] := List.eq_nil_of_length_eq_zero (by simpa using Hlen)
    subst this
    iexists []
    isplitr
    · ipureintro; exact List.Forall₂.nil
    isplitl []
    · iapply inodesOwn_nil
    iintro -
    iframe
  | cons w ws ih =>
    intro ins q Hlive
    iintro ⟨Hpv, Hl⟩
    icases BigSepL2.bigSepL2_cons_inv_right.1 $$ Hl with ⟨%it, %ins', %Heq, Hw, Hl⟩
    subst Heq
    icases (pv_half W.data W.ps W.pages q).1 $$ Hpv with ⟨Hpv1, Hpv2⟩
    icases (pv_half W.data W.ps W.pages q.half).1 $$ Hpv1 with ⟨Hpk, Hpv1⟩
    have Hl1 : wsLive ws := fun x hx => Hlive x (List.mem_cons_of_mem _ hx)
    have Hw0 := Hlive w (List.mem_cons_self)
    icases ih ins' q.half Hl1 $$ [Hpv2 Hl] with ⟨%es, %Hm, Hes, Hback⟩
    · iframe
    unfold wOwn
    icases Hw with ⟨%Hfp, Hk, Hv⟩
    icases srcBorrow W hc q.half.half it.key' w.ks w.key Hw0.1 $$ [Hpk Hk] with ⟨%dk, %Hdk, Hk, Hkb⟩
    · iframe
    icases srcBorrow W hc q.half.half it.value' w.vs w.value Hw0.2 $$ [Hpv1 Hv] with ⟨%dv, %Hdv, Hv, Hvb⟩
    · iframe
    iexists (⟨w.flags, w.pgid, w.key, w.value, dk, dv⟩ :: es)
    isplitr
    · ipureintro
      exact List.Forall₂.cons ⟨rfl, rfl, rfl, rfl, Hdk, Hdv⟩ Hm
    isplitl [Hk Hv Hes]
    · iapply (inodesOwn_cons _ _ _ _).2
      iframe
      unfold inodeIs
      iframe
      ipureintro; exact Hfp
    iintro Hall
    icases (inodesOwn_cons _ _ _ _).1 $$ Hall with ⟨Hi, Hes⟩
    unfold inodeIs
    icases Hi with ⟨-, Hk, Hv⟩
    ihave Hk := Hkb $$ Hk
    ihave Hv := Hvb $$ Hv
    ihave Hr := Hback $$ Hes
    icases Hk with ⟨Hpk, Hk⟩
    icases Hv with ⟨Hpv1, Hv⟩
    icases Hr with ⟨Hpv2, Hl⟩
    isplitl [Hpk Hpv1 Hpv2]
    · iapply (pv_half W.data W.ps W.pages q).2
      iframe Hpv2
      iapply (pv_half W.data W.ps W.pages q.half).2
      iframe
    iapply BigSepL2.bigSepL2_cons.2
    iframe
    ipureintro; exact Hfp

/-- Two nodes of a bucket, out of it (and back unchanged). -/
theorem bktOwn_node2_acc (W : WView) (bl : Loc) (B : BRec) (l1 l2 : Loc) (r1 r2 : NRec)
    (h1 : B.ns !! l1 = some r1) (h2 : B.ns !! l2 = some r2) (hne : l1 ≠ l2) :
    bktOwn (GF := GF) W bl B ⊢ nodeOwn W l1 r1 ∗ nodeOwn W l2 r2 ∗
      (nodeOwn W l1 r1 -∗ nodeOwn W l2 r2 -∗ bktOwn W bl B) := by
  unfold bktOwn
  iintro ⟨Hbv, Hib, Hnm, Hbm, Hpg, Hns⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
    (show Std.get? B.ns l1 = some r1 from h1)).1 $$ Hns with ⟨Hr1, Hns⟩
  have h2' : Std.get? (Std.delete B.ns l1) l2 = some r2 := by
    show (GMap.delete l1 B.ns) !! l2 = some r2
    rw [GMap.lookup_delete_ne _ hne]; exact h2
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
    h2').1 $$ Hns with ⟨Hr2, Hns⟩
  iframe Hr1 Hr2
  iintro Hr1 Hr2
  iframe
  iapply (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
    (show Std.get? B.ns l1 = some r1 from h1)).2
  iframe
  iapply (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r) h2').2
  iframe

/-- A node's key (nil, or bytes from its source), lent out, and back. -/
theorem keyBorrow (W : WView) (hc : W.data.locCar ≠ 0) (q : Qp) (k : GoSlice) (src : Src)
    (bs : List w8) (hns : src ≠ Src.stale) :
    pagesView (GF := GF) W.data W.ps q W.pages ∗
      (if k = slice.nil then iprop(True) else srcOwn W k src bs) ⊢ ∃ dk ck,
      ⌜k ≠ slice.nil → ck = bs⌝ ∗ k ↦*{dk} ck ∗
      (k ↦*{dk} ck -∗ pagesView W.data W.ps q W.pages ∗
        (if k = slice.nil then iprop(True) else srcOwn W k src bs)) := by
  iintro ⟨Hpv, Hk⟩
  by_cases h : k = slice.nil
  · subst h
    iexists DFrac.own 1, []
    isplitr
    · ipureintro; intro h; exact absurd rfl h
    isplitl []
    · iapply ownSlice_nil
    iintro -
    iframe
  · rw [if_neg h]
    icases srcBorrow W hc q k src bs hns $$ [Hpv Hk] with ⟨%dk, -, Hk, Hback⟩
    · iframe
    iexists dk, bs
    isplitr
    · ipureintro; intro _; rfl
    iframe Hk
    iintro Hk
    ihave Hb := Hback $$ Hk
    iexact Hb

theorem bigSepM_gsingleton {K V : Type} [DecidableEq K] (Φ : K → V → IProp GF) (i : K) (x : V) :
    ([∗map] k ↦ v ∈ ({[i := x]} : GMap K V), Φ k v) ⊣⊢ Φ i x :=
  BigSepM.bigSepM_singleton (M := GMap K)

theorem srcOwn_other (W W' : WView) (s : GoSlice) (src : Src) (bs : List w8)
    (h : src ≠ Src.view) : srcOwn (GF := GF) W s src bs = srcOwn W' s src bs := by
  cases src with
  | view => exact absurd rfl h
  | own d => rfl
  | stale => rfl

theorem pageOwn_other (W W' : WView) (B : BRec) (h : B.isrc ≠ Src.view) :
    pageOwn (GF := GF) W B = pageOwn W' B := by
  unfold pageOwn
  cases hs : B.isrc with
  | view => exact absurd hs h
  | own d => rfl
  | stale => rfl

theorem nodeOwn_other (W W' : WView) (l : Loc) (r : NRec)
    (h : (∀ w ∈ r.ws, w.ks ≠ Src.view ∧ w.vs ≠ Src.view) ∧ r.ksrc ≠ Src.view) :
    nodeOwn (GF := GF) W l r ⊢ nodeOwn W' l r := by
  unfold nodeOwn
  iintro ⟨Hn, Hins, Hcap, Hents, Hch, Hchcap, Hkey⟩
  iframe Hn Hins Hcap Hch Hchcap
  isplitl [Hents]
  · iapply (BigSepL2.bigSepL2_mono (Φ := fun _ it w => wOwn (GF := GF) W it w)
      (Ψ := fun _ it w => wOwn (GF := GF) W' it w) ?_) $$ Hents
    intro k it w _ hw
    have hw' := h.1 w (List.mem_of_getElem? hw)
    unfold wOwn
    rw [srcOwn_other W W' _ _ _ hw'.1, srcOwn_other W W' _ _ _ hw'.2]
  · rw [srcOwn_other W W' _ _ _ h.2]
    iexact Hkey

/-- Once no byte is the view's, the transaction's resources stand over any other view. -/
theorem ownWriteTxG_reattach (W W' : WView) (txl : Loc) (T : WTx) (h : noView T) :
    ownWriteTxG (GF := GF) W txl T ⊢ ownWriteTxG W' txl T := by
  unfold ownWriteTxG
  iintro ⟨Ht, Hm, Hpm, Hbufs, Hbs⟩
  iframe Ht Hm Hpm Hbufs
  iapply (BigSepM.bigSepM_mono (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
    (Ψ := fun bl B => bktOwn (GF := GF) W' bl B) ?_) $$ Hbs
  intro bl B hB
  obtain ⟨hi, hn⟩ := h bl B hB
  unfold bktOwn
  iintro ⟨Hbv, Hib, Hnm, Hbm, Hpg, Hns⟩
  iframe Hbv Hib Hnm Hbm
  rw [pageOwn_other W W' B hi]
  iframe Hpg
  iapply (BigSepM.bigSepM_mono (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
    (Ψ := fun l r => nodeOwn (GF := GF) W' l r) ?_) $$ Hns
  intro l r hr
  exact nodeOwn_other W W' l r (hn l r hr)

/-- The transaction's meta copy, out of its resources (and back, changed). -/
theorem ownWriteTxG_meta_acc (W : WView) (txl : Loc) (T : WTx) :
    ownWriteTxG (GF := GF) W txl T ⊢ structFieldRef Tx go!"meta" txl ↦ T.t.meta' ∗ T.t.meta' ↦ T.mv ∗
      (∀ mv', structFieldRef Tx go!"meta" txl ↦ T.t.meta' ∗ T.t.meta' ↦ mv' -∗
        ownWriteTxG W txl { T with mv := mv' }) := by
  unfold ownWriteTxG TxW_rest_root
  iintro ⟨⟨Hw, Hm, Hdb, Hmeta, Hpages, Hst, Hch, Hwf, %Hn⟩, Hmv, Hpm, Hbufs, Hbs⟩
  iframe Hmeta Hmv
  iintro %mv' ⟨Hmeta, Hmv⟩
  iframe
  ipureintro; exact Hn

end own

end bbolt
end EtcdGrove
end Perennial
