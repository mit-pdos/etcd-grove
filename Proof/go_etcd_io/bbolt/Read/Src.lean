/-
The read path's (U6, `notes/bbolt-proof-plan.md`) sources of the slices a reader returns: a
sub-range of a reader bucket's page is, as a byte slice, bytes of the view or persistent heap
bytes (`srcOwn` at a source other than `stale`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.RCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section facts
theorem bytesAt_bytesAt (pg : List w8) (o L off n : Nat) (h : off + n ≤ L) :
    bytesAt (bytesAt pg o L) off n = bytesAt pg (o + off) n := by
  unfold bytesAt
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]

theorem bytesAt_drop' (pg : List w8) : bytesAt pg 0 pg.length = pg := by
  unfold bytesAt; simp

theorem bytesAt_length (pg : List w8) (off n : Nat) (h : off + n ≤ pg.length) :
    (bytesAt pg off n).length = n := by
  unfold bytesAt; simp; omega

variable [GooseExts]

/-- A sub-range of bytes of the view is bytes of the view. -/
theorem inViewLoc_sub (v : View) (p : Loc) (bs : List w8) (h : inViewLoc v p bs) (off n : Nat)
    (hn : off + n ≤ bs.length) :
    inViewLoc v (p +ₗ ((off : Nat) : Int)) (bytesAt bs off n) := by
  obtain ⟨id, pg, o, hpg, hle, hbs, rfl⟩ := h
  have hl := bytesAt_length bs off n hn
  refine ⟨id, pg, o + off, hpg, by rw [hl]; omega, ?_, ?_⟩
  · rw [hl, ← hbs, bytesAt_bytesAt pg o bs.length off n hn]
  · rw [loc_add_assoc]; exact congrArg (fun z => v.base +ₗ z) (by omega)

/-- A sub-range of a page of the view is bytes of the view. -/
theorem inViewLoc_page (v : View) (id : Nat) (pg : List w8) (h : v.pages !! id = some pg)
    (off n : Nat) (hn : off + n ≤ pg.length) :
    inViewLoc v (pageLoc v id +ₗ ((off : Nat) : Int)) (bytesAt pg off n) := by
  have hl := bytesAt_length pg off n hn
  refine ⟨id, pg, off, h, by rw [hl]; omega, by rw [hl], ?_⟩
  unfold pageLoc; rw [loc_add_assoc]; exact congrArg (fun z => v.base +ₗ z) (by omega)

end facts

section src
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

instance srcOwn_persistent_r (v : View) (s : GoSlice) (src : Src) (bs : List w8) :
    Persistent (srcOwn (GF := GF) v s src bs) := by
  cases src <;> unfold srcOwn <;> infer_instance

/-- **A sub-range of a reader bucket's page, as a byte slice, has a source** (the view's bytes,
or persistent heap bytes of a cloned inline page). -/
theorem rd_src (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (b : Loc) (dqb : DFrac) (bv : List w8) (ibp pp : Loc) (pid : Nat) (l : Loc) (pg : List w8)
    (h : rPageAt v bv pp pid = some (l, pg)) (hne : pg ≠ []) (off n : Nat)
    (hn : off + n ≤ pg.length) (hn32 : n < 2 ^ 32) :
    rdTxK (GF := GF) K tx src q T v ∗ rBktP v tx b dqb bv ibp pp ⊢
      (rdTxK K tx src q T v ∗ rBktP v tx b dqb bv ibp pp) ∗
      ∃ s : Src, ⌜s ≠ Src.stale⌝ ∗
        srcOwn v (slice.mk (l +ₗ ((off : Nat) : Int)) (W64 (n : Int)) (W64 (n : Int))) s
          (bytesAt pg off n) := by
  have hl := bytesAt_length pg off n hn
  iintro H
  icases rd_page_bounds K tx src q T v b dqb bv ibp pp pid l pg h hne $$ H with ⟨H, %Hbd⟩
  unfold rPageAt at h
  by_cases hi : inBucketRoot bv = 0
  · rw [if_pos hi] at h
    by_cases h0 : pid = 0
    · rw [if_pos h0] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      unfold rBktP
      rw [if_pos hi]
      icases H with ⟨Hk, H1, H2, H3, H4, H5, H6, H7, %Hpp, Hlo⟩
      unfold locOwn
      icases Hlo with (%Hv | #Hb)
      · isplitl
        · iframe; isplitr
          · ipureintro; exact Hpp
          ileft; ipureintro; exact Hv
        iexists Src.view
        isplitr
        · ipureintro; intro e; cases e
        unfold srcOwn
        ipureintro
        exact ⟨inViewLoc_sub v pp _ Hv off n hn, by rw [hl]; exact hn32, by rw [hl], by rw [hl]⟩
      · isplitl
        · iframe; isplitr
          · ipureintro; exact Hpp
          iright; iexact Hb
        iexists (Src.own DFrac.discard)
        isplitr
        · ipureintro; intro e; cases e
        unfold srcOwn
        icases Read.bytesPointsto_sub_acc pp DFrac.discard (inlinePage bv) (bytesAt (inlinePage bv) off n)
          off (by rw [hl]; exact hn) (by rw [hl]) $$ Hb with ⟨Hs, -⟩
        have Ho := Read.bytesPointsto_ownSlice (GF := GF) (pp +ₗ ((off : Nat) : Int)) DFrac.discard
          (bytesAt (inlinePage bv) off n) (by simp [Loc.add]; omega) (by rw [hl]; omega)
        rw [hl] at Ho
        iapply Ho.1
        iexact Hs
    · rw [if_neg h0] at h; cases h
  · rw [if_neg hi] at h
    obtain ⟨pg', hpg, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    iframe H
    iexists Src.view
    isplitr
    · ipureintro; intro e; cases e
    unfold srcOwn
    ipureintro
    exact ⟨inViewLoc_page v pid pg' hpg off n hn, by rw [hl]; exact hn32, by rw [hl], by rw [hl]⟩

/-- **The reader's view's cells**, out of `rdTxK` and back. -/
theorem rdTxK_cells_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ qc, viewCells qc v ∗
      (viewCells qc v -∗ rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hmeta, Hroot, Hfill, Hpages, Hch, Hwf, Hdb, Hmv, Hcells, Hmap, #Hvo, %Hf⟩, Hpool⟩
  iexists _
  iframe Hcells
  iintro Hcells
  iexists r, c, mv, k
  iframe; iframe #
  isplitr
  · ipureintro; exact Hc
  ipureintro; exact Hf

/-- The reader's view's base is a mapped address. -/
theorem rdTxK_base_pos (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ ⌜0 < v.base.addr⌝ := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hmeta, Hroot, Hfill, Hpages, Hch, Hwf, Hdb, Hmv, Hcells,
      ⟨%l, Hg, Hmf, %Hl⟩, #Hvo, %Hf⟩, Hpool⟩
  iapply mapFields_base_nonnull
  iexact Hmf

omit hos [GooseSemantics] go_gctx sem package_sem in
/-- The view's cells split by fraction. -/
theorem viewCells_split_r (q1 q2 : Qp) (v : View) :
    viewCells (GF := GF) (q1 + q2) v ⊣⊢ viewCells q1 v ∗ viewCells q2 v := by
  unfold viewCells
  rw [← BigSepM.bigSepM_sep_eq]
  constructor
  · apply BigSepM.bigSepM_mono_of_forall
    intro k x
    exact ((bytesPointsto_dfractional (GF := GF) _ x).dfractional (DFrac.own q1) (DFrac.own q2)).1
  · apply BigSepM.bigSepM_mono_of_forall
    intro k x
    exact ((bytesPointsto_dfractional (GF := GF) _ x).dfractional (DFrac.own q1) (DFrac.own q2)).2

/-- **A live slice's bytes, read** (persistent bytes, or bytes of the view through its cells),
and back. -/
theorem viewCells_src_acc (qc : Qp) (v : View) (hb : 0 < v.base.addr) (s : GoSlice) (sr : Src)
    (bs : List w8) (hs : sr ≠ Src.stale) :
    srcOwn (GF := GF) v s sr bs ∗ viewCells qc v ⊢ ∃ dq : DFrac, s ↦*{dq} bs ∗
      (s ↦*{dq} bs -∗ viewCells qc v) := by
  cases sr with
  | stale => exact absurd rfl hs
  | own d =>
    unfold srcOwn
    iintro ⟨#Hs, Hv⟩
    iexists DFrac.discard
    iframe Hs
    iintro _
    iexact Hv
  | view =>
    unfold srcOwn
    iintro ⟨%Hin, Hv⟩
    obtain ⟨hl, hlen, hsl, hsc⟩ := Hin
    have hpos : 0 < s.ptr.addr := by
      obtain ⟨id, pg, off, -, -, -, hp⟩ := hl
      rw [hp]; simp [Loc.add]; omega
    have hs' : s = slice.mk s.ptr (W64 (bs.length : Int)) (W64 (bs.length : Int)) := by
      cases s; simp only at hsl hsc ⊢; rw [hsl, hsc]
    have Ho := Read.bytesPointsto_ownSlice (GF := GF) s.ptr (DFrac.own 1) bs hpos (by omega)
    icases viewCells_loc_acc qc v s.ptr bs hl $$ Hv with ⟨%dq, Hb, Hback⟩
    have Ho := Read.bytesPointsto_ownSlice (GF := GF) s.ptr dq bs hpos (by omega)
    rw [← hs'] at Ho
    iexists dq
    icases Ho.1 $$ Hb with Hb
    iframe Hb
    iintro Hb
    iapply Hback
    iapply Ho.2
    iexact Hb

/-- **Two live slices' bytes, read together** out of `rdTxK`, and back. -/
theorem rdTxK_src2_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (s1 s2 : GoSlice) (r1 r2 : Src) (b1 b2 : List w8) (h1 : r1 ≠ Src.stale)
    (h2 : r2 ≠ Src.stale) :
    rdTxK (GF := GF) K tx src q T v ∗ srcOwn v s1 r1 b1 ∗ srcOwn v s2 r2 b2 ⊢
      ∃ d1 d2 : DFrac, s1 ↦*{d1} b1 ∗ s2 ↦*{d2} b2 ∗
        (s1 ↦*{d1} b1 -∗ s2 ↦*{d2} b2 -∗ rdTxK K tx src q T v) := by
  iintro ⟨Hk, #H1, #H2⟩
  ihave %Hb := rdTxK_base_pos K tx src q T v $$ Hk
  icases rdTxK_cells_acc K tx src q T v $$ Hk with ⟨%qc, Hc, Hk⟩
  rw [← Qp.half_add_half qc]
  icases (viewCells_split_r qc.half qc.half v).1 $$ Hc with ⟨Hc1, Hc2⟩
  icases viewCells_src_acc qc.half v Hb s1 r1 b1 h1 $$ [Hc1] with ⟨%d1, Hs1, Hb1⟩
  · iframe; iframe #
  icases viewCells_src_acc qc.half v Hb s2 r2 b2 h2 $$ [Hc2] with ⟨%d2, Hs2, Hb2⟩
  · iframe; iframe #
  iexists d1, d2
  iframe Hs1 Hs2
  iintro Hs1 Hs2
  ihave Hc1 := Hb1 $$ Hs1
  ihave Hc2 := Hb2 $$ Hs2
  iapply Hk
  iapply (viewCells_split_r qc.half qc.half v).2
  iframe

/-- Where a key a reader searches for is: caller-owned bytes, or bytes of the view. -/
inductive KeyR where
  | heap (dk : DFrac)
  | view

/-- The key `key` holding `kb` from `kr`. -/
def keyR (v : View) (key : GoSlice) (kr : KeyR) (kb : List w8) : IProp GF :=
  match kr with
  | .heap dk => iprop(key ↦*{dk} kb)
  | .view => iprop(⌜inViewAt v key kb⌝)

/-- A live slice is a key. -/
theorem srcOwn_keyR (v : View) (s : GoSlice) (sr : Src) (bs : List w8) (hs : sr ≠ Src.stale) :
    srcOwn (GF := GF) v s sr bs ⊢ ∃ kr, keyR v s kr bs := by
  cases sr with
  | stale => exact absurd rfl hs
  | own d => unfold srcOwn; iintro H; iexists (KeyR.heap DFrac.discard); unfold keyR; iexact H
  | view => unfold srcOwn; iintro %H; iexists KeyR.view; unfold keyR; ipureintro; exact H

/-- **A reader bucket's page and a key, read together**, and back. -/
theorem rd_page_key_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (b : Loc) (dqb : DFrac) (bv : List w8) (ibp pp : Loc) (pid : Nat) (l : Loc) (pg : List w8)
    (h : rPageAt v bv pp pid = some (l, pg)) (key : GoSlice) (kr : KeyR) (kb : List w8) :
    rdTxK (GF := GF) K tx src q T v ∗ rBktP v tx b dqb bv ibp pp ∗ keyR v key kr kb ⊢
      ∃ dq dk, bytesPointsto l dq pg ∗ key ↦*{dk} kb ∗
        (bytesPointsto l dq pg -∗ key ↦*{dk} kb -∗
          rdTxK K tx src q T v ∗ rBktP v tx b dqb bv ibp pp ∗ keyR v key kr kb) := by
  cases kr with
  | heap dk =>
    unfold keyR
    iintro ⟨Hk, Hb0, Hkey⟩
    icases rd_page_acc K tx src q T v b dqb bv ibp pp pid l pg h $$ [Hk Hb0] with ⟨%dq, Hp, Hb⟩
    · iframe
    iexists dq, dk
    iframe Hp Hkey
    iintro Hp Hkey
    ihave H := Hb $$ Hp
    icases H with ⟨H1, H2⟩
    iframe
  | view =>
    unfold keyR
    iintro ⟨Hk, Hb, %Hin⟩
    ihave %Hbase := rdTxK_base_pos K tx src q T v $$ Hk
    have Hko : srcOwn (GF := GF) v key Src.view kb ⊣⊢ iprop(⌜inViewAt v key kb⌝) := by
      unfold srcOwn; exact .rfl
    -- the page's bytes from the first half of the cells (or persistent bytes), the key's from
    -- the second
    have hpage : rPageAt v bv pp pid = some (l, pg) → (∃ id, v.pages !! id = some pg ∧
        l = pageLoc v id) ∨ (inBucketRoot bv = 0 ∧ pid = 0 ∧ l = pp ∧ pg = inlinePage bv) := by
      intro h
      unfold rPageAt at h
      by_cases hi : inBucketRoot bv = 0
      · rw [if_pos hi] at h
        by_cases h0 : pid = 0
        · rw [if_pos h0] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact Or.inr ⟨hi, h0, h.1.symm, h.2.symm⟩
        · rw [if_neg h0] at h; cases h
      · rw [if_neg hi] at h
        obtain ⟨pg', hpg, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        exact Or.inl ⟨pid, by rw [hpg, he.2], he.1.symm⟩
    -- bytes of the page as a view location, or persistent
    have Hpl : rdTxK (GF := GF) K tx src q T v ∗ rBktP v tx b dqb bv ibp pp ⊢
        (rdTxK K tx src q T v ∗ rBktP v tx b dqb bv ibp pp) ∗
        (⌜inViewLoc v l pg⌝ ∨ bytesPointsto l DFrac.discard pg) := by
      rcases hpage h with ⟨id, hpg, rfl⟩ | ⟨hi, -, rfl, rfl⟩
      · iintro H
        iframe H
        ileft; ipureintro
        have := inViewLoc_page v id pg hpg 0 pg.length (by omega)
        rw [bytesAt_drop' pg] at this
        simpa using this
      · unfold rBktP
        rw [if_pos hi]
        iintro ⟨Hk, H1, H2, H3, H4, H5, H6, H7, %Hpp, Hlo⟩
        unfold locOwn
        icases Hlo with (%Hv | #Hb)
        · iframe; isplitr
          · isplitr
            · ipureintro; exact Hpp
            ileft; ipureintro; exact Hv
          ileft; ipureintro; exact Hv
        · iframe; isplitr
          · isplitr
            · ipureintro; exact Hpp
            iright; iexact Hb
          iright; iexact Hb
    icases Hpl $$ [Hk Hb] with ⟨⟨Hk, Hb⟩, Hpg⟩
    · iframe
    icases rdTxK_cells_acc K tx src q T v $$ Hk with ⟨%qc, Hc, Hkb⟩
    rw [← Qp.half_add_half qc]
    icases (viewCells_split_r qc.half qc.half v).1 $$ Hc with ⟨Hc1, Hc2⟩
    icases viewCells_src_acc qc.half v Hbase key Src.view kb (by intro e; cases e) $$ [Hc2]
      with ⟨%dk, Hkey, Hkeyb⟩
    · iframe; unfold srcOwn; ipureintro; exact Hin
    icases Hpg with (%Hv | #Hp)
    · icases viewCells_loc_acc qc.half v l pg Hv $$ Hc1 with ⟨%dq, Hp, Hpb⟩
      iexists dq, dk
      iframe Hp Hkey
      iintro Hp Hkey
      ihave Hc1 := Hpb $$ Hp
      ihave Hc2 := Hkeyb $$ Hkey
      iframe Hb
      isplitl [Hkb Hc1 Hc2]
      · iapply Hkb
        iapply (viewCells_split_r qc.half qc.half v).2
        iframe
      ipureintro; exact Hin
    · iexists DFrac.discard, dk
      iframe Hp Hkey
      iintro - Hkey
      ihave Hc2 := Hkeyb $$ Hkey
      iframe Hb
      isplitl [Hkb Hc1 Hc2]
      · iapply Hkb
        iapply (viewCells_split_r qc.half qc.half v).2
        iframe
      ipureintro; exact Hin

/-- **Bytes of a reader bucket's page as a byte slice and a key, read together**, and back. -/
theorem rd_slice_key_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (b : Loc) (dqb : DFrac) (bv : List w8) (ibp pp : Loc) (pid : Nat) (l : Loc) (pg : List w8)
    (h : rPageAt v bv pp pid = some (l, pg)) (off n : Nat) (hn : off + n ≤ pg.length)
    (hn63 : n < 2 ^ 63) (hn0 : 0 < n) (key : GoSlice) (kr : KeyR) (kb : List w8) :
    rdTxK (GF := GF) K tx src q T v ∗ rBktP v tx b dqb bv ibp pp ∗ keyR v key kr kb ⊢ ∃ dq dk,
      slice.mk (l +ₗ ((off : Nat) : Int)) (W64 (n : Int)) (W64 (n : Int)) ↦*{dq} bytesAt pg off n ∗
      key ↦*{dk} kb ∗
      (slice.mk (l +ₗ ((off : Nat) : Int)) (W64 (n : Int)) (W64 (n : Int)) ↦*{dq} bytesAt pg off n -∗
        key ↦*{dk} kb -∗ rdTxK K tx src q T v ∗ rBktP v tx b dqb bv ibp pp ∗ keyR v key kr kb) := by
  have hlen : (bytesAt pg off n).length = n := by unfold bytesAt; simp; omega
  iintro H
  icases rd_page_key_acc K tx src q T v b dqb bv ibp pp pid l pg h key kr kb $$ H
    with ⟨%dq, %dk, Hb, Hkey, Hback⟩
  icases Read.bytesPointsto_bounds l dq pg (by intro e; simp [e] at hn; omega) $$ Hb
    with ⟨Hb, %Hbd⟩
  icases Read.bytesPointsto_sub_acc l dq pg (bytesAt pg off n) off (by rw [hlen]; omega)
    (by rw [hlen]) $$ Hb with ⟨Hs, Hsb⟩
  have Ho := Read.bytesPointsto_ownSlice (GF := GF) (l +ₗ ((off : Nat) : Int)) dq
    (bytesAt pg off n) (by simp [Loc.add]; omega) (by rw [hlen]; exact hn63)
  rw [hlen] at Ho
  icases Ho.1 $$ Hs with Hs
  iexists dq, dk
  iframe Hs Hkey
  iintro Hs Hkey
  icases Ho.2 $$ Hs with Hs
  iapply Hback $$ [Hsb Hs] Hkey
  iapply Hsb
  iexact Hs

end src

end bbolt
end EtcdGrove
end Perennial
