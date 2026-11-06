/-
The reader's read path context (U6, `notes/bbolt-proof-plan.md`): a reader bucket with its
header and inline page locations exposed (`rBktP`, of which `rBkt` is the existential), the page a
bucket position names (`rPageAt`), and the bytes of such a page read out of the reader's
resources (`rd_page_acc`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.Base
public import Proof.go_etcd_io.bbolt.Read.Bytes
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rctx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem rBkt_eq (v : View) (tx b : Loc) (dq : DFrac) (bv : List w8) :
    rBkt (GF := GF) v tx b dq bv = iprop(∃ ibp pp, rBktP v tx b dq bv ibp pp) := rfl

/-- **A page of the reader's view, read** out of `rdTxK`, and back. -/
theorem rdTxK_page_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (id : Nat) (pg : List w8) (h : v.pages !! id = some pg) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ dq, bytesPointsto (pageLoc v id) dq pg ∗
      (bytesPointsto (pageLoc v id) dq pg -∗ rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hmeta, Hroot, Hfill, Hpages, Hch, Hwf, Hdb, Hmv, Hcells, Hmap, #Hvo, %Hf⟩, Hpool⟩
  icases viewCells_page_acc _ v id pg h $$ Hcells with ⟨Hpg, Hcells⟩
  iexists _
  iframe Hpg
  iintro Hpg
  iexists r, c, mv, k
  iframe; iframe #
  isplitr
  · ipureintro; exact Hc
  isplitl [Hcells Hpg]
  · iapply Hcells; iexact Hpg
  ipureintro; exact Hf

/-- **Bytes of the reader's view at a location, read** out of `rdTxK`, and back. -/
theorem rdTxK_loc_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (l : Loc) (bs : List w8) (h : inViewLoc v l bs) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ dq, bytesPointsto l dq bs ∗
      (bytesPointsto l dq bs -∗ rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hmeta, Hroot, Hfill, Hpages, Hch, Hwf, Hdb, Hmv, Hcells, Hmap, #Hvo, %Hf⟩, Hpool⟩
  icases viewCells_loc_acc _ v l bs h $$ Hcells with ⟨%dq, Hpg, Hcells⟩
  iexists dq
  iframe Hpg
  iintro Hpg
  iexists r, c, mv, k
  iframe; iframe #
  isplitr
  · ipureintro; exact Hc
  isplitl [Hcells Hpg]
  · iapply Hcells; iexact Hpg
  ipureintro; exact Hf

/-- **A page of a reader bucket, read** (a page of the view, or its inline page: bytes of the
view or persistent heap bytes), and back. -/
theorem rd_page_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (b : Loc) (dqb : DFrac) (bv : List w8) (ibp pp : Loc) (pid : Nat) (l : Loc) (pg : List w8)
    (h : rPageAt v bv pp pid = some (l, pg)) :
    rdTxK (GF := GF) K tx src q T v ∗ rBktP v tx b dqb bv ibp pp ⊢ ∃ dq,
      bytesPointsto l dq pg ∗
      (bytesPointsto l dq pg -∗ rdTxK K tx src q T v ∗ rBktP v tx b dqb bv ibp pp) := by
  unfold rPageAt at h
  by_cases hi : inBucketRoot bv = 0
  · rw [if_pos hi] at h
    by_cases h0 : pid = 0
    · rw [if_pos h0] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      unfold rBktP
      rw [if_pos hi]
      iintro ⟨Hk, H1, H2, H3, H4, H5, H6, H7, %Hpp, Hlo⟩
      unfold locOwn
      icases Hlo with (%Hv | #Hb)
      · icases rdTxK_loc_acc K tx src q T v pp _ Hv $$ Hk with ⟨%dq, Hb, Hk⟩
        iexists dq
        iframe Hb
        iintro Hb
        ihave Hk := Hk $$ Hb
        iframe
        isplitr
        · ipureintro; exact Hpp
        ileft; ipureintro; exact Hv
      · iexists DFrac.discard
        iframe Hb
        iintro -
        iframe
        ipureintro; exact Hpp
    · rw [if_neg h0] at h; cases h
  · rw [if_neg hi] at h
    obtain ⟨pg', hpg, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    iintro ⟨Hk, Hb⟩
    icases rdTxK_page_acc K tx src q T v pid pg' hpg $$ Hk with ⟨%dq, Hp, Hk⟩
    iexists dq
    iframe Hp
    iintro Hp
    ihave Hk := Hk $$ Hp
    iframe

variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The bounds of a reader bucket's page (non-empty), keeping the resources. -/
theorem rd_page_bounds (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (b : Loc) (dqb : DFrac) (bv : List w8) (ibp pp : Loc) (pid : Nat) (l : Loc) (pg : List w8)
    (h : rPageAt v bv pp pid = some (l, pg)) (hne : pg ≠ []) :
    rdTxK (GF := GF) K tx src q T v ∗ rBktP v tx b dqb bv ibp pp ⊢
      (rdTxK K tx src q T v ∗ rBktP v tx b dqb bv ibp pp) ∗
      ⌜0 < l.addr ∧ l.addr + pg.length ≤ maxAddr⌝ := by
  iintro H
  icases rd_page_acc K tx src q T v b dqb bv ibp pp pid l pg h $$ H with ⟨%dq, Hb, Hback⟩
  icases Read.bytesPointsto_bounds l dq pg hne $$ Hb with ⟨Hb, %Hbd⟩
  ihave H := Hback $$ Hb
  iframe
  ipureintro; exact Hbd

/-- **A reader bucket's page header, read**, and back. -/
theorem rd_hdr_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (b : Loc) (dqb : DFrac) (bv : List w8) (ibp pp : Loc) (pid : Nat) (l : Loc) (pg : List w8)
    (h : rPageAt v bv pp pid = some (l, pg)) (h16 : 16 ≤ pg.length) :
    rdTxK (GF := GF) K tx src q T v ∗ rBktP v tx b dqb bv ibp pp ⊢ ∃ dq,
      l ↦{dq} pageHdr pg ∗ (l ↦{dq} pageHdr pg -∗ rdTxK K tx src q T v ∗ rBktP v tx b dqb bv ibp pp) := by
  iintro H
  icases rd_page_acc K tx src q T v b dqb bv ibp pp pid l pg h $$ H with ⟨%dq, Hb, Hback⟩
  icases Read.bytesPointsto_bounds l dq pg (by intro e; simp [e] at h16) $$ Hb with ⟨Hb, %Hbd⟩
  icases bytesPointsto_view_read (V := Page) l dq pg 0 l (by simp) (by omega) Hbd.1 $$ Hb
    with ⟨Hh, Hhb⟩
  iexists dq
  rw [show pageHdr pg = (decode (List.take 16 (List.drop 0 pg)) : Page) from rfl]
  iframe Hh
  iintro Hh
  iapply Hback
  iapply Hhb
  iexact Hh

/-- **Element `i` of a reader bucket's page, read** (its 16 bytes as an element view), and back. -/
theorem rd_elem_acc {V : Type} [ByteEncoding V 16] [TypedPointsto (GF := GF) V]
    [BytesView (GF := GF) V] (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (b : Loc) (dqb : DFrac) (bv : List w8) (ibp pp : Loc) (pid : Nat) (l : Loc) (pg : List w8)
    (h : rPageAt v bv pp pid = some (l, pg)) (i : Nat) (hi : elemOff i + 16 ≤ pg.length) :
    rdTxK (GF := GF) K tx src q T v ∗ rBktP v tx b dqb bv ibp pp ⊢ ∃ dq,
      (l +ₗ ((elemOff i : Nat) : Int)) ↦{dq} (decode (bytesAt pg (elemOff i) 16) : V) ∗
      ((l +ₗ ((elemOff i : Nat) : Int)) ↦{dq} (decode (bytesAt pg (elemOff i) 16) : V) -∗
        rdTxK K tx src q T v ∗ rBktP v tx b dqb bv ibp pp) := by
  iintro H
  icases rd_page_acc K tx src q T v b dqb bv ibp pp pid l pg h $$ H with ⟨%dq, Hb, Hback⟩
  icases Read.bytesPointsto_bounds l dq pg (by intro e; simp [e] at hi) $$ Hb with ⟨Hb, %Hbd⟩
  icases bytesPointsto_view_read (V := V) l dq pg (elemOff i) _ rfl hi Hbd.1 $$ Hb
    with ⟨Hh, Hhb⟩
  iexists dq
  rw [show bytesAt pg (elemOff i) 16 = List.take 16 (List.drop (elemOff i) pg) from rfl]
  iframe Hh
  iintro Hh
  iapply Hback
  iapply Hhb
  iexact Hh

/-- **Bytes of a reader bucket's page as a byte slice**, and back. -/
theorem rd_slice_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (b : Loc) (dqb : DFrac) (bv : List w8) (ibp pp : Loc) (pid : Nat) (l : Loc) (pg : List w8)
    (h : rPageAt v bv pp pid = some (l, pg)) (off n : Nat) (hn : off + n ≤ pg.length)
    (hn63 : n < 2 ^ 63) (hn0 : 0 < n) :
    rdTxK (GF := GF) K tx src q T v ∗ rBktP v tx b dqb bv ibp pp ⊢ ∃ dq,
      slice.mk (l +ₗ ((off : Nat) : Int)) (W64 (n : Int)) (W64 (n : Int)) ↦*{dq} bytesAt pg off n ∗
      (slice.mk (l +ₗ ((off : Nat) : Int)) (W64 (n : Int)) (W64 (n : Int)) ↦*{dq} bytesAt pg off n -∗
        rdTxK K tx src q T v ∗ rBktP v tx b dqb bv ibp pp) := by
  have hlen : (bytesAt pg off n).length = n := by unfold bytesAt; simp; omega
  iintro H
  icases rd_page_acc K tx src q T v b dqb bv ibp pp pid l pg h $$ H with ⟨%dq, Hb, Hback⟩
  icases Read.bytesPointsto_bounds l dq pg (by intro e; simp [e] at hn; omega) $$ Hb
    with ⟨Hb, %Hbd⟩
  icases Read.bytesPointsto_sub_acc l dq pg (bytesAt pg off n) off (by rw [hlen]; omega)
    (by rw [hlen]) $$ Hb with ⟨Hs, Hsb⟩
  have Ho := Read.bytesPointsto_ownSlice (GF := GF) (l +ₗ ((off : Nat) : Int)) dq
    (bytesAt pg off n) (by simp [Loc.add]; omega) (by rw [hlen]; exact hn63)
  rw [hlen] at Ho
  icases Ho.1 $$ Hs with Hs
  iexists dq
  iframe Hs
  iintro Hs
  icases Ho.2 $$ Hs with Hs
  iapply Hback
  iapply Hsb
  iexact Hs

end rctx

end bbolt
end EtcdGrove
end Perennial
