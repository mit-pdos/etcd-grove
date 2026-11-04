/-
U7c's (`notes/bbolt-proof-plan.md`) heap accessors for `Cursor.node` (and `Bucket.node`): a live
node's struct out of `wtxW` and back, its entries' count below `2^63`, and the header of the page
at a position of a live bucket (`wpageAt`: a view page, or the inline page, from the view's cells
or from the bucket's persistent page bytes).
-/
module

public import Proof.go_etcd_io.bbolt.Write.CurNode
public import Proof.go_etcd_io.bbolt.Read.Bytes
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A node's struct out of `wtxW`**, and back unchanged. -/
theorem wtxW_node_ptr_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc)
    (B : BRec) (n : Loc) (rn : NRec) (hb : X.t.bs !! bl = some B) (hn : B.ns !! n = some rn) :
    wtxW (GF := GF) K tx r m X ⊢ n ↦ rn.nv ∗ (n ↦ rn.nv -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  ihave %Ho := wtxHeap_objs_node tx (DFrac.own 1) X bl B n rn hb hn $$ Hh
  icases wtxHeap_node_ptr_acc tx (DFrac.own 1) X bl n rn Ho $$ Hh with ⟨Hn, Hback⟩
  iframe Hn
  iintro Hn
  ihave Hh := Hback $$ Hn
  iframe; iframe #; ipureintro; exact Hr

/-- **A live node's entries are fewer than `2^63`** (its `inodes` slice's length). -/
theorem wtxW_node_len (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc)
    (B : BRec) (n : Loc) (rn : NRec) (hb : X.t.bs !! bl = some B) (hn : B.ns !! n = some rn)
    (hl : n ∈ X.live) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m X ∗ ⌜rn.ws.length < 2 ^ 63⌝ := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  icases wtxHeap_live_node_acc tx (DFrac.own 1) X bl B n rn hb hn hl $$ Hh with ⟨Ho, Hback⟩
  unfold objOwn
  icases Ho with ⟨Hn, Hs, Hcap, Hws, Hch, Hchcap, Hkey⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hwl := BigSepL2.bigSepL2_length $$ Hws
  ihave Hh := Hback $$ [Hn Hs Hcap Hws Hch Hchcap Hkey]
  · simp only [objOwn]; iframe
  isplitl
  · iframe; iframe #; ipureintro; exact Hr
  ipureintro
  rw [← Hwl, Hsl.1]
  have := Hsl.2
  word

/-- An inline page's bytes, read from the bucket's `pageOwn`, at some fraction, and back. -/
theorem pageOwn_acc (v : View) (B : BRec) (hsrc : B.pst = PageSt.view ∨ ∃ dq, B.isrc = Src.own dq)
    (hp : B.bv.page' ≠ null) :
    viewCells (GF := GF) wq v ∗ pageOwn v B ⊢ ∃ dq : DFrac, bytesPointsto B.bv.page' dq B.ipg ∗
      (bytesPointsto B.bv.page' dq B.ipg -∗ viewCells wq v ∗ pageOwn v B) := by
  iintro ⟨Hc, Hp⟩
  by_cases hv : B.pst = PageSt.view
  · unfold pageOwn
    rw [hv]
    simp only
    icases Hp with %Hin
    icases viewCells_loc_acc wq v B.bv.page' B.ipg Hin $$ Hc with ⟨%dq, Hb, Hback⟩
    iexists dq
    iframe Hb
    iintro Hb
    ihave Hc := Hback $$ Hb
    iframe
    ipureintro; exact Hin
  · obtain ⟨dq0, hdq⟩ := hsrc.resolve_left hv
    have e : pageOwn (GF := GF) v B = bytesPointsto B.bv.page' DFrac.discard B.ipg := by
      unfold pageOwn; cases h : B.pst <;> simp_all
    rw [e]
    icases Hp with #Hp
    iexists DFrac.discard
    iframe Hp
    iintro -
    iframe

variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The header of the page at a position of a live bucket** (`wpageAt`; for an inline bucket,
its page field's bytes as its status says), at some fraction, and back. -/
theorem wtxW_hdr_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (pid : w64) (pa : Loc) (pg : List w8) (hb : X.t.bs !! bl = some B) (hl : bl ∈ X.liveB)
    (hw : wpageAt X.v B pid = some (pa, pg))
    (hsrc : B.ib.root' = W64 0 → B.pst = PageSt.view ∨ ∃ dq, B.isrc = Src.own dq)
    (hpa : 0 < pa.addr) (h16 : 16 ≤ pg.length) :
    wtxW (GF := GF) K tx r m X ⊢ ∃ dq, pa ↦{dq} pageHdr pg ∗
      (pa ↦{dq} pageHdr pg -∗ wtxW K tx r m X) := by
  -- the page's bytes, out of the view's cells or the bucket's page
  suffices H : wtxW (GF := GF) K tx r m X ⊢ ∃ dq, bytesPointsto pa dq pg ∗
      (bytesPointsto pa dq pg -∗ wtxW K tx r m X) by
    iintro Hw
    icases H $$ Hw with ⟨%dq, Hb, Hback⟩
    icases bytesPointsto_view_read (V := Page) pa dq pg 0 pa (by simp) (by omega) hpa $$ Hb
      with ⟨Hh, Hhb⟩
    iexists dq
    rw [show pageHdr pg = (decode (List.take 16 (List.drop 0 pg)) : Page) from rfl]
    iframe Hh
    iintro Hh
    iapply Hback
    iapply Hhb
    iexact Hh
  by_cases hin : B.ib.root' = W64 0
  · unfold wpageAt at hw
    rw [if_pos hin] at hw
    split at hw
    · simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hp : B.bv.page' ≠ null := by
        intro e; rw [e] at hpa; simp [null] at hpa
      unfold wtxW wtxCore
      iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
      have Ho := bobjs_bkt X.t bl B hb
      icases wtxHeap_bkt_obj_acc tx (DFrac.own 1) X bl B Ho $$ Hh with ⟨Ho, Hback⟩
      rw [show decide (bl ∈ X.liveB) = true from decide_eq_true hl]
      unfold objOwn
      icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, Hpo⟩
      simp only [↓reduceIte]
      icases pageOwn_acc X.v B (hsrc hin) hp $$ [Hcells Hpo] with ⟨%dq, Hb, Hpb⟩
      · iframe
      iexists dq
      iframe Hb
      iintro Hb
      icases Hpb $$ Hb with ⟨Hcells, Hpo⟩
      ihave Hh := Hback $$ [H1 H2 H3 H4 H5 H6 H7 H8 H9 Hpo]
      · iframe
      iframe; iframe #; ipureintro; exact Hr
    · cases hw
  · unfold wpageAt at hw
    rw [if_neg hin] at hw
    obtain ⟨pg0, hpg, e⟩ := Option.map_eq_some_iff.1 hw
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    unfold wtxW
    iintro ⟨Hcore, Hcells, Hmap⟩
    icases viewCells_page_acc wq X.v pid.toNat pg0 hpg $$ Hcells with ⟨Hb, Hback⟩
    iexists DFrac.own wq
    unfold pageLoc
    iframe Hb
    iintro Hb
    ihave Hcells := Hback $$ Hb
    iframe

end heap

end Write

end bbolt
end EtcdGrove
end Perennial
