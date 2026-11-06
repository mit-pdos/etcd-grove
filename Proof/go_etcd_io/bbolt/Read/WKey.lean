/-
A key the writer's searches take (maintainer R's U6g item 4): `keyR` over the writer's base view
(caller-owned bytes at a fraction, or bytes of the view), given back, in place of a persistent
`srcOwn` key; its bytes read through the view's cells.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WCtx
public import Proof.go_etcd_io.bbolt.Read.Src

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wkey
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A key's bytes, read** through the view's cells (a view key) or its owner's share, and back. -/
theorem keyR_cells_acc (q : Qp) (v : View) (hb : 0 < v.base.addr) (key : GoSlice) (kr : KeyR)
    (kb : List w8) :
    keyR (GF := GF) v key kr kb ∗ viewCells q v ⊢ ∃ dk : DFrac, key ↦*{dk} kb ∗
      (key ↦*{dk} kb -∗ keyR v key kr kb ∗ viewCells q v) := by
  cases kr with
  | heap dk =>
    simp only [keyR]
    iintro ⟨Hk, Hc⟩
    iexists dk
    iframe Hk
    iintro Hk
    iframe
  | view =>
    simp only [keyR]
    iintro ⟨%Hin, Hc⟩
    icases srcOwn_acc q v key Src.view kb (by intro h; cases h) hb $$ [Hc] with ⟨%dk, Hk, Hkb⟩
    · iframe; unfold srcOwn; ipureintro; exact Hin
    iexists dk
    iframe Hk
    iintro Hk
    icases Hkb $$ Hk with ⟨-, Hc⟩
    iframe
    ipureintro; exact Hin

/-- **A page's bytes and a key's, through their sources and the view's cells**, and back
(`cells_page_key_acc` with a `keyR` key). -/
theorem cells_page_keyR_acc (q : Qp) (v : View) (hb : 0 < v.base.addr) (pa : Loc) (s : Src)
    (pg : List w8) (key : GoSlice) (kr : KeyR) (kb : List w8) :
    srcLoc (GF := GF) v pa s pg ∗ keyR v key kr kb ∗ viewCells q v ⊢ ∃ dq dk,
      bytesPointsto pa dq pg ∗ key ↦*{dk} kb ∗
      (bytesPointsto pa dq pg -∗ key ↦*{dk} kb -∗ keyR v key kr kb ∗ viewCells q v) := by
  iintro ⟨#Hs, Hk, Hc⟩
  icases (viewCells_halves q v).1 $$ Hc with ⟨Hc1, Hc2⟩
  icases Write.srcLoc_acc q.half v pa s pg $$ [Hc1] with ⟨%dq, Hp, Hpb⟩
  · iframe; iframe #
  icases keyR_cells_acc q.half v hb key kr kb $$ [Hk Hc2] with ⟨%dk, Hkey, Hkb⟩
  · iframe
  iexists dq, dk
  iframe Hp Hkey
  iintro Hp Hkey
  ihave Hc1 := Hpb $$ Hp
  icases Hkb $$ Hkey with ⟨Hk, Hc2⟩
  iframe Hk
  iapply (viewCells_halves q v).2
  iframe

/-- **A key and a live slice's bytes, read together** out of `wtxW` (the key caller-owned or the
view's), and back (`bytes.Equal(name, k)` after a writer's search). -/
theorem wtxW_keyR_src_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (key : GoSlice)
    (kr : KeyR) (kb : List w8) (s : GoSlice) (sr : Src) (bs : List w8) (hs : sr ≠ Src.stale) :
    wtxW (GF := GF) K tx r m X ∗ keyR X.v key kr kb ∗ srcOwn X.v s sr bs ⊢
      ∃ d1 d2 : DFrac, key ↦*{d1} kb ∗ s ↦*{d2} bs ∗
        (key ↦*{d1} kb -∗ s ↦*{d2} bs -∗ wtxW K tx r m X ∗ keyR X.v key kr kb) := by
  iintro ⟨Hw, Hk, #Hs⟩
  icases wtxW_cells_acc K tx r m X $$ Hw with ⟨%Hbase, Hc, Hwb⟩
  icases (viewCells_halves wq X.v).1 $$ Hc with ⟨Hc1, Hc2⟩
  icases keyR_cells_acc wq.half X.v Hbase key kr kb $$ [Hk Hc1] with ⟨%d1, H1, Hb1⟩
  · iframe
  icases viewCells_src_acc wq.half X.v Hbase s sr bs hs $$ [Hc2] with ⟨%d2, H2, Hb2⟩
  · iframe; iframe #
  iexists d1, d2
  iframe H1 H2
  iintro H1 H2
  icases Hb1 $$ H1 with ⟨Hk, Hc1⟩
  ihave Hc2 := Hb2 $$ H2
  iframe Hk
  iapply Hwb
  iapply (viewCells_halves wq X.v).2
  iframe

/-- **A key's bytes** out of `wtxW` and back. -/
theorem wtxW_keyR_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (key : GoSlice)
    (kr : KeyR) (kb : List w8) :
    wtxW (GF := GF) K tx r m X ∗ keyR X.v key kr kb ⊢
      ∃ d1 : DFrac, key ↦*{d1} kb ∗ (key ↦*{d1} kb -∗ wtxW K tx r m X ∗ keyR X.v key kr kb) := by
  iintro ⟨Hw, Hk⟩
  icases wtxW_cells_acc K tx r m X $$ Hw with ⟨%Hbase, Hc, Hwb⟩
  icases keyR_cells_acc wq X.v Hbase key kr kb $$ [Hk Hc] with ⟨%d1, H1, Hb1⟩
  · iframe
  iexists d1
  iframe H1
  iintro H1
  icases Hb1 $$ H1 with ⟨Hk, Hc⟩
  iframe Hk
  iapply Hwb; iexact Hc

-- `hdlFrags`, `hdlFrags_lookup`, `hdlFrags_insert`: moved to `Inv/Tx` (U6w; `wtxCore` holds them).

end wkey

end bbolt
end EtcdGrove
end Perennial
