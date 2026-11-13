/-
A reader's meta copy and its high-water mark (batch 42 of `notes/bbolt-proof-plan.md`, for U10e's
`freepages` checks): `rtxFrac`'s pure facts bound every view page's extent by the meta's `pgid`
(established at `Txn/RdInit.rdTxK_intro` from `treeOK` and `isMeta`); `rdTxK_meta_pgid_acc` reads
`tx.meta` and the meta with that bound, and gives the reader back.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rd
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit package_sem in
/-- **A reader's meta copy, with its txid and its high-water mark bounding the view's pages**, and
back. -/
theorem rdTxK_meta_pgid_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ (m : Loc) (mv : Meta),
      tx.[Tx, go!"meta"] ↦{DFrac.own q} m ∗ m ↦{DFrac.own q} mv ∗
      ⌜mv.txid'.toNat = v.txid ∧
        ∀ id pg, v.pages !! id = some pg → id + (1 + pageOverflow pg) ≤ mv.pgid'.toNat⌝ ∗
      (tx.[Tx, go!"meta"] ↦{DFrac.own q} m -∗ m ↦{DFrac.own q} mv -∗ rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpkg, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hmg, Hrest⟩, Hpool⟩
  icases Hrest with ⟨Hme, Hrb, Hfp, Hpg, Hch, Hwf, Hdb, Hrest⟩
  icases Hrest with ⟨Hmv, Hvc, Hmap, Hvo, %Hf⟩
  iexists t.meta', mv
  iframe Hme Hmv
  isplitr
  · ipureintro; exact ⟨Hf.2.2.1, Hf.2.2.2.2.2.2.2⟩
  iintro Hme Hmv
  iexists r, c, mv, k
  isplitr
  · ipureintro; exact Hc
  iframe Hreg Hpkg Hcore Hv Hex Hpool
  iexists t
  iframe
  ipureintro; exact Hf

end rd

end bbolt
end EtcdGrove
end Perennial
