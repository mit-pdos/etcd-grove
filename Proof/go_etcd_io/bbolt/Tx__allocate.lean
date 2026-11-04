/-
The proof of `Spec/go_etcd_io/bbolt/Tx__allocate.lean`: U4c's `Mmap/TxAlloc` (its `Tx.allocate.spec'`
is the shared statement since batch 29, `notes/bbolt-proof-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__allocate
public import Proof.go_etcd_io.bbolt.Mmap.TxAlloc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Tx.allocate.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hAlloc : DB.allocate.spec (GF := GF) (hG := hG))
    (hTxid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hCount : TxStats.IncPageCount.spec (GF := GF) (hG := hG))
    (hPAlloc : TxStats.IncPageAlloc.spec (GF := GF) (hG := hG)) :
    Tx.allocate.spec (GF := GF) (hG := hG) :=
  Tx.allocate.wp_proof' hLogger hAlloc hTxid hId hCount hPAlloc

end proof

end bbolt
end EtcdGrove
end Perennial
