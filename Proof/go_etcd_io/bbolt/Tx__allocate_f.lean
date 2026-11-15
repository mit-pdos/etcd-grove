/-
The proof of `Spec/go_etcd_io/bbolt/Tx__allocate_f.lean`: U4c's `Mmap/TxAlloc` (batch 44.1,
`notes/bbolt-proof-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__allocate_f
public import Proof.go_etcd_io.bbolt.Mmap.TxAlloc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Tx.allocate_f.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hAlloc : DB.allocate.spec (GF := GF) (hG := hG))
    (hTxid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hCount : TxStats.IncPageCount.spec (GF := GF) (hG := hG))
    (hPAlloc : TxStats.IncPageAlloc.spec (GF := GF) (hG := hG)) :
    Tx.allocate_f.spec (GF := GF) (hG := hG) :=
  Tx.allocate_f.wp_proof' hLogger hAlloc hTxid hId hCount hPAlloc

end proof

end bbolt
end EtcdGrove
end Perennial
