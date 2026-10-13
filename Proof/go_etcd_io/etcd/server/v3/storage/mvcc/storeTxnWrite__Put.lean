/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Put
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__put

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.storeTxnWrite.Put.wp_proof (hput : mvcc.storeTxnWrite.put.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnWrite.Put.spec (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend key value k v leaseID
  wp_start as ⟨Htw, #Hkey, #Hval, Hlease, %Hb⟩
  (try wp_auto)
  wp_apply (hput tw s γ ilog pend key value k v leaseID) $$ [$Htw $Hkey $Hval $Hlease] as Htw
  · ipureintro; exact Hb
  (try wp_auto)
  iunfold mvcc.storeTxnWriteIs at Htw
  iNamed Htw
  (try wp_auto)
  have hrev : (W64 ((ilog.length : Int) - 1) : w64) + W64 1 = W64 (ilog.length : Int) := by
    rw [← mvcc.W64_add_one]; simp
  rw [hrev]
  iapply HΦ
  iunfold mvcc.storeTxnWriteIs
  iexists trace, ti, bt, Locked, chs, ps, ntok
  simp only [named]
  iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hcres
  iframe #
  ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn⟩

end proof

end EtcdGrove
end Perennial
