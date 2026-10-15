/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/txReadBuffer__reset.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer__reset
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txBuffer__reset

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.txReadBuffer.reset.wp_proof
    (hreset : backend.txBuffer.reset.spec (GF := GF) (hG := hG)) :
    backend.txReadBuffer.reset.spec (GF := GF) (hG := hG) := by
  intro txr R
  wp_start as Hrb
  unfold ownRB
  icases Hrb with ⟨%m, Htb, Hver, Hbks⟩
  wp_apply hreset $$ [$Htb $Hbks] as ⟨Htb, Hbks⟩
  iapply HΦ
  iexists m
  simp only [RBuf.reset]
  iframe

end proof

end EtcdGrove
end Perennial
