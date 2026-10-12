/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__progressAll
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__progressIfSync

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

theorem mvcc.watchableStore.progressAll.wp_proof
    (hPIS : mvcc.watchableStore.progressIfSync.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.progressAll.spec (GF := GF) (hG := hG) := by
  intro s st γ m dq M
  wp_start as ⟨#Hws, Hm, #HM, HR⟩
  wp_auto
  wp_apply (hPIS s st γ m dq M _) $$ [$Hws $Hm $HM $HR] as %b ⟨Hm, HR⟩
  (try wp_auto)
  iapply HΦ
  iframe Hm HR

end proof

end EtcdGrove
end Perennial
