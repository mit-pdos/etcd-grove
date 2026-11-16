/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/progressNotifyEvent.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.progressNotifyEvent
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem progressNotifyEvent.wp_proof : progressNotifyEvent.spec (GF := GF) (hG := hG) := by
  intro rev
  wp_start as -
  ihave #Pti : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_apply _root_.Perennial.time.wp_Now as %t0 -
  (try wp_auto)
  iapply HΦ
  iexists _
  iframe
  ipureintro
  exact ⟨rfl, rfl, rfl⟩

end proof

end k8s
end EtcdGrove
end Perennial
