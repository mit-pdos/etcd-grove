/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/newBlockLogger.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.newBlockLogger

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

theorem newBlockLogger.wp_proof : newBlockLogger.spec (GF := GF) (hG := hG) := by
  intro iv th msg ot gr ck hmsg
  wp_start as #Hck
  iapply wp_fupd
  wp_auto
  irename «$r0» => Hl
  generalize «$r0_ptr» = r at *
  iStructNamed Hl
  iunfold clockNowOk at Hck
  wp_apply Hck as %t
  (try wp_auto)
  imod sync.init_Mutex (blockLoggerInv r) ⊤
    (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.blockLogger go!"mu" r)
    $$ [mu] [lastLogTime eventCount timeWaiting] with #Hmu
  · iexact mu
  · inext; unfold blockLoggerInv; iexists t, _, _; iframe
  ipersist interval
  ipersist threshold
  ipersist msg
  ipersist objectType
  ipersist groupResource
  ipersist «clock»
  imodintro
  iapply HΦ
  unfold blockLoggerOk
  imodintro
  iexists iv, th, msg, ot, gr, ck
  iframe #
  isplitr
  · ipureintro; exact hmsg
  iunfold clockNowOk
  iexact Hck

end proof

end k8s
end EtcdGrove
end Perennial
