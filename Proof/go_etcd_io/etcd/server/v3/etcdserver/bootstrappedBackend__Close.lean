/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedBackend__Close.lean`: `(*bootstrappedBackend).Close()`, over the backend's `Close`. Lean-first (no Rocq
counterpart); stage R-D1 (2026-11-04).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedBackend__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Close

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem bootstrappedBackend.Close.wp_proof
    (hClose : backend.backend.Close.spec (GF := GF) (hG := hG)) :
    bootstrappedBackend.Close.spec (GF := GF) (hG := hG) := by
  intro s bk γ P W Pk be
  wp_start as ⟨Hs, %Hbe, #HB, #HSC, Hopen⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF)
    pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  iStructNamed Hs
  wp_auto
  rw [Hbe]
  wp_auto
  wp_apply hClose γ P W Pk be $$ [Hopen] as %err -
  · iframe Hopen; iframe #
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
