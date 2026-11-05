/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedServer__Close.lean`: `(*bootstrappedServer).Close()`, over the record's storage's. Lean-first (no Rocq
counterpart); stage R-D1 (2026-11-04).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedServer__Close
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedStorage__Close

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

theorem bootstrappedServer.Close.wp_proof
    (hClose : bootstrappedStorage.Close.spec (GF := GF) (hG := hG)) :
    bootstrappedServer.Close.spec (GF := GF) (hG := hG) := by
  intro b bs sto bk γ P W Pk be
  wp_start as ⟨Hb, #Hsto, #Hbk, %Hbe, #HB, #HSC, Hopen⟩
  iStructNamed Hb
  wp_auto
  wp_apply hClose bs.storage' sto bk γ P W Pk be $$ [Hopen]
  · iframe Hopen; iframe #; ipureintro; exact Hbe
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
