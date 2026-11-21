/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__monitorCompactHash.lean`: `s.monitorCompactHash()` (`server.go`) with the check off: `s.FeatureEnabled(CompactHashCheck)` (stepped into: `s.Cfg.ServerFeatureGate.Enabled(f)`, which the gate answers `false`) and it returns at once. Until
prove-etcdserver (2026-11-20) a names-only trust-boundary axiom.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__monitorCompactHash

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

theorem EtcdServer.monitorCompactHash.wp_proof :
    EtcdServer.monitorCompactHash.spec (GF := GF) (hG := hG) := by
  intro s fg
  wp_start as ⟨#Hfg, #Hoff⟩
  wp_auto
  -- `s.FeatureEnabled(f)`, stepped into (its spec asks for the whole gate's contract)
  wp_method_call
  wp_call
  wp_auto
  iunfold featureIs at Hoff
  icases Hoff with ⟨%fi, %Hfi, #HEn⟩
  subst Hfi
  wp_auto
  wp_apply HEn
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
