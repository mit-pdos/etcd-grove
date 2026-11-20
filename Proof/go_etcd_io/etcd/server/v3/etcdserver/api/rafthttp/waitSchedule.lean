/-
The proof of `waitSchedule` (`pipeline.go`: `runtime.Gosched()`), over Perennial's linked proof
of `runtime.Gosched` (until 2026-11-19 a trust-boundary axiom). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.waitSchedule
public import Perennial.Spec.runtime.Gosched
import Perennial.Proof.runtime.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.waitSchedule.wp_proof : rafthttp.waitSchedule.spec (GF := GF) (hG := hG) := by
  wp_start as #Hpkg
  ihave #Hrt : isPkgInit (PROP := IProp GF) pkg_id.runtime $$ []
  · iPkgInit
  wp_apply _root_.Perennial.runtime.wp_Gosched
  · itrivial
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
