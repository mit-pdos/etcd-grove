/-
`waitSchedule` (`pipeline.go`: `runtime.Gosched()`), verified: translated with its body
(`Code/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp.toml`), over Perennial's `runtime.Gosched`.
Until 2026-11-18 a trust-boundary axiom. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.waitSchedule
public import Perennial.Proof.runtime.Link

@[expose] public section

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
  wp_start
  wp_apply runtime.wp_Gosched
  · itrivial
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
