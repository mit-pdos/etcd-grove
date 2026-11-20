/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Message__CloseNotify.lean`, over
`snap/message.go`'s translation (with its body since 2026-11-19; until then a trust-boundary axiom,
D22 S-h). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__CloseNotify

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode snap

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

theorem snap.Message.CloseNotify.wp_proof : snap.Message.CloseNotify.spec (GF := GF) (hG := hG) := by
  intro m c
  wp_start as #Hc
  unfold msgCloseC msgCloseRO
  icases Hc with #Hc
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
