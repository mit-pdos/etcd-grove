/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/newCorruptionChecker.lean`: `newCorruptionChecker(lg,
s, storage)` (`corrupt.go`), an allocation of `&corruptionChecker{lg, hasherAdapter{s, storage}}`.
Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16), for
`NewServer`; until prove-etcdserver (2026-11-20) a names-only trust-boundary axiom.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.newCorruptionChecker

@[expose] public section

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

theorem newCorruptionChecker.wp_proof : newCorruptionChecker.spec (GF := GF) (hG := hG) := by
  intro lg s h
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
