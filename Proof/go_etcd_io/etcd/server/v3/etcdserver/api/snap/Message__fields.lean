/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Message__fields.lean`: `msgIs`'s
definition (`Proof/.../snap/Defs.lean`; until 2026-11-19 an opaque predicate and this law a
trust-boundary axiom, rafthttp stage 7d, D42). What it states is now part of the axiom of
`NewMessage`, which makes `msgIs`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__fields

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode snap

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem snap.Message.fields.wp_proof : snap.Message.fields.spec (GF := GF) (hG := hG) := by
  intro m ml rc
  unfold msgIs msgRO
  iintro #⟨Hml, Htsz, Hrd, -⟩
  iframe Hml Htsz Hrd

end proof

end EtcdGrove
end Perennial
