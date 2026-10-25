/-
The trust boundary: net/http's errors are not rafthttp's `errMemberRemoved` (rafthttp stage 7d,
2026-10-24, the user's choice; `netErrNotRemoved_spec`, `Snapshot.lean`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Snapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (see `netErrNotRemoved_spec`): `errors.Is` of an error net/http made
against rafthttp's `errMemberRemoved` is `false`. The snapshot sender's `send` asks it of every
error its `post` returns; the server's error channel receives none (its predicate is `False`: a
static cluster's member is never removed). -/
axiom rafthttp.netErrNotRemoved_ok : netErrNotRemoved_spec (GF := GF)

end proof

end EtcdGrove
end Perennial
