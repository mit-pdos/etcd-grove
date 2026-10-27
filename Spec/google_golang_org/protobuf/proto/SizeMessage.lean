/-
`proto.Size` of a raft v3.7 `*pb.Message`: the trust boundary (D21 M2, 2026-10-19, the user's D21h
(A)). `EtcdServer.Process` sizes a received `MsgApp` for the server's stats
(`s.stats.RecvAppendReq(..., proto.Size(m))`, `server.go:717-719`). Lean-first; stated over the
raftpb ownership predicates of `Proof/go_etcd_io/raft/v3/InvPb.lean`, as `SizeEntry.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `proto.Size(m)` of a `*pb.Message` holding `ms` (at any fractions, with or without its entries'
capacity) returns some `int` at least `0`, the message back.

Against protobuf-go v1.36.11 (`proto/size.go`, `internal/impl/encode.go:118-129`): `Size` is the
length of the wire encoding, a non-negative `int`; it reads the message (its entries, snapshot,
context and responses) and stores the size cache atomically: a write to the hidden fields only,
which the hidden-field invariant (`pbMsg`, inside `msgPtsC`) owns. -/
abbrev proto.SizeMessage.spec : Prop :=
  ∀ (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ msgPtsC l dq dqe cap ms }}
    (App (Val (@! google_golang_org.protobuf.proto.Size)) (Val #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #l)))
  {{ (n : w64), RET #n; msgPtsC l dq dqe cap ms ∗ ⌜0 ≤ sint.Z n⌝ }}

end spec

end EtcdGrove
end Perennial
