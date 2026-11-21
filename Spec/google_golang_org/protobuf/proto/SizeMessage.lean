/-
`proto.Size` of a raft v3.7 `*pb.Message`: the trust boundary (D21 M2, 2026-10-19, the user's D21h
(A)). `EtcdServer.Process` sizes a received `MsgApp` for the server's stats
(`s.stats.RecvAppendReq(..., proto.Size(m))`, `server.go:717-719`). Lean-first; stated over the
raftpb ownership predicates of `Proof/go_etcd_io/raft/v3/InvPb.lean` (as `SizeEntry.lean` was until out_size C3).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb
public import Proof.go_etcd_io.raft.v3.PbContentOwn

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

/-- `proto.Size(m)` of a `*pb.Message`, in two forms:

1. holding `ms` (`msgPtsC`, at any fractions, with or without its entries' capacity): some `int`,
   the message back. Nothing is said of the result: `msgPtsC` admits an entry pointer repeated many
   times (the entries are read-only, `entRoC`) and says nothing of what the responses point to.
2. at the content `c` with no responses (`msgPtsCC`): if `c`'s size (`msgSize`, protobuf's formula,
   as `proto.SizePb`'s) is below `2^63`, the result is it.

Against protobuf-go v1.36.12 (`proto/size.go:19-40`, `internal/impl/encode.go:63-117`): the length of
the wire encoding, summed with Go's wrapping `int` additions, each repeated message element's size
recomputed, nothing checked: a true size of `2^63` or more wraps without a panic (`proto.SizePb`'s
docstring), and with no responses each partial sum is at most the total, so below `2^63` the result
is the size. It reads the message (its entries, snapshot, context and responses) and stores the size
cache atomically: a write to the hidden fields only, which the hidden-field invariant (`pbMsg`,
inside `msgPtsC`/`msgPtsCC`) owns. (Until rafthttpfix, 2026-11-20, form 1 only, with `0 ≤ n`: false,
a message repeating one large entry `2^30` times sizes negative,
`notes/axiom-review/proto-sizemessage-fix.md`, `examples/axiomcx/protosizewrap`.) -/
abbrev proto.SizeMessage.spec : Prop :=
  (∀ (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt),
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ msgPtsC l dq dqe cap ms }}
      (App (Val (@! google_golang_org.protobuf.proto.Size)) (Val #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #l)))
    {{ (n : w64), RET #n; msgPtsC l dq dqe cap ms }}) ∧
  (∀ (l : Loc) (dq dqe : DFrac) (cap : Bool) (c : MsgC), c.resps = [] →
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ msgPtsCC l dq dqe cap c }}
      (App (Val (@! google_golang_org.protobuf.proto.Size)) (Val #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #l)))
    {{ (n : w64), RET #n; msgPtsCC l dq dqe cap c ∗ ⌜msgSize c < 2 ^ 63 → sint.Z n = msgSize c⌝ }})

end spec

end EtcdGrove
end Perennial
