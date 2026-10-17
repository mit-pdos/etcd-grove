/-
`proto.Size` of a raft v3.7 `*pb.Message`: the trust boundary (`google.golang.org/protobuf` is
names-only), as `SizeEntry.lean` for a `*pb.Entry`. `snap.NewMessage` sizes the snapshot message
with it (`message.go:44`, branch `pr-verify/etcd-21569`). Lean-first; stated over the raftpb
ownership predicates of `Proof/go_etcd_io/raft/v3/InvPb.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `proto.Size(m)` of a `*pb.Message` holding `ms` (at any fraction) returns some `int` at least
`0`; no spec fixes a size.

Against protobuf-go v1.36.11 (`proto/size.go`, `internal/impl/encode.go`): `Size` is the length
of the wire encoding, a non-negative `int`; it reads the message (and its entries and snapshot)
and stores the size caches atomically: writes to the hidden fields only, which the hidden-field
invariant (`pbMsg`, inside `msgOwn`) owns, as `SizeEntry`'s. -/
abbrev proto.SizeMessage.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (ms : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ msgOwn l dq ms }}
    (App (Val (@! google_golang_org.protobuf.proto.Size))
      (Val #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #l)))
  {{ (n : w64), RET #n; msgOwn l dq ms ∗ ⌜0 ≤ sint.Z n⌝ }}

end spec

end EtcdGrove
end Perennial
