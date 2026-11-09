/-
`proto.Size(m)` (protobuf-go, assumed: `proto/size.go`).

Users: raft's `entsSize`/`limitSize` (`util.go`, R3: sums of entry sizes), etcd's
`adjustChunkLimit` (`v3_server.go:270`, 2c), the watch server's fragmenting (`watch.go:618,647`,
2b), `logUnaryRequestStats` (this batch: log fields only), `bootstrap.go:474`, `server.go:719`.

Why true: `Size` walks the message's fields (reads only; the `sizeCache` stores are atomic, inside
`msgAt`) and sums their encoded lengths in an `int`, which wraps without a panic; it recurses once
per level (the depth premise keeps the stack bounded). A `nil` message is not specified (no user).

Changes: from `specs-ref/Spec/google_golang_org/protobuf/proto/{Size,SizePb,SizeEntry,SizeMessage}.lean`:
one spec over `msgAt` for every message type (it was one per caller-built `PbType` record, the
refuted shape of `notes/pbenc-ok-inconsistent.md`).

Margin: the code returns the exact length; the spec gives `encSize c` modulo `2 ^ 64`.
-/
module

public import Spec.google_golang_org.protobuf.proto.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Proto

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.protobuf.proto.Assumptions]

/-- `proto.Size(m)` of a message holding `c` (any fraction, given back): its encoded size, wrapped
to an `int`. -/
def Size.spec : Prop :=
  ∀ (t : go.GoType) (p : Loc) (dq : DFrac) (c : Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ msgAt t p dq c ∗ ⌜depth c < depthMax⌝ }}
    (App (Val (@! google_golang_org.protobuf.proto.Size)) (Val #(msgVal t p)))
  {{ (n : w64), RET #n; msgAt t p dq c ∗ ⌜n = W64 (encSize c)⌝ }}

end spec

end Proto
end EtcdGrove
end Perennial
