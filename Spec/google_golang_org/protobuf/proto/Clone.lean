/-
`proto.Clone(m)` (protobuf-go, assumed: `proto/merge.go`).

Users: the client's `cloneCompare` (`compare.go:193`, W0), raft's `raftLog.snapshot`,
`unstable.restore`, `nextUnstableSnapshot` (`log.go:295`, `log_unstable.go:114,196`, R3), etcd's
`raft.go:228,231`, `bootstrap.go:470`, `snapshot_merge.go:48` (2d, 2e: snapshots and `ConfState`s).

Why true: `Clone` allocates a new message of the same type and merges the source into it: a deep
copy (every submessage and byte slice new), recursing per level; it reads the source only.

Changes: from `specs-ref/.../proto/{Clone,ClonePb,CloneEntry,CloneSnapshot,CloneConfState}.lean`:
one spec over `msgAt`; the result's owner relation law gives each caller its model back.

Margin: none (a `nil` message, which `Clone` returns as `nil`, is not specified: no user).
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

/-- `proto.Clone(m)` of a message holding `c` (any fraction, given back): a fresh message of the same
type holding `c`, owned. -/
def Clone.spec : Prop :=
  ∀ (t : go.GoType) (p : Loc) (dq : DFrac) (c : Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ msgAt t p dq c ∗ ⌜depth c < depthMax⌝ }}
    (App (Val (@! google_golang_org.protobuf.proto.Clone)) (Val #(msgVal t p)))
  {{ (v : GoInterface), RET #v; msgAt t p dq c ∗
      ∃ p' : Loc, ⌜v = msgVal t p'⌝ ∗ msgAt t p' (DFrac.own 1) c }}

end spec

end Proto
end EtcdGrove
end Perennial
