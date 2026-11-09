/-
`ConfChangesToString(ccs)` (`raftpb/confchange.go:170`).

Users: raft's `DescribeConfChange` (`util.go:216`, R3: log lines), the examples' tracing.

Proof sketch: a `strings.Builder` (Perennial's); per element (`ccsPts`: each single at `dq`),
`GetType()`, a byte or string written, `fmt.Fprintf(&buf, "%d", GetNodeId())` (Perennial's `fmt`);
`buf.String()`.

Changes: new on this branch (no old spec; R3 asked for it). Margin: the string's value is not
specified (no user reads it but a logger).
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftPb

open Iris Iris.BI
open go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- `ConfChangesToString(sl)` of a slice of changes: some string, the slice given back. -/
def ConfChangesToString.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (cs : List ConfChangeSingle),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ccsPts sl dq cs }}
    (App (Val (@! go_etcd_io.raft.v3.raftpb.ConfChangesToString)) (Val #sl))
  {{ (s : GoString), RET #s; ccsPts sl dq cs }}

end spec

end RaftPb
end EtcdGrove
end Perennial
