/-
`ConfChangesToString(ccs)` (`raftpb/confchange.go:156`).

**Assumed (trust boundary).** The body is translated, but it formats into a `strings.Builder`
(`WriteByte`, `WriteString`, `String`) with `fmt.Fprintf(&buf, "%d", cc.GetNodeId())`, and neither
Perennial (its `strings` translation is the `Builder` type only, no methods; `fmt.Fprintf` is
names-only) nor this repository specifies them. The triple is true of Go: the loop reads each
single through its nil-safe getters (`ccsPts`), writes only the local builder (Go's `Builder` grows
its own buffer; `Fprintf` of a `uint64` under `%d` calls no method) and returns its string; no
panic.

Users: raft's `DescribeEntry` (`util.go:216`, the conf-change formatter of a log line), which has
no spec on this branch (debug output only): no specified caller; kept because its body is
translated and R3 asked for it (`req/go_etcd_io_raft_v3_raftpb.md`, "from R3").

Proof sketch (were `strings.Builder` and `fmt.Fprintf` specified): a builder; per element
(`ccsPts`: each single at `dq`) `GetType()`, a byte or string written (`ccLetter`), `Fprintf` of
`GetNodeId()`; `buf.String()`.

Changes: verify-round: (A5-provability F1) stated as assumed (its sketch cited Perennial specs that
do not exist); the `Users` line corrected (`util.go:216` is `DescribeEntry`). The triple is
unchanged.

Margin: the string's value is not specified (no user reads it but a logger).
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

/-- **Assumed.** `ConfChangesToString(sl)` of a slice of changes: some string, the slice given back. -/
def ConfChangesToString.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (cs : List ConfChangeSingle),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ccsPts sl dq cs }}
    (App (Val (@! go_etcd_io.raft.v3.raftpb.ConfChangesToString)) (Val #sl))
  {{ (s : GoString), RET #s; ccsPts sl dq cs }}

end spec

end RaftPb
end EtcdGrove
end Perennial
