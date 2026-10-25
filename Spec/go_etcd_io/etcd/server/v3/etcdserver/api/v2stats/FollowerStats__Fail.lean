/-
`(*v2stats.FollowerStats).Fail()`: the trust boundary (v2stats is names-only but for
`NewLeaderStats`; `Fail` increments a counter under the stats' own lock, as `Succ` keeps its
latencies: `FollowerStats__Succ.lean`). rafthttp's pipeline calls it after a failed `MsgApp`. A
no-op spec, as `Succ`'s (D38). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `fs.Fail()` of a non-nil `*FollowerStats` returns. -/
abbrev v2stats.FollowerStats.Fail.spec : Prop :=
  ∀ (fs : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗ ⌜fs ≠ null⌝ }}
    (App (Val (fs @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.FollowerStats.ty @!! go!"Fail")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
