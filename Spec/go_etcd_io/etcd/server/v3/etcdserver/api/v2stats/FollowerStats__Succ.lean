/-
`(*v2stats.FollowerStats).Succ(d)`: the trust boundary (v2stats is names-only but for
`NewLeaderStats`; `Succ` is floating-point latency bookkeeping under the stats' own lock: `math.Sqrt`
of running averages). rafthttp's msgappv2 encoder calls it after each frame. A no-op spec, as the
metrics' (D33). Lean-first.
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

/-- `fs.Succ(d)` of a non-nil `*FollowerStats` returns. -/
abbrev v2stats.FollowerStats.Succ.spec : Prop :=
  ∀ (fs : Loc) (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗ ⌜fs ≠ null⌝ }}
    (App (Val (fs @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.FollowerStats.ty @!! go!"Succ")) (Val #d))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
