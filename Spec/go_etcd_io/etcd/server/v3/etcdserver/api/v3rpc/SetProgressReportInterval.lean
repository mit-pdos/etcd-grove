/-
`v3rpc.SetProgressReportInterval` (`watch.go`). Lean-first (no Rocq counterpart); the
vocabulary is `v3rpc/InvWatchStream.lean` and `v3rpc/InvWatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`SetProgressReportInterval(d)`** of an interval between `10` nanoseconds and `2 ^ 62` (the
lock's invariant, `intervalP`: `GetProgressReportInterval` divides it by ten and adds a jitter). -/
abbrev v3rpc.SetProgressReportInterval.spec : Prop :=
  ∀ d : w64,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.watchVars ∗ ⌜10 ≤ sint.Z d ∧ sint.Z d ≤ 2 ^ 62⌝ }}
    (App (Val (@! v3rpc.SetProgressReportInterval)) (Val #d))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
