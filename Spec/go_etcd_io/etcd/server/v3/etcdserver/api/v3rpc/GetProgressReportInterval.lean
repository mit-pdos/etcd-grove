/-
`v3rpc.GetProgressReportInterval` (`watch.go`). Lean-first (no Rocq counterpart); the
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`GetProgressReportInterval()`**, by a thread (its token, returned: the thread borrows a
reader slot of the interval's lock from the package's pool, `v3rpc.intervalPool`, while
`threadBound GF` is at most the slots' number; 2026-10-20, watchkv: until then the caller's
reader slot): the interval with a jitter of less than a tenth of it, positive. -/
abbrev v3rpc.GetProgressReportInterval.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.watchVars ∗ threadTok ∗
      ⌜threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders⌝ }}
    (App (Val (@! v3rpc.GetProgressReportInterval)) (Val #()))
  {{ (d : w64), RET #d; ⌜0 < sint.Z d⌝ ∗ threadTok }}

end spec

end EtcdGrove
end Perennial
