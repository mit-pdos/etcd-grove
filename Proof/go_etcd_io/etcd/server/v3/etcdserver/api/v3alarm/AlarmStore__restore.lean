/-
The trust boundary: `(*v3alarm.AlarmStore).restore()` (`alarms.go`, names-only: it reads the alarm
bucket through `schema`'s names-only alarm backend and decodes protobuf records). Lean-first (no
Rocq counterpart); D22 receiver epochs, S7c (2026-10-23): why the statement is true of the Go code
is in its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore__restore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom v3alarm.AlarmStore.restore.wp_proof :
  v3alarm.AlarmStore.restore.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
