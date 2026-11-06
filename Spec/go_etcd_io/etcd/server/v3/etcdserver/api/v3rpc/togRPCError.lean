/-
`v3rpc.togRPCError` (`util.go`). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvKV.lean` and `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`togRPCError(err)`** of an error it can take (`srvErrIs`) whose `Error()` returns a message
with `P` (`errMsgP`): a non-nil error, `err` itself (a context error), the error map's value, or a
`status` error with code `Unknown` whose description has `P` (`grpcErrOut`; k8s etcd3 7c-2: it was
only the non-nil error). `togRPCError_plain` is the triple at `P := fun _ => True`. -/
abbrev v3rpc.togRPCError.spec : Prop :=
  ∀ (P : GoString → Prop) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.srvErrIs err ∗ v3rpc.errMsgP err P }}
    (App (Val (@! v3rpc.togRPCError)) (Val #err))
  {{ (e : GoInterface), RET #e; ⌜e ≠ GoInterface.nil⌝ ∗ v3rpc.grpcErrOut P err e }}

end spec

end EtcdGrove
end Perennial
