/-
`etcdserverpb.RangeRequest.String()`: the trust boundary (`api/etcdserverpb/rpc.pb.go`, names-only:
`protoimpl.X.MessageStringOf(x)`, protobuf's reflective text format). Lean-first (no Rocq
counterpart); unit P4 (2026-10-14), for the server's `Range` (its request is the
`fmt.Stringer` `txn.WarnOfExpensiveReadOnlyRangeRequest` logs).

It reads the request's fields (`rangeRequestIs`, read-only; the message's internal state, which
`ProtoReflect` initializes with an atomic store, is not modelled, as for `proto.Size`) and returns
some string.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `r.String()` of the range request `r` (`rangeRequestIs`): some string. -/
abbrev RangeRequest.String.spec : Prop :=
  ∀ (r : Loc) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      txn.rangeRequestIs r o }}
    (App (Val (r @!! go.GoType.PointerType etcdserverpb.RangeRequest.ty @!! go!"String"))
      (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
