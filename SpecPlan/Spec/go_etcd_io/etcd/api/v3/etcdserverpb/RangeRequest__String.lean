/-
`(*etcdserverpb.RangeRequest).String()` (`api/etcdserverpb/rpc.pb.go`, generated, names only here:
assumed; `protoimpl.X.MessageStringOf(x)`, protobuf's reflective text format).

Users: `v3rpc`'s `logUnaryRequestStats` (`server/etcdserver/api/v3rpc/interceptor.go:118`), the
server's `Range` (`server/etcdserver/v3_server.go:126`, through `txn.WarnOfExpensiveReadOnlyRangeRequest`'s
`fmt.Stringer`: `stringerAt_msg`).

Why true: it reads the request's fields (the message's internal state, which `ProtoReflect`
initializes with an atomic store, is inside `msgAt`, as for `proto.Size`) and returns some string.

Changes: verify-round: restored (A6 completeness F6: dropped from the old tree,
Re-review (R-A6, second tier): premise `depth c < depthMax` (text marshaling recurses per level).
`specs-ref/Spec/go_etcd_io/etcd/api/v3/etcdserverpb/RangeRequest__String.lean`), over `msgAt` at any
share (was txn's `rangeRequestIs`).
Margin: the string's content is not modelled (its users log it).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI
open go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `r.String()` of a range request held at `dq`: some string, the share given back. -/
def RangeRequest.String.spec : Prop :=
  ∀ (r : Loc) (dq : DFrac) (c : Proto.Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      Proto.msgAt etcdserverpb.RangeRequest.ty r dq c ∗ ⌜Proto.depth c < Proto.depthMax⌝ }}
    (App (Val (r @!! go.GoType.PointerType etcdserverpb.RangeRequest.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; Proto.msgAt etcdserverpb.RangeRequest.ty r dq c }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
