/-
`asembleRangeResponse` (`range.go`): the response.
Lean-first; see `InvRange.lean`, `RangeModel.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `asembleRangeResponse(rr, r)`: a fresh response (read-only from then on) with header revision
`rr.Rev`, the first `limit` key-values (a positive limit), `More` if more remained
(`srvTrunc`, `srvMore`), values dropped if keys-only (`respKv`), and `rr.Count`. The result's
key-values are the response's (shared, read-only). -/
abbrev txn.asembleRangeResponse.spec : Prop :=
  ∀ (rr r : Loc) (o : OpFull) (rev count : w64) (vs : List EtcdKv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      txn.rangeResultIs rr rev count vs ∗ txn.rangeRequestIs r o }}
    (App (App (Val (@! txn.asembleRangeResponse)) (Val #rr)) (Val #r))
  {{ (resp : Loc), RET #resp;
      txn.rangeResponseIs resp rev ((txn.srvTrunc o vs).map (txn.respKv o)) (txn.srvMore o vs) count ∗
      txn.respHdrOwn (structFieldRef etcdserverpb.RangeResponse go!"Header" resp) }}

end spec

end EtcdGrove
end Perennial
