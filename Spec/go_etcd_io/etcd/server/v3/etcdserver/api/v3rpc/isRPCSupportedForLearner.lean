/-
`v3rpc.isRPCSupportedForLearner` (`v3rpc/util.go`; unit P3b). Lean-first (no Rocq counterpart);
the vocabulary is `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvQuota.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvQuota

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

/-- **What a learner serves** (pure): a request a learner member answers, given the
`Serializable` field `ser` of a `*RangeRequest` (ignored for any other request): a
`*StatusRequest`, a `*DefragmentRequest` (etcd-io/etcd#21862: defragmentation is local
backend maintenance), or a `*RangeRequest` with `Serializable` set. Everything else (the nil
interface, any other request) is rejected. -/
def v3rpc.learnerServes (req : GoInterface) (ser : Bool) : Prop :=
  (∃ l : Loc, req = interface.mkOk (go.GoType.PointerType etcdserverpb.StatusRequest.ty) #l) ∨
  (∃ l : Loc, req = interface.mkOk (go.GoType.PointerType etcdserverpb.DefragmentRequest.ty) #l) ∨
  (∃ l : Loc, req = interface.mkOk (go.GoType.PointerType etcdserverpb.RangeRequest.ty) #l ∧
    ser = true)

/-- **`isRPCSupportedForLearner(req)`** (etcd-io/etcd#21862): answers whether a learner serves
`req` (`learnerServes`), with `ser` the `Serializable` field it read when `req` is a
`*RangeRequest`. Premise (`learnerReqOk`): what it reads, an interface holding a pointer (or
nil) and, for a `*RangeRequest`, its `Serializable`. -/
abbrev v3rpc.isRPCSupportedForLearner.spec : Prop :=
  ∀ (req : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.learnerReqOk req }}
    (App (Val (@! v3rpc.isRPCSupportedForLearner)) (Val #req))
  {{ (b : Bool), RET #b; ∃ ser : Bool,
      (∀ r : Loc, ⌜req = interface.mkOk (go.GoType.PointerType etcdserverpb.RangeRequest.ty) #r⌝ →
        structFieldRef etcdserverpb.RangeRequest go!"Serializable" r ↦□ ser) ∗
      ⌜b = true ↔ v3rpc.learnerServes req ser⌝ }}

/-- **The spec before etcd-io/etcd#21862** (kept for comparison; `spec_implies_old` in the
proof file): the result was some boolean, unconstrained. Its docstring said `true` for a
`*StatusRequest`, a `*RangeRequest`'s `Serializable`, `false` otherwise. -/
abbrev v3rpc.isRPCSupportedForLearner.spec_old : Prop :=
  ∀ (req : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.learnerReqOk req }}
    (App (Val (@! v3rpc.isRPCSupportedForLearner)) (Val #req))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
