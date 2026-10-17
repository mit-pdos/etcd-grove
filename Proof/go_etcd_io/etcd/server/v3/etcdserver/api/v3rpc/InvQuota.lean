/-
**The quota wrapper of the KV service and the server's unary interceptors** (`v3rpc/quota.go`,
`v3rpc/interceptor.go`, unit P3b): `NewQuotaKVServer(s)`
wraps the KV service (`NewKVServer(s)`) in a `*quotaKVServer`, whose `Put` (and `Txn`) first
checks the backend's quota (`quotaAlarmer.check`: the quota's `Available`; if not, it raises the
NOSPACE alarm through `s.Alarm` and answers `ErrGRPCNoSpace`), and whose other methods are the
embedded service's (promoted). Lean-first (no Rocq counterpart).

* `quotaAlarmerAt qa s` (persistent): the `*quotaAlarmer` `qa`, read-only: its quota (a
  `storage.Quota`, `apply.isQuota`: `storage` is names-only, `NewBackendQuota` the trust
  boundary), its alarmer the server `s`, its member id.
* `quotaKVServerAt q kv s` (persistent): the `*quotaKVServer` `q`, read-only: its embedded
  `KVServer` the value `kv`, its alarmer `quotaAlarmerAt`.
* `quotaKVServer_is_KVServer`: `*quotaKVServer` implements `pb.KVServer` (`NewQuotaKVServer`
  converts a `*quotaKVServer` to `pb.KVServer`): from the method sets of the packages'
  `Assumptions` (`go_type_set`; an assumed class until Perennial `5f111b9a8`).
* `learnerReqOk req` (persistent): what the unary interceptor's learner check
  (`isRPCSupportedForLearner`) reads of a request: an interface holding a pointer (or `nil`),
  and, for a `*RangeRequest`, its `Serializable` read-only.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

/-- **`*quotaKVServer` implements `pb.KVServer`** (see the file header). -/
theorem v3rpc.quotaKVServer_is_KVServer [FfiSyntax] [GoGlobalContext] [GoLocalContext]
    [go.Semantics] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] :
    go.typeSetContains (go.GoType.PointerType v3rpc.quotaKVServer.ty)
      etcdserverpb.KVServer.ty = true := by
  go_type_set

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The `*quotaAlarmer` `qa`** (persistent; see the file header). -/
def v3rpc.quotaAlarmerAt (qa s : Loc) : IProp GF :=
  iprop(∃ (q : GoInterface) (id : w64),
    structFieldRef v3rpc.quotaAlarmer go!"q" qa ↦□ q ∗ apply.isQuota q ∗
    structFieldRef v3rpc.quotaAlarmer go!"a" qa ↦□
      (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s : GoInterface) ∗
    structFieldRef v3rpc.quotaAlarmer go!"id" qa ↦□ id)

instance v3rpc.quotaAlarmerAt_persistent (qa s : Loc) :
    Persistent (v3rpc.quotaAlarmerAt (GF := GF) qa s) := by
  unfold v3rpc.quotaAlarmerAt; infer_instance

/-- **The `*quotaKVServer` `q`** over the service `kv` and the server `s` (persistent; see the
file header). -/
def v3rpc.quotaKVServerAt (q : Loc) (kv : GoInterfaceOk) (s : Loc) : IProp GF :=
  iprop(⌜q ≠ null⌝ ∗
    structFieldRef v3rpc.quotaKVServer go!"KVServer" q ↦□ GoInterface.ok kv ∗
    v3rpc.quotaAlarmerAt (structFieldRef v3rpc.quotaKVServer go!"qa" q) s)

instance v3rpc.quotaKVServerAt_persistent (q : Loc) (kv : GoInterfaceOk) (s : Loc) :
    Persistent (v3rpc.quotaKVServerAt (GF := GF) q kv s) := by
  unfold v3rpc.quotaKVServerAt; infer_instance

/-- **What the learner check reads of a request** (persistent; see the file header). -/
def v3rpc.learnerReqOk (req : GoInterface) : IProp GF :=
  iprop(⌜req = GoInterface.nil ∨ ∃ (t : go.GoType) (l : Loc), req = interface.mkOk t #l⌝ ∗
    ∀ r : Loc, ⌜req = interface.mkOk (go.GoType.PointerType etcdserverpb.RangeRequest.ty) #r⌝ →
      ∃ b : Bool, structFieldRef etcdserverpb.RangeRequest go!"Serializable" r ↦□ b)

instance v3rpc.learnerReqOk_persistent (req : GoInterface) :
    Persistent (v3rpc.learnerReqOk (GF := GF) req) := by
  unfold v3rpc.learnerReqOk; infer_instance

end defs

end EtcdGrove
end Perennial
