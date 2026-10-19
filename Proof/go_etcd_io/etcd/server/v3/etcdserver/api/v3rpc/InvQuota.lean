/-
**The quota wrapper of the KV service and the server's unary interceptors** (`v3rpc/quota.go`,
`v3rpc/interceptor.go`, unit P3b): `NewQuotaKVServer(s)`
wraps the KV service (`NewKVServer(s)`) in a `*quotaKVServer`, whose `Put` (and `Txn`) first
checks the backend's quota (`quotaAlarmer.check`: `newBackendQuota(s, name).Available`, a quota of
the backend current at the check; if not, it raises the NOSPACE alarm through `s.Alarm` and
answers `ErrGRPCNoSpace`), and whose other methods are the embedded service's (promoted).
Lean-first (no Rocq counterpart).

* `quotaAlarmerAt qa s` (persistent): the `*quotaAlarmer` `qa`, read-only: its server `s` and
  its quota's name (since the fork's 8f793b820, D22g (A),
  `issues/etcd-quota-stale-backend-after-snapshot.md`: until then the quota itself, built over
  the backend current at construction, which a snapshot's install replaces and closes), the
  server's fields `newBackendQuota` reads (`s.lg`, `s.Cfg.QuotaBackendBytes`), and the workload
  premise under which every quota answers `Available` (`apply.backendUnderQuota`, which the
  constructors take).
* `quotaRd s` (not persistent): what a check spends and gets back: the reader slots of `s.lgMu`
  and `s.bemu` (`newBackendQuota`'s `s.Logger()` and `s.Backend()`).
* `quotaKVServerAt q kv s` (persistent): the `*quotaKVServer` `q`, read-only: its embedded
  `KVServer` the value `kv`, its alarmer `quotaAlarmerAt`.
* `QuotaKVServerIsKVServer`: `*quotaKVServer` implements `pb.KVServer` (a method-set fact, which
  the model leaves uninterpreted: `methodSet`; Go's type checker establishes it,
  `NewQuotaKVServer` converts a `*quotaKVServer` to `pb.KVServer`), as context's
  `ErrorStringIsError`: an assumption about the semantics.
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

/-- **`*quotaKVServer` implements `pb.KVServer`** (a method-set fact; see the file header). -/
class v3rpc.QuotaKVServerIsKVServer [FfiSyntax] [GoGlobalContext] [GoLocalContext]
    [GoSemanticsFunctions] : Prop where
  is_kv : go.typeSetContains (go.GoType.PointerType v3rpc.quotaKVServer.ty)
    etcdserverpb.KVServer.ty = true

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The `*quotaAlarmer` `qa`** (persistent; see the file header). -/
def v3rpc.quotaAlarmerAt (qa s : Loc) : IProp GF :=
  iprop(∃ (name : GoString) (lg : Loc) (qb : w64),
    structFieldRef v3rpc.quotaAlarmer go!"s" qa ↦□ s ∗
    structFieldRef v3rpc.quotaAlarmer go!"name" qa ↦□ name ∗
    srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ qb ∗
    ⌜apply.backendUnderQuota⌝)

instance v3rpc.quotaAlarmerAt_persistent (qa s : Loc) :
    Persistent (v3rpc.quotaAlarmerAt (GF := GF) qa s) := by
  unfold v3rpc.quotaAlarmerAt; infer_instance

/-- **What a quota check spends and gets back** (see the file header). -/
def v3rpc.quotaRd (s : Loc) : IProp GF :=
  iprop(srvLgReader s ∗ srvBemuReader s)

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
