/-
`v3rpc.Server(s, tls, interceptor, gopts...)` (`v3rpc/grpc.go`; item 4, the server start): the
gRPC server etcd serves its services with. Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvGrpcStart.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart

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

/-- **`Server(s, nil, nil, gopts...)`** (no TLS, no extra interceptor; `gopts` neutral options,
read-only) returns a `*grpc.Server` being built (`grpcSrvNew`) with etcd's unary chain
`[il, im, iu]` (`newLogUnaryInterceptor(s)`'s, grpc-prometheus's, `newUnaryInterceptor(s)`'s) and
stream chain `[ims, is]` (grpc-prometheus's, `newStreamInterceptor(s)`'s), all transparent, and
etcd's services registered: among them the KV service's `Put`, `Range`, `DeleteRange`, `Txn` on
the `*quotaKVServer` `q` over the `*kvServer` `p` (`kvRegs`) and the `Watch` stream on the
`*watchServer` `pw` (`watchSReg`), given the service values' method sets (`ServerMethodSets`, Go's
type checker's facts). The server's resources come back (the progress interval
written by `NewWatchServer`). -/
abbrev v3rpc.Server.spec : Prop :=
  v3rpc.ServerMethodSets → ∀ (s : Loc) (C : v3rpc.GrpcCfg GF) (d : w64) (gsl : GoSlice) (gvs : List GoInterface),
  -- the backend stays under its quota (audit phase B3, D19h)
  apply.backendUnderQuota →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.grpcCfgOk s C ∗ srvLgReader s ∗ srvBemuReader s ∗ srvGoRes s ∗
      srvCfgFieldAddr s go!"WatchProgressNotifyInterval" ↦ d ∗ ⌜sint.Z d ≤ 2 ^ 62⌝ ∗
      gsl ↦*□ gvs ∗ ⌜∀ v ∈ gvs, grpcSrvOpt v .neutral⌝ }}
    (App (App (App (App (Val (@! v3rpc.Server)) (Val #s)) (Val #(null : Loc)))
      (Val #(func.nil : GoFunc))) (Val #gsl))
  {{ (gs : Loc), RET #gs; ∃ (q p pw : Loc) (il im iu ims is : GoFunc) (svcs : List GoString)
      (regs sregs : List (GoString × val × GoInterface)) (cid mid : w64) (R : v3rpc.WSrv GF)
      (d' : w64),
      grpcSrvNew gs [il, im, iu] [ims, is] svcs regs sregs ∗
      ⌜(∀ x ∈ v3rpc.kvRegs q, x ∈ regs) ∧ v3rpc.watchSReg pw ∈ sregs⌝ ∗
      v3rpc.quotaKVServerAt q ⟨go.GoType.PointerType v3rpc.kvServer.ty, #p⟩ s ∗
      v3rpc.kvServerIs p s C.A cid mid C.n ∗
      v3rpc.isWatchServer pw R ∗ ⌜R.s = s ∧ R.E = C.E ∧ R.wsl = C.wsl ∧ R.γ = C.γ⌝ ∗
      (□ ∀ (γi : IdNames) (C : GoInterfaceOk → IProp GF),
        srvIdGen s γi -∗ idCred γi 1 -∗ □ (∀ ci', reqIdCtxAt γi ci' -∗ C ci') -∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk C) ∗
      (□ ∀ (Q : GoInterface → IProp GF) (C : GoInterfaceOk → IProp GF),
        srvInterceptorOk im iprop(True) Q C) ∗
      (□ ∀ C : GoInterfaceOk → IProp GF,
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk C) ∗
      srvStreamInterceptorOk ims iprop(True) ∗ srvStreamInterceptorOk is iprop(True) ∗
      srvLgReader s ∗ srvBemuReader s ∗ srvGoRes s ∗
      srvCfgFieldAddr s go!"WatchProgressNotifyInterval" ↦ d' }}

end spec

end EtcdGrove
end Perennial
