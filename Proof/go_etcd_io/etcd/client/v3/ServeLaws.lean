/-
**The started server's linked facts, as hypotheses** (the import tiers, 2026-11-18): the statements of
v3rpc's `Results.lean`'s `raftKV_serverM`, `ServeFromStart.lean`'s `grpcCfgOk_of_startedM` and
`AuthnServedOn.lean`'s `authTokReg_of`, each as `<name>.law : Prop`, which a function's proof
(`etcdstart.Serve`, the auth barriers) takes as a hypothesis instead of importing those linking
modules; `<name>_law_holds` (beside the lemma; `raftKV_serverM`'s in `ServeFromStart.lean`) proves
it, and the `Link`s pass it.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.AuthnSpec
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServe
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWatchBuilt
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI
open Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section laws1
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `raftKV_serverM`'s statement (`Results.lean`, a linking module), as a hypothesis of the proofs
that use it (the import tiers); `raftKV_serverM_law_holds` proves it. -/
abbrev raftKV_serverM.law : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
      (d : v3rpc.KVDep GF) (na : Nat) (tok : Option GoString),
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ ⌜E.authMode ≠ .any⌝ ∗
        isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ⊢
      raftKV s (srvKVAnsM E.authOn s E ρ γr c F d na tok)

end laws1

end v3rpc
end EtcdGrove
end Perennial

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section laws2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `grpcCfgOk_of_startedM`'s statement (`ServeFromStart.lean`, a linking module), as a hypothesis
of the proofs that use it (the import tiers); `grpcCfgOk_of_startedM_law_holds` proves it. -/
abbrev grpcCfgOk_of_startedM.law : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
      (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (tos : List GoInterface) (on : Bool)
      (A : v3rpc.KVAns GF),
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ zapLoggerOk cfg.Logger' ∗
        isServerReqM on s E ρ ∗ isServerReadM on s E γr ∗ srvAuthLb s E ∗ v3rpc.raftKV s A ∗
        srvServeFacts s E cfg ∗ srvWatchBuilt s E ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.eofVar ∗
        cfg.TracerOptions' ↦*□ tos ⊢
      |==> ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk s C ∗ ⌜C.A = A ∧ C.E = E⌝

end laws2

end client
end EtcdGrove
end Perennial

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section laws3
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `authTokReg_of`'s statement (`AuthnServedOn.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `authTokReg_of_law_holds` proves it. -/
abbrev authTokReg_of.law : Prop :=
  ∀ (addr u pw : GoString) (γa : auth.AuthNames),
    isGrpcRpc (GF := GF) addr authnMethod (etcdAuthenticateSpec γa) ⊢
      authTokReg [addr] u pw (fun t => auth.tokIssued γa t u)

end laws3

end client
end EtcdGrove
end Perennial
