/-
`barrier(addr)` (`examples/etcd/dist/client/auth.go`; authN's, copied): root's linearizable read of `z/barrier`
through a new client of `addr`, closed at return. Over `New_user_dist` (`newUserClient.spec`) and `KV_GetOn_dist`:
on success the member `addr` serves has published an auth index whose state is the history's after a requested
prefix extending the caller's `L₀` (`barrierFloor`, `AuthLeaseDefs.lean`). Lean-first (no Rocq counterpart); F7
stage S4.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist etcd_dist.authd

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `barrier(addr)`, auth on, `addr` serving a member of the view, the caller's lower bound `L₀` of the requested
log: `true` and `barrierFloor Γ γR L₀ addr`, or `false`. -/
abbrev barrier.spec : Prop :=
  ∀ [π : NetProtoGS] (addr : GoString) (V : WEnv GF) (Γ : DistView) (γR : ServerRaftNames)
    (L₀ : List EntryModel),
  threadBound GF ≤ 2 ^ 30 → plainEndpoint addr →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) → Γ.auth = true → γR.raft.log = Γ.kv.rlog →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ membersAt (Gg := hG.goose_globalGS) [addr] Γ ∗ srvReqLogLb γR L₀ }}
    (App (Val (@! client.barrier)) (Val #addr))
  {{ (ok : Bool), RET #ok; levelTok 0 ∗ (⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ barrierFloor Γ γR L₀ addr)) }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
