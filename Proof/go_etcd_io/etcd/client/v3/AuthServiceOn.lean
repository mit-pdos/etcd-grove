/-
**A client's admin call's history update** (the auth-mode merge's 5b, 2026-10-29): the update an
admin call through the client's `Auth` (`authClient.UserAdd`, ...) hands the server
(`v3rpc.authHistAuT`, etcd's `Auth` specs), at the token of some attempt of the call (the caller does
not know which attempt's metadata the server saw), as `clientGrant` for a write's grant.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KVServiceOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthService

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **A client admin call's history update** (persistent): `v3rpc.authHistAuT`'s, its header told
bound to the token of some attempt of the call on `conn` with a context of outgoing metadata `om`
(errdesc stage 1, 2026-11-20: until then indexed by the context). -/
def clientHistAu (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (om : GrpcMd)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) : IProp GF :=
  histAu ρ.raft ρ.kv srvAuthSt0
    (fun hm => iprop(∃ md, clientAttemptMd conn om md ∗
      v3rpc.hdrBoundT T E.authMode (auth.mdTokenOf md) hm)) rq Q

instance clientHistAu_persistent (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (om : GrpcMd) (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) :
    Persistent (clientHistAu T E ρ conn om rq Q) := by
  unfold clientHistAu; infer_instance

/-- A client's update is one at the token of each of its attempts. -/
theorem clientHistAu_attempt (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (om : GrpcMd) (md : GrpcMd) (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) :
    clientAttemptMd conn om md ⊢ clientHistAu (GF := GF) T E ρ conn om rq Q -∗
      v3rpc.authHistAuT T E ρ (auth.mdTokenOf md) rq Q := by
  unfold clientHistAu v3rpc.authHistAuT
  have h : ∀ hm, clientAttemptMd conn om md ∗ v3rpc.hdrBoundT T E.authMode (auth.mdTokenOf md) hm ⊢
      iprop(∃ md, clientAttemptMd conn om md ∗ v3rpc.hdrBoundT T E.authMode (auth.mdTokenOf md) hm) := by
    intro hm
    iintro ⟨#Hmd, Hb⟩
    iexists md
    iframe Hb Hmd
  iintro #Hmd H
  iapply (histAu_mono_with _ _ _ _ _ _ _ (clientAttemptMd conn om md) h) $$ [Hmd H]
  iframe Hmd H

end defs

end client
end EtcdGrove
end Perennial
