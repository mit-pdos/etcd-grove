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

/-- **A client admin call's history update** (persistent): `v3rpc.authHistAuT`'s, its header told
bound to the token of some attempt of the call `ctx` on `conn`. -/
def clientHistAu (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (ctx : GoInterface)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) : IProp GF :=
  histAu ρ.raft ρ.kv srvAuthSt0
    (fun hm => iprop(∃ md, ⌜clientAttemptMd conn ctx md⌝ ∗
      v3rpc.hdrBoundT s E.authMode (auth.mdTokenOf md) hm)) rq Q

instance clientHistAu_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (ctx : GoInterface) (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) :
    Persistent (clientHistAu s E ρ conn ctx rq Q) := by
  unfold clientHistAu; infer_instance

/-- A client's update is one at the token of each of its attempts. -/
theorem clientHistAu_attempt (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (ctx : GoInterface) (md : GrpcMd) (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF)
    (hmd : clientAttemptMd conn ctx md) :
    clientHistAu (GF := GF) s E ρ conn ctx rq Q ⊢
      v3rpc.authHistAuT s E ρ (auth.mdTokenOf md) rq Q := by
  unfold clientHistAu v3rpc.authHistAuT
  apply histAu_mono
  intro hm
  iintro Hb
  iexists md
  iframe Hb
  ipureintro; exact hmd

end defs

end client
end EtcdGrove
end Perennial
