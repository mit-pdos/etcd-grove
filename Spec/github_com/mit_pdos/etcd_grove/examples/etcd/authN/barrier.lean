/-
`barrier(addr, lg)` (`examples/etcd/authN/authN.go`; auth3's, copied into authN, 2026-11-15): root's
linearizable read of `z/barrier` through a new client of the member at `addr`, after the set-up.
Lean-first (no Rocq counterpart).

**The triple:** at a member `s` with auth on at `γa` (its KV methods and `Authenticate` registered at
`addr`, its read view `isServerReadM true`), given the set-up's facts at the member's names (the
auth history frozen at `hs`, the set-up's requested log `Lset` and a committed log `Lc`, each with
the set-up's last state `setupSt r`: `SetUp`'s post, carried to the member's names by
`etcdstart.sameCluster`), `true` only with the auth state fixed after the set-up at the member
(`akAuthFixed γa ρ Lset i`, at some published index `i`: `akAuthFixed_barrier`); `false` otherwise
(the client's or the read's error).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.AuthFixed
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.Base
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseTimeToLive_Handler
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseLeases_Handler
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseGrant
public import Proof.go_etcd_io.etcd.client.v3.AuthnSpec
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authN

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver client etcd_auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authN.Assumptions]

/-- See the file header. -/
abbrev barrier.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (addr : GoString) (lg : Loc) (V : WEnv GF) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γa : auth.AuthNames) (γz : GName) (hs : List auth.AuthState)
    (Lset Lc : List EntryModel) (r : Nat),
  plainEndpoint addr → threadBound GF ≤ 2 ^ 30 → E.authMode = .on γa →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authN ∗ levelTok 0 ∗ (zapLoggerOk lg ∗ isGrpcRpc addr authnMethod (etcdAuthenticateSpec γa) ∗
      akKVOn addr s E ρ cid mid ∗ isServerReadM true s E ρ.rd ∗
      authHistFrozen ρ.kv γz hs ∗ srvReqLogLb ρ.raft Lset ∗
      ⌜admStates ρ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog ρ.kv srvAuthSt0 Lset = setupSt r⌝ ∗
      srvRLogLb ρ.raft Lc ∗ ⌜srvAuthAtLog ρ.kv srvAuthSt0 Lc = setupSt r⌝) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.authN.barrier)) (Val #addr))
      (Val #lg))
  {{ (ok : Bool), RET #ok; levelTok 0 ∗ (⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ ∃ i : Nat, akAuthFixed γa ρ Lset i)) }}

end spec

end etcd_authN
end EtcdGrove
end Perennial
