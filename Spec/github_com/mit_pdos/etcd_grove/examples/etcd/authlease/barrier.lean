/-
`barrier(addr, lg)` (`examples/etcd/authlease/authlease.go`; authN's, 2026-11-18, with the read's update and
floor): root's linearizable read of `z/barrier` through a new client of the member at `addr`, after the
set-up. Lean-first (no Rocq counterpart).

**The triple:** authN's `barrier.spec` (the auth state fixed after the set-up at the member,
`akAuthFixed`), with the caller's read update `Q` (`client_range_on`'s: none, or a persistent
`kvReadAu`): `true` also gives the floor of the member's store at the log the read met
(`srvApi.kvLogLb`) and `Q` of that log's state (the lessor law's floor, auth-lease S4 §8.3: barrier 2
at the member a check then reaches).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.AuthFixed
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Base
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseTimeToLive_Handler
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseLeases_Handler
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseGrant
public import Proof.go_etcd_io.etcd.client.v3.AuthnSpec
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver client etcd_auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

/-- See the file header. -/
abbrev barrier.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (addr : GoString) (lg : Loc) (V : WEnv GF) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γa : auth.AuthNames) (γz : GName) (hs : List auth.AuthState)
    (Lset Lc : List EntryModel) (r : Nat) (Q : KVState → IProp GF),
  plainEndpoint addr → threadBound GF ≤ 2 ^ 30 → E.authMode = .on γa →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authlease ∗ levelTok 0 ∗ (zapLoggerOk lg ∗ isGrpcRpc addr authnMethod (etcdAuthenticateSpec γa) ∗
      akKVOn addr s E ρ cid mid ∗ isServerReadM E.authOn s E ρ.rd ∗
      authHistFrozen ρ.kv γz hs ∗ srvReqLogLb ρ.raft Lset ∗
      ⌜admStates ρ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog ρ.kv srvAuthSt0 Lset = setupSt r⌝ ∗
      srvRLogLb ρ.raft Lc ∗ ⌜srvAuthAtLog ρ.kv srvAuthSt0 Lc = setupSt r⌝ ∗
      □ (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu ρ.rd.kv Q)) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.authlease.barrier)) (Val #addr))
      (Val #lg))
  {{ (ok : Bool), RET #ok; levelTok 0 ∗ (⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ (∃ i : Nat, akAuthFixed γa ρ Lset i) ∗
      ∃ (log : mvcc.Log) (lt : LeaseTable), srvApi.kvLogLb E.γs log ∗ □ Q (kvStateOf log lt))) }}

end spec

end etcd_authlease
end EtcdGrove
end Perennial
