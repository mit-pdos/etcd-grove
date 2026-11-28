/-
**authlease's driver vocabulary** (auth-lease S4, item 9): what the helpers' specs (`barriers`,
`grantPut`, `noAuth`, `foreign`, `absent`) are written in. A barrier's arguments at one member
(`BArgs`) with `barrier.spec`'s precondition (`barrierPre`) and success (`barrierPost`), for the
barrier loop `barriers`. Lean-first (no Rocq counterpart).

Moved here from the authlease example's `authlease/Env.lean` (2026-11-27): the multi-machine theorem
reuses it (names and namespace `etcd_authlease` unchanged).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.WorkEnv
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc3On
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKVOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthTie
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseTimeToLive_Handler
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseLeases_Handler
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseGrant
public import Proof.go_etcd_io.etcd.client.v3.AuthnSpec
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLeaseOn
public import Proof.go_etcd_io.etcd.client.v3.LeaseSpecs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.WorkAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseCellModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver client etcd_auth

/-- **`grantPut`'s and the checks' lease TTL** (`grantTTL`: etcd's `MaxLeaseTTL`, so that no lease of
the run expires however long the process runs, `lease.leasesNoExpiry`). -/
abbrev grantTTLv : w64 := W64 9000000000

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A barrier's arguments at one member** (`barrier.spec`'s, but the logger): its client address,
its client's watch environment (`barrier.spec`'s `V`, which the barrier's client is made with),
server, environment and request names, ids, auth names, the set-up's frozen history, requested log and
committed log, its auth state's revision, and the caller's read update. -/
structure BArgs (GF : BundledGFunctors) where
  addr : GoString
  V : client.WEnv GF
  s : Loc
  E : apply.AEnv GF
  ρ : ReqNames
  cid : w64
  mid : w64
  γa : auth.AuthNames
  γz : GName
  hs : List auth.AuthState
  Lset : List EntryModel
  Lc : List EntryModel
  r : Nat
  Q : KVState → IProp GF

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`barrier.spec`'s precondition at `b`** (persistent), but the package and the logger. -/
def barrierPre (b : BArgs GF) : IProp GF :=
  iprop(⌜plainEndpoint b.addr ∧ b.E.authMode = .on b.γa⌝ ∗
    isGrpcRpc b.addr authnMethod (etcdAuthenticateSpec b.γa) ∗
    akKVOn b.addr b.s b.E b.ρ b.cid b.mid ∗ isServerReadM b.E.authOn b.s b.E b.ρ.rd ∗
    authHistFrozen b.ρ.kv b.γz b.hs ∗ srvReqLogLb b.ρ.raft b.Lset ∗
    ⌜admStates b.ρ.kv srvAuthSt0 b.Lset = b.hs ∧ srvAuthAtLog b.ρ.kv srvAuthSt0 b.Lset = setupSt b.r⌝ ∗
    srvRLogLb b.ρ.raft b.Lc ∗ ⌜srvAuthAtLog b.ρ.kv srvAuthSt0 b.Lc = setupSt b.r⌝ ∗
    □ (⌜b.Q = fun _ => iprop(True)⌝ ∨ kvReadAu b.ρ.rd.kv b.Q))

instance barrierPre_persistent (b : BArgs GF) : Persistent (barrierPre b) := by
  unfold barrierPre; infer_instance

/-- **`barrier.spec`'s success at `b`** (persistent): the auth state fixed after the set-up, and the
member's floor with the read update's result. -/
def barrierPost (b : BArgs GF) : IProp GF :=
  iprop((∃ i : Nat, akAuthFixed b.γa b.ρ b.Lset i) ∗
    ∃ (log : mvcc.Log) (lt : LeaseTable), srvApi.kvLogLb b.E.γs log ∗ □ b.Q (kvStateOf log lt))

instance barrierPost_persistent (b : BArgs GF) : Persistent (barrierPost b) := by
  unfold barrierPost; infer_instance

end defs

end etcd_authlease
end EtcdGrove
end Perennial
