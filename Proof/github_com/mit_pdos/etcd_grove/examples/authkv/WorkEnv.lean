/-
**What a principal's workload runs against** (`notes/authkv-main-plan.md`, S2, S4, S6; draft,
2026-10-29). Lean-first (no Rocq counterpart).

`Work(c, who)` runs on a client `c` of authkv's member after `SetUp`. What it needs:
- **the principal's token** (`akPrincipal`). `u` and `v`'s clients were built with their user name
  (C1: `userClientAt`, a token issued to the user or the context's own). `anon` and `bad` share the
  set-up's client, which has no user name: its attempts carry the context's own token only
  (`attemptTokOk` at `False`), so `anon`'s none, and `bad`'s `badtoken` (`reqCtx`,
  `badCtx_unbound`);
- **the member's KV methods with auth on** (`akKVOn`: what `etcd_kv_auth_served_on` gives);
- **the history invariant** (S1, `Hist.lean`);
- **the auth state fixed after the set-up** (S6, `akAuthFixed`): every requested log extending the
  set-up's `Lset` has the auth state `setupSt _`.

S4 (the watch with auth on) is not here: `watcher.Watch.spec` covers prefix watches of a non-empty
key, at the state's events, with nothing of auth. `Work`'s refused watch, `u`'s range watch and
root's watch of every key need it generalized (the plan's S4). Until then `Work.spec` takes the
watcher's facts as `Main` has them (`watchAddrFacts`).

**Draft.** `akAuthFixed` is stated over today's names (`srvRLogLb`, the model's `kvRaftOfOn`).
The auth-mode merge's step 5 and 5b (`srvReqLogLb`, `srvAuthAtLog`, `admStates`, the client's
history view) replace them before the freeze. `akAuthFixed_alloc` is S6's stub.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Hist
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.ClientAuth
public import Proof.go_etcd_io.etcd.client.v3.ClientUser
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposeOn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The principal `who`'s token on the connection `conn`** (persistent): `u`'s and `v`'s clients
send a token issued to their user (C1); `anon`'s and `bad`'s, the context's own. -/
def akPrincipal (conn : Loc) (γa : auth.AuthNames) (who : GoString) : IProp GF :=
  if who = go!"u" ∨ who = go!"v" then userClientAt conn γa who
  else attemptTokOk conn (fun _ => iprop(False))

instance akPrincipal_persistent (conn : Loc) (γa : auth.AuthNames) (who : GoString) :
    Persistent (akPrincipal (GF := GF) conn γa who) := by
  unfold akPrincipal; split <;> infer_instance

/-- **The member's KV methods with auth on, at `addr`** (persistent; what
`etcd_kv_auth_served_on` gives). -/
def akKVOn (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid : w64) : IProp GF :=
  iprop(isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn s E ρ cid mid) ∗
    isGrpcRpcMd addr go!"/etcdserverpb.KV/Range" (etcdRangeSpecOn s E γr cid mid) ∗
    isGrpcRpcMd addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpecOn s E ρ cid mid) ∗
    isGrpcRpcMd addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpecOn s E ρ γr cid mid))

instance akKVOn_persistent (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid : w64) : Persistent (akKVOn (GF := GF) addr s E ρ γr cid mid) := by
  unfold akKVOn; infer_instance

/-- The model's auth state after the requested log `L` (draft: step 5's `srvAuthAtLog`). -/
def akAuthAt (ρ : ReqNames) (L : List EntryModel) : auth.AuthState :=
  (kvRaftOfOn ρ.kv.c0 ρ.kv.ch0 (srvAuthSt0, ρ.kv.log0) L).1

/-- **The auth state fixed after the set-up** (S6; persistent): the set-up's log `Lset` is
committed, and every committed log extending it has the auth state `setupSt` at some revision. -/
def akAuthFixed (ρ : ReqNames) (Lset : List EntryModel) : IProp GF :=
  iprop(srvRLogLb ρ.raft Lset ∗
    □ ∀ L, ⌜Lset <+: L⌝ -∗ srvRLogLb ρ.raft L -∗ ⌜∃ r, akAuthAt ρ L = setupSt r⌝)

instance akAuthFixed_persistent (ρ : ReqNames) (Lset : List EntryModel) :
    Persistent (akAuthFixed (GF := GF) ρ Lset) := by
  unfold akAuthFixed; infer_instance

end defs

end authkv
end EtcdGrove
end Perennial
