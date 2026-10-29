/-
**What a principal's workload runs against** (`notes/authkv-main-plan.md`, S2, S4, S6; draft,
2026-10-29). Lean-first (no Rocq counterpart).

`Work(c, who)` runs on a client `c` of authkv's member after `SetUp`. What it needs:
- **the principal's tokens** (`akTokP`, at `clientTokAt`). `u` and `v`'s clients were built with
  their user name (C1: a token issued to the user or the context's own). `anon` and `bad` share the
  set-up's client, which has no user name: its attempts carry the context's own token only, so
  `anon`'s none, and `bad`'s `badtoken` (`reqCtx`, `badCtx_unbound`; round 1, F-W4: `reqCtx.spec`
  does not yet say the timeout context has no outgoing token);
- **the member's KV methods with auth on** (`akKVOn`: what `etcd_kv_auth_served_on` gives);
- **the history invariant** (S1, `Hist.lean`);
- **the auth state fixed after the set-up** (S6, `akAuthFixed`): every auth state from the set-up's
  published index on, and every requested log extending the set-up's `Lset`, at `setupSt _`.

S4 (the watch with auth on) is not here: `watcher.Watch.spec` covers prefix watches of a non-empty
key, at the state's events, with nothing of auth. `Work`'s refused watch, `u`'s range watch and
root's watch of every key need it generalized (the plan's S4). Until then `Work.spec` takes the
watcher's facts as `Main` has them (`watchAddrFacts`).

**Draft.** `akAuthFixed`'s write half is over 5b's frozen history (`SetUp`'s post); its read half
waits for its source, 5b's deferred read tie. `akAuthFixed_alloc` is S6's stub.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Hist
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.ClientAuth
public import Proof.go_etcd_io.etcd.client.v3.ClientUser
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposeOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthModel

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

/-- **The tokens principal `who`'s client sends** (round 1, F-W5: `Work` takes
`clientTokAt cl [addr] (akTokP γa who)`, what `Main` holds): `u`'s and `v`'s clients were built
with their user name, so tokens issued to it (`newUserClient`, `clientTokAt_user`); `anon` and
`bad` share the set-up's client, built with none (`common.NewClient`, at `False`), so their
attempts carry the context's own token only. -/
def akTokP (γa : auth.AuthNames) (who : GoString) : GoString → IProp GF :=
  if who = go!"u" ∨ who = go!"v" then fun t => auth.tokIssued γa t who else fun _ => iprop(False)

/-- **The member's KV methods with auth on, at `addr`** (persistent; what
`etcd_kv_auth_served_on` gives). -/
def akKVOn (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    IProp GF :=
  iprop(isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn s E ρ cid mid) ∗
    isGrpcRpcMd addr go!"/etcdserverpb.KV/Range" (etcdRangeSpecOn s E ρ.rd cid mid) ∗
    isGrpcRpcMd addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpecOn s E ρ cid mid) ∗
    isGrpcRpcMd addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpecOn s E ρ ρ.rd cid mid))

instance akKVOn_persistent (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) : Persistent (akKVOn (GF := GF) addr s E ρ cid mid) := by
  unfold akKVOn; infer_instance

/-- **The auth state fixed after the set-up** (S6; persistent): for reads (round 1, F-W1), the
set-up's published index `n` and every state of the auth history from it on `setupSt` at some
revision (`client_range_on`/`client_txn_on`'s verdicts are from states at indices at least the
published bound they are given; its source, 5b's deferred read tie, `notes/authkv-main-plan.md`);
for writes (5b), the set-up's requested log `Lset` and the auth history frozen at its history
(`SetUp`'s post), whose last state is `setupSt`: a write's grant at a log extending `Lset`
(`writeGrantG`'s `authHistLb`) is then at `setupSt` (`akAuthFixed_write`). -/
def akAuthFixed (γa : auth.AuthNames) (ρ : ReqNames) (Lset : List EntryModel) (n : Nat) :
    IProp GF :=
  iprop(auth.authPubLb γa n ∗
    □ (∀ m st, ⌜n ≤ m⌝ -∗ auth.authStateAt γa m st -∗ ⌜∃ r, st = setupSt r⌝) ∗
    srvReqLogLb ρ.raft Lset ∗
    ∃ (γz : GName) (hs : List auth.AuthState) (r : Nat), authHistFrozen ρ.kv γz hs ∗
      ⌜admStates ρ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog ρ.kv srvAuthSt0 Lset = setupSt r⌝)

instance akAuthFixed_persistent (γa : auth.AuthNames) (ρ : ReqNames) (Lset : List EntryModel)
    (n : Nat) : Persistent (akAuthFixed (GF := GF) γa ρ Lset n) := by
  unfold akAuthFixed; infer_instance

/-- **A write granted after the set-up is granted at `setupSt`**: the grant's log `L` extends
`Lset` and its history is a lower bound (`writeGrantG`), so the frozen history is `L`'s
(`authHistFrozen_prefix`, `admStates_prefix`) and `L`'s auth state is `Lset`'s. -/
theorem akAuthFixed_write (γa : auth.AuthNames) (ρ : ReqNames) (Lset : List EntryModel) (n : Nat)
    (L : List EntryModel) (E : CoPset) (hE : ↑authHistN ⊆ E) (hL : Lset <+: L) :
    ⊢ akAuthFixed (GF := GF) γa ρ Lset n -∗ authHistLb ρ.kv (admStates ρ.kv srvAuthSt0 L) ={E}=∗
      ⌜∃ r, srvAuthAtLog ρ.kv srvAuthSt0 L = setupSt r⌝ := by
  iintro #Hf #Hlb
  iunfold akAuthFixed at Hf
  icases Hf with ⟨-, -, -, %γz, %hs, %r, #Hz, %Hh⟩
  imod (authHistFrozen_prefix ρ.kv γz hs _ E hE) $$ Hz Hlb with %Hp
  imodintro
  ipureintro
  have h1 := admStates_prefix ρ.kv srvAuthSt0 _ _ hL
  rw [Hh.1] at h1
  have heq : hs = admStates ρ.kv srvAuthSt0 L :=
    h1.eq_of_length (Nat.le_antisymm h1.length_le Hp.length_le)
  exact ⟨r, (srvAuthAtLog_of_admStates ρ.kv srvAuthSt0 Lset L (Hh.1.trans heq)).symm.trans Hh.2⟩

end defs

end authkv
end EtcdGrove
end Perennial
