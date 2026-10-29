/-
**authkv's history invariant** (`notes/authkv-main-plan.md`, S1; draft, 2026-10-29). Lean-first
(no Rocq counterpart).

`CheckHistory` panics unless every event of root's watch above the set-up's revision `setupRev`,
but root's last write `z/end`, is a write its key's principal was permitted (`histOk`). The events
are the KV state's (`KVState.revEvents`), so `Main` keeps an invariant on the KV state, the
client's half `etcdKV γk σ`, that says so of every revision above `setupRev` (`stateHistOk`).

A write changes the state only through the update its client hands the server, fired at the
commit (`kv_prop_au_on`). With auth on the update is told, as it fires, the server's grant at that
commit: `kvAu1G`'s `G σ` (the auth-mode merge's step 5, `notes/auth-mode-merge-plan.md`; candidate
3: `writeGrantAt`). This file is independent of `G`'s form. An update keeps the invariant if
whatever `G` it is told makes the write's new events ones the invariant admits
(`akHist_writeAu`'s premise, `opHistOk`). From the grant to `opHistOk` is the workload's
reasoning (S2: the token's principal, the state at `setupSt`, `granted_setupSt_iff`). An
ungranted principal's update is then never fired with a `G σ` that holds.

**Draft.** `kvAu1G` here is a stand-in for step 5's (same shape: the update's atomic
postcondition carries `G σ`). The laws are `sorry`: the stage's stubs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Checks
public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-! ## The history's predicate on a KV state -/

section pure
variable [GooseExts]

/-- Root's last write's key, `z/end`. -/
abbrev endKey : GoString := go!"z/end"

/-- A key the history admits after the set-up: one its principal (`writerK`) was permitted, or
root's `z/end`. -/
def keyHistOk (k : GoString) : Prop := permittedK (writerK k) k ∨ k = endKey

/-- **The history's predicate on a KV state** (S1): every event of a revision above `setupRev` is
on a key the history admits. -/
def stateHistOk (setupRev : Nat) (σ : KVState) : Prop :=
  ∀ r, setupRev < r → ∀ ev ∈ σ.revEvents r, keyHistOk ev.kv.key

/-- **A KV operation the history admits**: from any state, the events of the revisions it adds
are on keys the history admits. -/
def opHistOk (op : KVOp) : Prop :=
  ∀ (σ : KVState) (r : Nat), σ.rev < r → ∀ ev ∈ (kvOpStep op σ).revEvents r, keyHistOk ev.kv.key

/-- **An operation keeps the predicate** (stub): it changes no revision at or below the state's
(`kvOpStep` appends), and the ones it adds are admitted. -/
theorem stateHistOk_step (setupRev : Nat) (op : KVOp) (σ : KVState)
    (h : stateHistOk setupRev σ) (hop : opHistOk op) : stateHistOk setupRev (kvOpStep op σ) := by
  sorry

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A client's update by `f`, fired at most once, told `G σ` when it fires** (draft: the
stand-in for the auth-mode merge's step 5 `kvAu1G`, whose shape this is). -/
def kvAu1G (γk : KVNames) (f : KVState → KVState) (G : KVState → IProp GF)
    (Q : KVState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
          <{ etcdKV γk (f σ) ∗ G σ, COMM Q σ }>)

/-- The history invariant's namespace. -/
def akHistN : Namespace := nroot .@ "authkv_hist"

/-- **The history invariant** (S1; persistent): the client's half of the KV state, at a state
whose revisions above `setupRev` the history admits. -/
def akHistInv (γk : KVNames) (setupRev : Nat) : IProp GF :=
  inv akHistN iprop(∃ σ : KVState, etcdKV γk σ ∗ ⌜stateHistOk setupRev σ⌝)

instance akHistInv_persistent (γk : KVNames) (setupRev : Nat) :
    Persistent (akHistInv (GF := GF) γk setupRev) := by
  unfold akHistInv; infer_instance

/-- **The invariant's allocation** (stub): once `SetUp` returns, from the client's half at a state
whose revision is `setupRev` (nothing above it yet). -/
theorem akHist_alloc (γk : KVNames) (σ : KVState) (setupRev : Nat) (h : σ.rev ≤ setupRev) :
    etcdKV (GF := GF) γk σ ⊢ |={⊤}=> akHistInv γk setupRev := by
  sorry

/-- **A write's update under the invariant** (stub): an update whose grant `G` makes the operation
one the history admits keeps the invariant. Its result is `True`; the caller's own result goes
through `Q`'s other conjuncts in S2. -/
theorem akHist_writeAu (γk : KVNames) (setupRev : Nat) (op : KVOp) (G : KVState → IProp GF)
    (hG : ∀ σ, G σ ⊢ ⌜opHistOk op⌝) :
    akHistInv (GF := GF) γk setupRev ⊢ kvAu1G γk (kvOpStep op) G (fun _ => iprop(True)) := by
  sorry

/-- **A read's update under the invariant** (stub): a read (root's watch, `u`'s watch: the
watch's read update, as watchkv's `wk_read_au`) fired at a state the invariant holds, so every
revision of it above `setupRev` is admitted. -/
theorem akHist_readAu (γk : KVNames) (setupRev : Nat) :
    akHistInv (GF := GF) γk setupRev ⊢ kvReadAu γk (fun σ => iprop(⌜stateHistOk setupRev σ⌝)) := by
  sorry

end defs

end authkv
end EtcdGrove
end Perennial
