/-
**authkv's history invariant** (`notes/authkv-main-plan.md`, S1; round 3, 2026-10-30). Lean-first
(no Rocq counterpart).

`CheckHistory` panics unless every event of root's watch above the set-up's revision `setupRev`,
but root's last write `z/end` and a repeat of a set-up put (`SetupWrite`), is a write its key's
principal was permitted (`histOk`). The events are the KV state's (`KVState.revEvents`), so `Main`
keeps an invariant on the KV state, the client's half `etcdKV γk σ`, that says so of every event
of every revision (`stateHistOk`): over the whole log, so that it is allocated at the boot state
(no event), before `SetUp`, and `SetUp`'s puts are updates under it (`akHist_setupAu`; round 3,
F-S1: a set-up put may be applied again after `SetUp` returns, the client retrying it, so the
checker tolerates one at any revision).

A write changes the state only through the update its client hands the server, fired at the
commit (`kv_prop_au_on`). With auth on the update is told, as it fires, the server's grant at that
commit: `kvAu1G`'s `G σ` (the auth-mode merge's step 5, `notes/auth-mode-merge-plan.md`; candidate
3: `writeGrantG`). This file is independent of `G`'s form. An update keeps the invariant if
whatever `G` it is told makes the write's new events ones the invariant admits
(`akHist_writeAu`'s premise, `opHistOk`). From the grant to `opHistOk` is the workload's
reasoning (S2: the token's principal, the state at `setupSt`, `granted_setupSt_iff`). An
ungranted principal's update is then never fired with a `G σ` that holds.

The update is step 5's `kvAu1G` (`InvRequest.lean`), at whatever `G`; with auth on, the server's
`writeGrantG … L₀`. Proved: `stateHistOk_step`, `opHistOk_setupPut`, `akHist_alloc`,
`akHist_setupAu` (over `akHist_writeAu`); `akHist_writeAu` and `akHist_readAu` are `sorry`: the
stage's stubs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Checks
public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchStep

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

/-- **An event the history admits**: a write its key's principal (`writerK`) was permitted,
root's `z/end`, or a repeat of a set-up put (`setupPutK`: a key of `setupKeys` with the value
`setup`, `SetupWrite`'s model without the event's kind). The kind is left out: the model's event
of a put is a delete only when the key's previous create revision, or the revision itself, is `0`,
which no state of the server's has; so a set-up put's event is admitted from any state
(`opHistOk_setupPut`), and the reader of the history shows the kind (a put) from the server's. -/
def evHistOk (ev : mvcc.EvM) : Prop :=
  permittedK (writerK ev.kv.key) ev.kv.key ∨ ev.kv.key = endKey ∨
    setupPutK ev.kv.key ev.kv.value

/-- **The history's predicate on a KV state** (S1): every event of every revision is one the
history admits. -/
def stateHistOk (σ : KVState) : Prop :=
  ∀ r, ∀ ev ∈ σ.revEvents r, evHistOk ev

/-- **A KV operation the history admits**: from any state, the events of the revisions it adds
are ones the history admits. -/
def opHistOk (op : KVOp) : Prop :=
  ∀ (σ : KVState) (r : Nat), σ.rev < r → ∀ ev ∈ (kvOpStep op σ).revEvents r, evHistOk ev

/-- An operation keeps the events of the revisions up to the state's: it commits at most one
revision after them (`KVState.commit_at`, `commit_changesAt`), or changes only the lease table. -/
theorem revEvents_kvOpStep (op : KVOp) (σ : KVState) (r : Nat) (hr : r ≤ σ.rev) :
    (kvOpStep op σ).revEvents r = σ.revEvents r := by
  have hc : ∀ cs, (σ.commit cs).revEvents r = σ.revEvents r := by
    intro cs
    unfold KVState.revEvents
    rw [KVState.commit_at _ _ _ (by omega), KVState.commit_changesAt _ _ _ hr]
  cases op <;> simp only [kvOpStep] <;> (repeat' split) <;> first | rfl | exact hc _

/-- **An operation keeps the predicate**: it changes no revision at or below the state's
(`revEvents_kvOpStep`), and the ones it adds are admitted (`opHistOk`). -/
theorem stateHistOk_step (op : KVOp) (σ : KVState)
    (h : stateHistOk σ) (hop : opHistOk op) : stateHistOk (kvOpStep op σ) := by
  intro r ev hev
  by_cases hle : r ≤ σ.rev
  · rw [revEvents_kvOpStep op σ r hle] at hev
    exact h r ev hev
  · exact hop σ r (by omega) ev hev

/-- The client's put of `k ↦ v` (no lease, no flag) commits the one change `put k v 0`. -/
theorem kvOpStep_putKeyOp (k v : GoString) (σ : KVState) :
    kvOpStep (.put (client.putKeyOp k v)) σ = σ.commit [.put k v (W64 0)] := by
  simp [kvOpStep, KVState.leaseMissing, client.putKeyOp, txn.putOpOf, txn.needsPrev,
    txn.putChangeOf, txn.putValOf, txn.putLeaseOf]

/-- The events of a revision after the state's, in the state with one more revision of the one
change `c`: none, or `c`'s. -/
theorem revEvents_commit_one (σ : KVState) (c : mvcc.Change) (r : Nat) (hr : σ.rev < r) :
    ∀ ev ∈ (σ.commit [c]).revEvents r, ∃ b, ev = mvcc.evOfKv r (v3rpc.chKv (W64 (r : Int)) b c) := by
  intro ev hev
  unfold KVState.revEvents at hev
  have hch : (σ.commit [c]).changesAt r = [] ∨ (σ.commit [c]).changesAt r = [c] := by
    unfold KVState.rev at hr
    unfold KVState.changesAt KVState.commit
    simp only [List.cons_ne_nil, ↓reduceIte]
    split
    · left; rfl
    · by_cases he : r - σ.compacted - 1 = σ.changes.length
      · right; rw [he, List.getElem?_append_right (Nat.le_refl _)]; simp
      · left; rw [List.getElem?_eq_none (by simp; omega)]; rfl
  rcases hch with h | h
  · rw [h, mvcc.evsOfRevM_nil] at hev; cases hev
  · rw [h, v3rpc.evsOfRevM_cons _ _ (KVStore.kvs_sorted _), mvcc.evsOfRevM_nil] at hev
    rw [List.mem_singleton] at hev
    exact ⟨_, hev⟩

/-- **A set-up put is admitted** from any state: its one event is of its key and value. -/
theorem opHistOk_setupPut (k : GoString) (hk : k ∈ setupKeys) :
    opHistOk (.put (client.putKeyOp k go!"setup")) := by
  intro σ r hr ev hev
  rw [kvOpStep_putKeyOp] at hev
  obtain ⟨b, rfl⟩ := revEvents_commit_one σ _ r hr ev hev
  right; right
  have hkey : (v3rpc.chKv (W64 (r : Int)) b (.put k go!"setup" (W64 0))).key = k :=
    v3rpc.chKv_key _ _ _
  have hval : (v3rpc.chKv (W64 (r : Int)) b (.put k go!"setup" (W64 0))).value = go!"setup" := by
    simp only [v3rpc.chKv, txn.putNv]; split <;> rfl
  generalize v3rpc.chKv (W64 (r : Int)) b (.put k go!"setup" (W64 0)) = kv at hkey hval
  unfold mvcc.evOfKv
  split <;> exact ⟨by simpa [hkey] using hk, hval⟩

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The history invariant's namespace. -/
def akHistN : Namespace := nroot .@ "authkv_hist"

/-- **The history invariant** (S1; persistent): the client's half of the KV state, at a state
whose every event the history admits. -/
def akHistInv (γk : KVNames) : IProp GF :=
  inv akHistN iprop(∃ σ : KVState, etcdKV γk σ ∗ ⌜stateHistOk σ⌝)

instance akHistInv_persistent (γk : KVNames) :
    Persistent (akHistInv (GF := GF) γk) := by
  unfold akHistInv; infer_instance

/-- **The invariant's allocation**: from the client's half at a state the history admits (the
boot state, before `SetUp`: no event). -/
theorem akHist_alloc (γk : KVNames) (σ : KVState) (h : stateHistOk σ) :
    etcdKV (GF := GF) γk σ ⊢ |={⊤}=> akHistInv γk := by
  iintro Hσ
  unfold akHistInv
  iapply inv_alloc akHistN ⊤
  inext
  iexists σ
  iframe Hσ
  ipureintro; exact h

/-- **A write's update under the invariant** (stub; round 1, F-H1/F-H2): an update whose grant
`G`, as it fires, makes the operation one the history admits keeps the invariant. The caller
refutes or uses the grant with what it holds (`clientTokAt`, `akAuthFixed`, the TLS refutation)
inside `hG`, in the mask the update fires in, the invariant opened; `Q` is the caller's result: a
refused principal's write takes `Q := False`, so its reply (`putReplied … Q`) cannot exist. -/
theorem akHist_writeAu (γk : KVNames) (op : KVOp) (G Q : KVState → IProp GF) :
    akHistInv (GF := GF) γk ∗
      □ (∀ σ, G σ -∗ |={((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑akHistN}=> ⌜opHistOk op⌝ ∗ Q σ) ⊢
    □ kvAu1G γk (kvOpStep op) G Q := by
  sorry

/-- **A read's update under the invariant** (stub): a read (root's watch, `u`'s watch: the
watch's read update, as watchkv's `wk_read_au`) fired at a state the invariant holds, so every
event of it is admitted. -/
theorem akHist_readAu (γk : KVNames) :
    akHistInv (GF := GF) γk ⊢ kvReadAu γk (fun σ => iprop(⌜stateHistOk σ⌝)) := by
  sorry

/-- An update told nothing (`G := True`) is a plain one. -/
theorem kvAu1G_true (γk : KVNames) (f : KVState → KVState) (Q : KVState → IProp GF) :
    kvAu1G (GF := GF) γk f (fun _ => iprop(True)) Q ⊢ kvAu1 γk f Q := by
  unfold kvAu1 kvAu1G
  exact aupd_post_mono (fun _ _ => sep_true_mpr)

/-- **`SetUp`'s puts under the invariant** (F-S1, round 3): a put of a set-up key with the value
`setup` keeps it from any state (`opHistOk_setupPut`), told nothing (`akHist_writeAu` at
`G := True`). -/
theorem akHist_setupAu (γk : KVNames) (k : GoString) (hk : k ∈ setupKeys) :
    akHistInv (GF := GF) γk ⊢
      □ kvOpAu1 γk (.put (client.putKeyOp k go!"setup")) (fun _ => iprop(True)) := by
  iintro #Hinv
  ihave #Hau := akHist_writeAu γk (.put (client.putKeyOp k go!"setup")) (fun _ => iprop(True))
    (fun _ => iprop(True)) $$ [Hinv]
  · isplitl []
    · iexact Hinv
    · iintro !> %σ -
      imodintro
      isplitl []
      · ipureintro; exact opHistOk_setupPut k hk
      · itrivial
  imodintro
  unfold kvOpAu1
  iapply kvAu1G_true
  iexact Hau

end defs

end authkv
end EtcdGrove
end Perennial
