/-
**authkv's history invariant** (`notes/authkv-main-plan.md`, S1; round 3, 2026-10-30). Lean-first
(no Rocq counterpart).

`CheckHistory` panics unless every event of root's watch, but root's last write `z/end` and the
set-up's puts (`SetupWrite`), is a write its key's principal was permitted (`histOk`). The events
are the KV state's (`KVState.revEvents`), so `Main` keeps an invariant on the KV state, the
client's half `etcdKV γk σ`, that says so of every event of every revision (`stateHistOk`): over
the whole log, so that it is allocated at the boot state (no event, `stateHistOk_boot`), before
`SetUp`, and `SetUp`'s puts are updates under it (`akHist_setupAu`; round 3, F-S1: `SetUp` gives
each put a persistent update, which the proof's model lets fire more than once, so the checker
admits a set-up put at any revision).

A write changes the state only through the update its client hands the server, fired at the
commit (`kv_prop_au_on`). With auth on the update is told, as it fires, the server's grant at that
commit: `kvAu1G`'s `G σ` (the auth-mode merge's step 5, `notes/auth-mode-merge-plan.md`; candidate
3: `writeGrantG`). This file is independent of `G`'s form. An update keeps the invariant if
whatever `G` it is told makes the write's new events ones the invariant admits
(`akHist_writeAu`'s premise, `opHistOk`). From the grant to `opHistOk` is the workload's
reasoning (S2: the token's principal, the state at `setupSt`, `granted_setupSt_iff`). An
ungranted principal's update is then never fired with a `G σ` that holds.

The update is step 5's `kvAu1G` (`InvRequest.lean`), at whatever `G`; with auth on, the server's
`writeGrantG … L₀`. Proved: `stateHistOk_step`, `opHistOk_putKey` (`opHistOk_setupPut`,
`opHistOk_endPut`), `stateHistOk_boot`, `revEvents_setupPut_put`, `histOk_of_evHistOk`,
`akHist_alloc`, `akHist_setupAu` (over `akHist_writeAu`); `akHist_writeAu` and `akHist_readAu`
are `sorry`: the stage's stubs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Checks
public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchStep
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLogOk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ClientLaws
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.HistoryLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.SyncModel

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
of a put is a delete when the key's previous create revision, or the revision itself, is `0`,
which only a state well formed through the revision (`kvLogOkTo`) rules out; so a set-up put's
event is admitted from any state (`opHistOk_setupPut`), and the reader of the history shows the
kind (a put) at the state it reads (`revEvents_setupPut_put`). -/
def evHistOk (ev : mvcc.EvM) : Prop :=
  permittedK (writerK ev.kv.key) ev.kv.key ∨ ev.kv.key = endKey ∨
    setupPutK ev.kv.key ev.kv.value

/-- **The history's check from the invariant's events**: a collected event the history admits,
of the kind put when it is a set-up put's (`setupPutK`; the reader's fact from the server's state,
`revEvents_setupPut_put`), is not one `histOk` refuses. -/
theorem histOk_of_evHistOk (evs : List common.wev)
    (h : ∀ e ∈ evs, permittedK (writerK e.Key') e.Key' ∨ e.Key' = endKey ∨
      (e.Put' = true ∧ setupPutK e.Key' e.Val')) :
    histOk evs endKey := by
  intro e he hne hsw
  rcases h e he with h | h | h
  · exact h
  · exact absurd h hne
  · exact absurd h hsw

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

/-- **A plain put of a key and value the history admits is admitted** from any state: its one
event is of its key and value. -/
theorem opHistOk_putKey (k v : GoString)
    (h : permittedK (writerK k) k ∨ k = endKey ∨ setupPutK k v) :
    opHistOk (.put (client.putKeyOp k v)) := by
  intro σ r hr ev hev
  rw [kvOpStep_putKeyOp] at hev
  obtain ⟨b, rfl⟩ := revEvents_commit_one σ _ r hr ev hev
  have hkey : (v3rpc.chKv (W64 (r : Int)) b (.put k v (W64 0))).key = k :=
    v3rpc.chKv_key _ _ _
  have hval : (v3rpc.chKv (W64 (r : Int)) b (.put k v (W64 0))).value = v := by
    simp only [v3rpc.chKv, txn.putNv]; split <;> rfl
  generalize v3rpc.chKv (W64 (r : Int)) b (.put k v (W64 0)) = kv at hkey hval
  unfold mvcc.evOfKv evHistOk
  split <;> (simp only; rw [hkey, hval]; exact h)

/-- **A set-up put is admitted** from any state (`opHistOk_putKey`). -/
theorem opHistOk_setupPut (k : GoString) (hk : k ∈ setupKeys) :
    opHistOk (.put (client.putKeyOp k go!"setup")) :=
  opHistOk_putKey k _ (Or.inr (Or.inr ⟨hk, rfl⟩))

/-- **Root's last write is admitted** from any state (`opHistOk_putKey`): its key is `endKey`. -/
theorem opHistOk_endPut (v : GoString) : opHistOk (.put (client.putKeyOp endKey v)) :=
  opHistOk_putKey endKey v (Or.inr (Or.inl rfl))

/-- A state whose revisions change nothing has no event. -/
theorem stateHistOk_of_changes_nil (σ : KVState) (h : ∀ cs ∈ σ.changes, cs = []) :
    stateHistOk σ := by
  intro r ev hev
  unfold KVState.revEvents KVState.changesAt at hev
  split at hev
  · rw [mvcc.evsOfRevM_nil] at hev; cases hev
  · cases hc : σ.changes[r - σ.compacted - 1]? with
    | none => rw [hc] at hev; simp only [Option.getD_none, mvcc.evsOfRevM_nil] at hev; cases hev
    | some cs =>
      rw [hc, h cs (List.mem_of_getElem? hc)] at hev
      simp only [Option.getD_some, mvcc.evsOfRevM_nil] at hev; cases hev

/-- A bootstrap log's entries (conf changes) change nothing in the mode-`on` model. -/
theorem kvModelOn_boot (γk : KVNames) (st₀ : auth.AuthState) (ps : List w64)
    (bootLog : List EntryM) (hb : srvBootLogOk ps bootLog) :
    kvModelOn γk st₀ (bootEntries bootLog) = γk.log0 := by
  obtain ⟨-, -, he⟩ := hb
  unfold kvModelOn kvRaftOfOn bootEntries
  rw [List.foldl_map]
  suffices h : ∀ (l : List EntryM) (st : auth.AuthState), (∀ e ∈ l, e.Type' = W32 1) →
      (l.foldl (fun s e => kvEntryOn γk.c0 γk.ch0 s (EntryModel.ofM e)) (st, γk.log0)).2 =
        γk.log0 by
    apply h
    intro e hm
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
    exact (he k _ (List.getElem?_eq_getElem hk)).2.2.1
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons e l ih =>
    intro st hl
    rw [List.foldl_cons]
    have ht : e.Type' = W32 1 := hl e (List.mem_cons_self ..)
    have : kvEntryOn γk.c0 γk.ch0 (st, γk.log0) (EntryModel.ofM e) = (st, γk.log0) := by
      unfold kvEntryOn kvEntry
      simp only [EntryModel.ofM, ht]
      rfl
    rw [this]
    exact ih st (fun e' h' => hl e' (List.mem_cons_of_mem _ h'))

/-- **The boot state is admitted** (`Main` allocates the invariant there, before `SetUp`): the
bootstrap log changes nothing (`kvModelOn_boot`) from the start's log of empty revisions. -/
theorem stateHistOk_boot (γk : KVNames) (st₀ : auth.AuthState) (ps : List w64)
    (bootLog : List EntryM) (hb : srvBootLogOk ps bootLog) (h0 : γk.log0 = [[], []]) :
    stateHistOk (kvStateOf (kvModelOn γk st₀ (bootEntries bootLog))) := by
  rw [kvModelOn_boot γk st₀ ps bootLog hb, h0]
  apply stateHistOk_of_changes_nil
  intro cs hcs
  simp [kvStateOf] at hcs
  exact hcs

/-- **A set-up put's event is a put** in a state well formed through its revision
(`kvLogOkTo`): the model's event of a put is a delete only when the key's create revision is `0`,
which `kvLogOkTo` rules out (every key of the state was created at a positive revision, and the
revision is below `2 ^ 63`); a delete's event has the empty value, not `setup`. -/
theorem revEvents_setupPut_put (σ : KVState) (r m : Nat) (hok : kvLogOkTo σ r) (hm : m ≤ r)
    (ev : mvcc.EvM) (hev : ev ∈ σ.revEvents m) (hsp : setupPutK ev.kv.key ev.kv.value) :
    ev.del = false := by
  obtain ⟨he, hr, hr63, hwf, hsm⟩ := hok
  have hc : σ.compacted = 0 := by rw [he]; rfl
  have hlen : σ.log.length = σ.rev + 1 := by
    simp only [KVState.log, KVState.rev, List.length_cons, hc]; omega
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · unfold KVState.revEvents KVState.changesAt at hev
    rw [if_pos (by omega), mvcc.evsOfRevM_nil] at hev; cases hev
  have hrev : σ.revEvents m = (kvStateOf σ.log).revEvents m := by rw [← he]
  rw [hrev, revEvents_kvStateOf σ.log m hm0 (by omega)] at hev
  have hsort := mvcc.stateAt_sorted σ.log (m - 1)
  have hpre : σ.log.take (r + 1) <+: σ.log := List.take_prefix _ _
  have htl : (σ.log.take (r + 1)).length = r + 1 := by rw [List.length_take]; omega
  have hst : mvcc.stateAt (σ.log.take (r + 1)) (m - 1) = mvcc.stateAt σ.log (m - 1) :=
    (txn.stateAt_of_prefix hpre (r := m - 1) (by rw [htl]; omega)).symm
  have hpos : ∀ x ∈ mvcc.stateAt σ.log (m - 1), 0 < sint.Z x.createRev := by
    intro x hx
    rw [← hst] at hx
    exact (txn.stateAt_client_revs _ hwf (by omega) hsm (m - 1) (by omega) x hx).1
  have hm63 : sint.Z (W64 (m : Int)) = m := by word
  have hmne : W64 (m : Int) ≠ W64 0 := by
    intro h; have := congrArg sint.Z h; rw [hm63] at this; simp at this; omega
  unfold mvcc.evsOfRevM at hev
  rw [List.mem_filterMap] at hev
  obtain ⟨i, -, hi⟩ := hev
  cases hk : mvcc.changeKv (W64 (m : Int)) (mvcc.stateAt σ.log (m - 1)) (σ.log.getD m []) i with
  | none => rw [hk] at hi; cases hi
  | some kv =>
    rw [hk] at hi
    simp only [Option.map_some, Option.some.injEq] at hi
    subst hi
    rcases mvcc.changeKv_cases _ _ hsort _ i kv hk with ⟨k, -, rfl⟩ | ⟨k, v, l, -, -, hkc⟩
    · -- a delete's event has the empty value
      exfalso
      have hv : (mvcc.evOfKv m (zeroKv k)).kv.value = [] := by
        unfold mvcc.evOfKv; split <;> rfl
      rw [hv] at hsp
      exact absurd hsp.2 (by decide)
    · have hne : kv.createRev ≠ W64 0 := by
        rw [hkc]
        cases hf : mvcc.findKey k (mvcc.applyChanges (W64 (m : Int)) (mvcc.stateAt σ.log (m - 1))
            ((σ.log.getD m []).take i)) with
        | none => exact hmne
        | some w =>
          simp only [Option.map_some, Option.getD_some]
          have hw : w ∈ mvcc.applyChanges (W64 (m : Int)) (mvcc.stateAt σ.log (m - 1))
              ((σ.log.getD m []).take i) := by
            unfold mvcc.findKey at hf; exact List.mem_of_find?_eq_some hf
          by_cases hwr : w.createRev = W64 (m : Int)
          · rw [hwr]; exact hmne
          · obtain ⟨u, hu, -, huc⟩ := txn.mem_applyChanges_createRev _ _ w hw hwr
            intro h0
            have := hpos u hu
            rw [huc, h0] at this
            simp at this
      unfold mvcc.evOfKv
      rw [if_neg hne]

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

/-- The invariant's namespace is inside the updates' outer mask. -/
theorem akHistN_mask : (↑akHistN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩,
    fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩

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

/-- **A write's update under the invariant** (round 1, F-H1/F-H2): an update whose grant
`G`, as it fires, makes the operation one the history admits keeps the invariant. The caller
refutes or uses the grant with what it holds (`clientTokAt`, `akAuthFixed`, the TLS refutation)
inside `hG`, in the mask the update fires in, the invariant opened; `Q` is the caller's result: a
refused principal's write takes `Q := False`, so its reply (`putReplied … Q`) cannot exist. -/
theorem akHist_writeAu (γk : KVNames) (op : KVOp) (G Q : KVState → IProp GF) :
    akHistInv (GF := GF) γk ∗
      □ (∀ σ, G σ -∗ |={((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑akHistN}=> ⌜opHistOk op⌝ ∗ Q σ) ⊢
    □ kvAu1G γk (kvOpStep op) G Q := by
  have Hm := akHistN_mask
  iintro ⟨#Hinv, #HG⟩
  imodintro
  unfold kvAu1G
  iauintro
  unfold atomic_acc
  iunfold akHistInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ, %HS⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑akHistN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ] with -
    · inext; iexists σ; iframe; ipureintro; exact HS
    imodintro
    iempintro
  · iintro ⟨Hσ, HGσ⟩
    imod Hclose2 with -
    imod HG $$ HGσ with ⟨%Hop, HQ⟩
    imod Hclose $$ [Hσ] with -
    · inext; iexists _; iframe; ipureintro; exact stateHistOk_step op σ HS Hop
    imodintro
    iexact HQ

/-- **A read's update under the invariant**: a read (root's watch, `u`'s watch: the
watch's read update, as watchkv's `wk_read_au`) fired at a state the invariant holds, so every
event of it is admitted. -/
theorem akHist_readAu (γk : KVNames) :
    akHistInv (GF := GF) γk ⊢ kvReadAu γk (fun σ => iprop(⌜stateHistOk σ⌝)) := by
  have Hm := akHistN_mask
  iintro #Hinv
  unfold kvReadAu kvAu
  imodintro
  iauintro
  unfold atomic_acc
  iunfold akHistInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ, %HS⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑akHistN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ] with -
    · inext; iexists σ; iframe; ipureintro; exact HS
    imodintro
    iempintro
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ] with -
    · inext; iexists σ; iframe; ipureintro; exact HS
    imodintro
    imodintro
    ipureintro; exact HS

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
