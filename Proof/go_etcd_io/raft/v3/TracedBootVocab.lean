/-
Lean-first (no Rocq counterpart). **Step 5 of the trace-check design (2026-11-12): the traced
constructors' vocabulary** (`notes/trace-check-design.md`, "Step 5 (2026-11-12): the constructors'
statements"; `notes/decisions.md`, "Step 5: the traced constructors"). Raft-internal (not on
`etc/api/raft.txt`): what the specs of `newRaft`, `NewRawNode`, `RawNode.Bootstrap` and `setupNode` are
written in, with its laws.

- The bootstrap's pure vocabulary: `bootPhase` (the capability's phase from `StartNode` to the end of
  `Bootstrap`: the voters `vs`, the voter's bootstrap share, nothing pending), `bootAt` (the last event
  the bootstrap event at position `k`, `BootEvAt`), `bootNone`, `bootCfg` (the voters' configuration, what
  the capability is at during the bootstrap), `BootFresh` (a fresh node: what positions 0-2 need).
- `trCapStart`: the capability before the `raft` struct exists. **Coupled to `trCapB`** (`TracedCap.lean`):
  its traced arm is `trCapB`'s body with the `Config`'s logger in place of the struct's field; a conjunct
  added to `trCapB` must be added here, and `trCapStart_trCapB` re-proved (review `step5-r1.md`'s S3: the
  shared core was not factored out, which would re-open the 15 files that unfold `trCapB`).
- `trNoCut`: the storage never compacted past `1` at a traced node (`TrNoSnap`'s storage-level form).
- `bootDoneG`: a voter's completion witness at raft's level (A8.3).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedCap
public import Proof.go_etcd_io.raft.v3.TracedSend
public import Proof.go_etcd_io.raft.v3.CCApply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

/-! ## The bootstrap's vocabulary (pure) -/

section vocab
variable [GooseExts]

/-- **The bootstrap's phase** (the capability's `Φ` from `StartNode` to the end of `Bootstrap`): the
voters are `vs`, the node's share is its bootstrap server (`simInit vs`'s, `startTrace`'s) with nothing
pending. The bootstrap lines keep the share (`trCap_fire_boot`), so the phase holds throughout; at the end
`simIdle_boot` turns it into `SimIdle C s` (the phase `rnTrace` holds). It fixes `C = vs`, which the
bootstrap gates' `BootNext C id o e` and `trCapB_bootDone`'s `hΛ` need. -/
def bootPhase (vs : List w64) (id : w64) : List w64 → ServerC → List Etcdraft.Msg → Prop :=
  fun C cs P => C = vs ∧ cs = toC (confAbs vs) ((simInit vs).s (idAbs id)) ∧ P = []

/-- **The node's last event is its bootstrap event at position `k`** (the capability's `Λ` between the
bootstrap lines: `BootEvAt`, A7; §5.1's table). -/
def bootAt (vs : List w64) (id : w64) (k : Nat) : Option TraceEv → Prop :=
  fun o => ∃ x, o = some x ∧ BootEvAt vs id k x

/-- **No event yet** (the capability's `Λ` at `StartNode`: `startTrace`'s `simBoot … false none`). -/
def bootNone : Option TraceEv → Prop := fun o => o = none

/-- **The voters' configuration** (`cC` of §5.2): what the capability is stated at during the bootstrap,
apart from raft's own (empty at positions 0-2, growing at positions `k + 4`); `Bootstrap`'s result's
(`cfgState (GMap.listToSet ps) ∅`). -/
def bootCfg (vs : List w64) : CfgM := (cfgState (GMap.listToSet vs) ∅).cfg

/-- **A fresh node** (`newRaft`'s traced scope): an empty storage (no hard state, the base `⟨0, 0⟩`, no
entry) and the empty conf state. Then `traceInitState` logs term `0`, vote `0`, commit `0`, log size `0`
(position 0), `switchToConfig` the empty configuration (position 1) and `becomeFollower` term `0`
(position 2). `setupNode`'s premises imply it. (Review `step5-r1.md`'s N1: no `Applied = 0`, which
`newRaft`'s `appliedTo` premise forces at this storage and no line reads.) -/
def BootFresh (σ : StorState) (hs : HardStateM) (csm : ConfStateM) : Prop :=
  HsEmpty hs ∧ σ.prev = entryID.mk (W64 0) (W64 0) ∧ σ.ents = [] ∧
  csm.Voters' = [] ∧ csm.VotersOutgoing' = [] ∧ csm.Learners' = [] ∧ csm.LearnersNext' = [] ∧
  csm.AutoLeave' = false

end vocab

/-! ## The capability before the struct, the storage's no-compaction, the completion witness -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The capability before the `raft` struct exists** (`newRaft`'s precondition): at an untraced node,
the nil logger (the old `TraceLoggerOk cv.TraceLogger'` premise); at a traced one, `trCapB`'s body
(`TracedCap.lean`) unbooted, with the logger `tl` (the `Config`'s `TraceLogger`) in place of the struct's
`traceLogger` field, which `newRaft` writes from it. Coupled to `trCapB` (the file header). -/
def trCapStart (tr : Option GName) (γ : RaftNames) (id : w64) (tl : GoInterface) (c : CfgM)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) : IProp GF :=
  match tr with
  | none => iprop(⌜TraceLoggerOk tl⌝)
  | some γd => iprop(∃ (tn : TraceNames) (C : List w64) (cs : ServerC) (P : List Etcdraft.Msg)
      (o : Option TraceEv),
      traceDir γd tn ∗ ⌜tn.voters = C ∧ (elements c.incoming).Perm C ∧ c.outgoing = ∅ ∧ id ∈ C ∧
        C.length ≤ γ.reBoot.length⌝ ∗
      isTraceLogger tn.tr tl ∗ ⌜tl ≠ interface.nil⌝ ∗ inv (simNS γ) (simInv C tn (simFx γ C)) ∗
      raftLogInv γ ∗ simNode tn id cs P ∗ simBoot tn id false o ∗ ⌜Λ o⌝ ∗ ⌜Φ C cs P⌝)

/-- **The storage is never compacted past `1` at a traced node** (persistent; the storage-level form of
`TrNoSnap`, `TracedSend.lean`). Its source is the client's storage contract at a traced cluster
(`isStorage`'s `#Hbound` and the gated `storBnd`, traced `⌜c = 0⌝`: `isStorage_trNoCut`), which exists
only from `InitialState`'s answer on; so the boot bundle's `InitialState` continuation returns it, and
`newRaft`/`NewRawNode` hand it on to `Bootstrap`, which packs `TrNoSnap` at the fresh log
(`trNoCut_trNoSnap`). Untraced it says nothing (`trNoCut_none`). -/
def trNoCut (tr : Option GName) (st : Storage) : IProp GF :=
  iprop(□ (⌜tr ≠ none⌝ -∗ storPast st 1 -∗ |={⊤}=> False))

instance trNoCut_persistent (tr : Option GName) (st : Storage) :
    Persistent (trNoCut (GF := GF) tr st) := by
  unfold trNoCut; infer_instance

/-- **A voter's completion witness at raft's level** (amendment A8.3's `startDoneB` is it at the
cluster's trace mode): nothing untraced; traced, `bootDone` at the trace's names. `Bootstrap` returns it
(minted by `trCapB_bootDone` at its last line, while the capability's `Λ` still records it). -/
def bootDoneG (tr : Option GName) (id : w64) : IProp GF :=
  match tr with
  | none => iprop(True)
  | some γd => iprop(∃ tn : TraceNames, traceDir γd tn ∗ bootDone tn id)

instance bootDoneG_persistent (tr : Option GName) (id : w64) :
    Persistent (bootDoneG (GF := GF) tr id) := by
  unfold bootDoneG; cases tr <;> infer_instance

/-! ## Laws -/

/-- **The capability from its start and the struct's logger field** (`newRaft`, after `r := &raft{…,
traceLogger: c.TraceLogger}`): untraced the nil logger; traced `trCapB_intro`'s argument. -/
theorem trCapStart_trCapB (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (tl : GoInterface)
    (c : CfgM) (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) :
    (r.[raft, go!"traceLogger"] ↦□ tl ∗ trCapStart tr γ id tl c Φ Λ : IProp GF) ⊢
      ⌜tr = none → TraceLoggerOk tl⌝ ∗ trCapB tr γ r id c false Φ Λ := by
  cases tr with
  | none =>
    unfold trCapStart
    iintro ⟨-, %H⟩
    isplitr
    · ipureintro; intro _; exact H
    unfold trCapB; iempintro
  | some γd =>
    iintro ⟨#Htl, H⟩
    iunfold trCapStart at H
    icases H with ⟨%tn, %C, %cs, %P, %o, #Hdir, %Hpf, #Hlg, %Hnn, #Hinv, #Hli, Hnode, Hbt, %HΛ, %HΦ⟩
    isplitr
    · ipureintro; intro h; cases h
    iunfold trCapB
    iexists tn, C, tl, cs, P
    iframe Hdir Htl Hlg Hinv Hli Hnode
    isplitr; · ipureintro; exact Hpf
    isplitr; · ipureintro; exact Hnn
    isplitl [Hbt]
    · iexists o; iframe Hbt; ipureintro; exact HΛ
    ipureintro; exact HΦ

/-- **`TrNoSnap` at a log state of base `0`** over the storage's `trNoCut` (`Bootstrap`'s packing of
`rnTrace`). -/
theorem trNoCut_trNoSnap (tr : Option GName) (ls : LogState) (h0 : uint.Z ls.prev.index' = 0) :
    (trNoCut tr ls.storage : IProp GF) ⊢ TrNoSnap tr ls := by
  iintro #H
  iunfold TrNoSnap
  iintro !> %Htr Hd
  icases Hd with (%Hp | Hp)
  · exact absurd h0 Hp
  · iunfold trNoCut at H
    iapply H $$ %Htr Hp

/-- Untraced, `trNoCut` is free. -/
theorem trNoCut_none (st : Storage) : ⊢ (trNoCut none st : IProp GF) := by
  iunfold trNoCut
  iintro !> %H
  exact absurd rfl H

end defs

end EtcdGrove
end Perennial
