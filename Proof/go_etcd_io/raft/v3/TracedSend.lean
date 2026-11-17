/-
Lean-first (no Rocq counterpart). Q8 stage 1, slice 6 (2026-11-09): the vocabulary of the send
path's specs above `raft.send` that may fall back to a snapshot (`maybeSendAppend`, `sendAppend`,
`bcastAppend` and their callers).

- `TrNoSnap tr ls`: a traced node's log is not compacted, as `maybeSendSnapshot`'s precondition
  states compaction (`⌜prev.index ≠ 0⌝ ∨ storPast storage 1`): the premise excluding, in traced
  mode, the snapshot branch of `maybeSendAppend` (the Draft's P2: a traced node sends no snapshot);
  `True` untraced (`trNoSnap_none`).
- `hookGateOpt_congr`: a hook gate at equal arguments (a gate stated at the loop's entry state used
  at a state that reads as it).
- `HookGateN tr r E n Q`: `traceReplicate`'s gate, the caller's (`appendEntry` takes it), as
  `HookGate` for `n` events in a row (`TraceFireN`); `hookGateN_none`, the untraced caller's.
- `normalCount_mapIdx`: stamping keeps the count of normal entries (the events `traceReplicate` logs).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]

/-- (Q8 stage 1, slice 6) **A traced node's log is not compacted**: compaction as
`raft.maybeSendSnapshot.spec`'s precondition states it (the log's boundary past `0`, or the storage
compacted past `1`) refutes the traced mode. `maybeSendAppend` falls back to `maybeSendSnapshot`
only from such a compaction (`term(pr.Next - 1)` or `entries(pr.Next)` failing with
`ErrCompacted`), so this is the narrowest premise excluding that branch in traced mode; a traced
caller has it from the Draft's P2 (no compaction in a traced cluster). Persistent; untraced it says
nothing (`trNoSnap_none`). (2026-11-12, trace-check implementation step 2, design revision 2's A4) In
its update form (`|={⊤}=> False`): its source at a traced `setupNode` is the client's storage contract
(`isStorage`'s gated bound), read under an update; its two uses (`maybeSendAppend`'s snapshot fallbacks)
are steps of a WP at `⊤`, which eliminate it (`imod`). -/
def TrNoSnap (tr : Option GName) (ls : LogState) : IProp GF :=
  iprop(□ (⌜tr ≠ none⌝ -∗ (⌜uint.Z ls.prev.index' ≠ 0⌝ ∨ storPast ls.storage 1) -∗ |={⊤}=> False))

instance trNoSnap_persistent (tr : Option GName) (ls : LogState) :
    Persistent (TrNoSnap (GF := GF) tr ls) := by
  unfold TrNoSnap; infer_instance

/-- An untraced node's: nothing. -/
theorem trNoSnap_none (ls : LogState) : ⊢ TrNoSnap (GF := GF) none ls := by
  iunfold TrNoSnap
  imodintro
  iintro %h
  exact absurd rfl h

/-- At a traced node, a compaction is a contradiction. -/
theorem trNoSnap_traced (tr : Option GName) (ls : LogState) (h : tr ≠ none) :
    TrNoSnap (GF := GF) tr ls ⊢ (⌜uint.Z ls.prev.index' ≠ 0⌝ ∨ storPast ls.storage 1) -∗ |={⊤}=> False := by
  iintro #H #Hc
  iunfold TrNoSnap at H
  iapply H $$ %h Hc

/-- At equal arguments (a state that reads as `s`). -/
theorem trNoSnap_congr (tr tr' : Option GName) (ls ls' : LogState) (h1 : tr = tr') (h2 : ls = ls') :
    TrNoSnap (GF := GF) tr ls ⊢ TrNoSnap tr' ls' := by
  subst h1 h2; exact .rfl

end defs

section pure
variable [GooseExts]

/-- (slice 17) A `MsgApp` gate's premise (`AppOk`, the commit, the destination, the peer's `Match` at
most the index) with its last conjunct restated: the `Match` read at another state with the same
`Match` values. -/
theorem and4_last {A B C D D' E : Prop} (f : D → D') (h : A ∧ B ∧ C ∧ D ∧ E) : A ∧ B ∧ C ∧ D' ∧ E :=
  ⟨h.1, h.2.1, h.2.2.1, f h.2.2.2.1, h.2.2.2.2⟩

/-- (Q8 stage 1, slice 6) What a `MsgApp`'s gate knows of the message (`raft.maybeSendAppend.spec`)
reads only the protocol state's term, log and commit, which a send and the `Progress` values leave
alone; (slice 17) and the `Match` values, which they leave alone too (`hpm`). -/
theorem appGate_send_prvals (id : w64) (s : NState) (ms : List Msg) (pvs : GMap w64 Progress)
    (to : w64) (mm : Msg) (hpm : prvalsMatch pvs = prvalsMatch s.prvals)
    (h : AppOk id (toPState { sendMsgs s ms with prvals := pvs }) mm ∧
      mm.commit = (toPState { sendMsgs s ms with prvals := pvs }).commit ∧ mm.dst = to ∧
      uint.Z ((prvalsMatch pvs !! to).getD (W64 0)) ≤ uint.Z mm.index ∧ mm.rejecthint = W64 0) :
    AppOk id (toPState s) mm ∧ mm.commit = (toPState s).commit ∧ mm.dst = to ∧
      uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0)) ≤ uint.Z mm.index ∧ mm.rejecthint = W64 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, h2, h3, by rw [← hpm]; exact h4, h5⟩
  unfold AppOk at h1 ⊢
  exact h1

/-- (Q8 stage 1, slice 6) A batch's normal entries, after a map that keeps every entry's type
(`appendEntry`'s stamping, `stamp`). -/
theorem normalCount_mapIdx (ents : List EntryM) (f : Nat → EntryM → EntryM)
    (hf : ∀ i e, (f i e).Type' = e.Type') : normalCount (ents.mapIdx f) = normalCount ents := by
  induction ents generalizing f with
  | nil => rfl
  | cons e es ih =>
    rw [List.mapIdx_cons]
    have h := ih (fun i => f (i + 1)) (fun i => hf (i + 1))
    unfold normalCount at h ⊢
    simp only [List.filter_cons, hf]
    split <;> simp only [List.length_cons, h]

/-- ... `stamp`'s. -/
theorem normalCount_stamp (tm li : w64) (ents : List EntryM) :
    normalCount (ents.mapIdx (stamp tm li)) = normalCount ents :=
  normalCount_mapIdx ents _ (fun _ _ => rfl)

/-- (Q8 stage 1, slice 7) A send's gate reads nothing an earlier send changes (the event's header):
the gate at the state with messages queued is the gate at the state before. -/
theorem sendOutGate_sendMsgs (id : w64) (s : NState) (ms : List Msg) (c : CfgM) (ty : w32)
    (out : List Msg) : sendOutGate id (sendMsgs s ms) c ty out = sendOutGate id s c ty out := rfl

/-- ... and the ghost (the trace mode) is the state's. -/
theorem sendMsgs_gh (s : NState) (ms : List Msg) : (sendMsgs s ms).gh = s.gh := rfl

/-- (2026-11-10, Q8 stage 1 slice 14) **An untraced cluster's resource ignores the outbox**: a family
`G` of caller resources indexed by the outbox (the broadcasts' and the step functions' gates since
slice 14, `notes/decisions.md`, "Q8 stage 1 (slice 14)") gives the same resource at every index when
the cluster is untraced. A traced caller indexes its resources by the outbox (the capability's pending
share is the outbox's traced messages); an untraced one passes a constant family (`IdxFree.const`).
`maybeSendAppend`'s snapshot fallback, reached only untraced (`TrNoSnap`), queues its messages through
no gate and needs it. -/
def IdxFree {α : Type _} (tr : Option GName) (G : List Msg → α) : Prop :=
  tr = none → ∀ o o' : List Msg, G o = G o'

theorem IdxFree.const {α : Type _} (tr : Option GName) (x : α) : IdxFree tr (fun _ : List Msg => x) :=
  fun _ _ _ => rfl

theorem IdxFree.of_some {α : Type _} {tr : Option GName} (G : List Msg → α) (h : tr ≠ none) :
    IdxFree tr G :=
  fun h' => absurd h' h

/-- (2026-11-10, Q8 stage 1 slice 14) **A resource family indexed by the outbox up to order**: raft's
abstract outbox is its queues up to permutation (`outboxRel`, `ownRaftPhysC_outbox`), and `campaign`'s
result names its messages in another order than it sends them (its own vote's response first). A
caller passes a family that ignores the order: untraced a constant one (`PermInv.const`), traced one
whose share is the outbox's traced messages up to order. -/
def PermInv {α : Type _} (G : List Msg → α) : Prop :=
  ∀ o o' : List Msg, o.Perm o' → G o = G o'

theorem PermInv.const {α : Type _} (x : α) : PermInv (fun _ : List Msg => x) :=
  fun _ _ _ => rfl

end pure

section gates
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- (Q8 stage 1, slice 6) **`traceReplicate`'s gate, the caller's** (`appendEntry` takes it): as
`HookGate` (an update at `⊤`, run at the hook, giving the logger field), for the `n` events in a row
the hook logs (`TraceFireN`, one per normal entry of the batch). -/
def HookGateN (tr : Option GName) (r : Loc) (E : TraceEv → Prop) (n : Nat) (Q : IProp GF) : IProp GF :=
  iprop(|={⊤}=> ∃ tl, r.[raft, go!"traceLogger"] ↦□ tl ∗ TraceFireN tr tl E n Q)

/-- An untraced caller's gate: the struct's nil logger and `Q`. -/
theorem hookGateN_none (r : Loc) (E : TraceEv → Prop) (n : Nat) (tl : GoInterface) (Q : IProp GF)
    (hok : TraceLoggerOk tl) :
    (r.[raft, go!"traceLogger"] ↦□ tl ∗ Q : IProp GF) ⊢ HookGateN none r E n Q := by
  iintro ⟨#Htl, HQ⟩
  iunfold HookGateN
  imodintro
  iexists tl
  iframe Htl
  iapply traceFireN_of_none rfl tl E hok Q n $$ HQ

/-- A hook gate at equal arguments (a gate at a state that reads as `s`). -/
theorem hookGateOpt_congr (tr tr' : Option GName) (r : Loc) (oE oE' : Option (TraceEv → Prop))
    (Q : IProp GF) (h1 : tr = tr') (h2 : oE = oE') :
    HookGateOpt tr r oE Q ⊢ HookGateOpt tr' r oE' Q := by
  subst h1 h2; exact .rfl

end gates

section idx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]

/-- (2026-11-10, Q8 stage 1 slice 14) A resource indexed by the outbox up to order (`PermInv`), at a
permuted outbox. -/
theorem idx_perm (G : List Msg → IProp GF) (hG : PermInv G) {o o' : List Msg} (h : o.Perm o') :
    G o ⊢ G o' := by
  rw [hG o o' h]

/-- (2026-11-10, Q8 stage 1 slice 14) Raft's struct and a resource indexed by its outbox, at an equal
state (`ownRaftPhysC_eq` for both). -/
theorem physG_eq (c : CfgM) (r : Loc) (id : w64) (G : List Msg → IProp GF) {s1 s2 : NState}
    (h : s1 = s2) :
    ownRaftPhysCV (GF := GF) c c.voters r id s1 ∗ G s1.outbox ⊢
      ownRaftPhysCV c c.voters r id s2 ∗ G s2.outbox := by
  subst h; exact .rfl

end idx

end EtcdGrove
end Perennial
