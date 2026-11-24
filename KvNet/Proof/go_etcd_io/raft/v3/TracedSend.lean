-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/TracedSend.lean` (etc/copy-part.py; rerun it, do not edit).
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
- (2026-11-24, #33 S4 P-raft-1b; `notes/antithesis-rawnode-design.md` §2.5, option (b)) **the
  no-snapshot flag `nc`**: `NoSnapG nc tr ls` (`TrNoSnap tr ls` at `nc = false`; at `nc = true` the
  log not compacted whatever the trace mode) and `IdxFreeN nc tr G` (`IdxFree tr G` at `nc = false`;
  at `nc = true` the family kept by queueing messages other than snapshots). The send path's specs
  take them at an implicit `nc`, which a caller's `IdxFree` premise fixes at `false`; an untraced
  caller that knows its log uncompacted (the harness's `RawNode`, `RnScope`) passes `nc = true` and a
  family recording that its outbox holds no `MsgSnap`.
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.TracedMsg

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

/-- (2026-11-24, #33 S4 P-raft-1b) **The no-snapshot premise at the flag `nc`**: at `nc = false`
`TrNoSnap` (a traced node's log not compacted), at `nc = true` the log not compacted whatever the
trace mode (`maybeSendAppend`'s snapshot fallback then unreachable untraced too). Reducible, so that
at a literal `false` it is `TrNoSnap` for the proof mode's matching. -/
@[reducible] def NoSnapG : Bool → Option GName → LogState → IProp GF
  | false, tr, ls => TrNoSnap tr ls
  | true, _, ls => iprop(□ ((⌜uint.Z ls.prev.index' ≠ 0⌝ ∨ storPast ls.storage 1) -∗ |={⊤}=> False))

instance noSnapG_persistent (nc : Bool) (tr : Option GName) (ls : LogState) :
    Persistent (NoSnapG (GF := GF) nc tr ls) := by
  cases nc <;> unfold NoSnapG <;> infer_instance

/-- At a traced node or under the flag, a compaction is a contradiction. -/
theorem noSnapG_cut (nc : Bool) (tr : Option GName) (ls : LogState) (h : tr ≠ none ∨ nc = true) :
    NoSnapG (GF := GF) nc tr ls ⊢ (⌜uint.Z ls.prev.index' ≠ 0⌝ ∨ storPast ls.storage 1) -∗ |={⊤}=> False := by
  cases nc with
  | false =>
    have h' : tr ≠ none := h.resolve_right (by decide)
    iintro #H #Hc
    try iunfold NoSnapG at H
    iunfold TrNoSnap at H
    iapply H $$ %h' Hc
  | true =>
    iintro #H #Hc
    try iunfold NoSnapG at H
    iapply H $$ Hc

/-- Off the untraced `nc = false` case, the premise refutes a compaction. -/
theorem noSnapG_guard {nc : Bool} {tr : Option GName} (h : ¬ (tr = none ∧ nc = false)) :
    tr ≠ none ∨ nc = true := by
  cases nc
  · exact Or.inl (fun h' => h ⟨h', rfl⟩)
  · exact Or.inr rfl

/-- At equal arguments (a state that reads as `s`). -/
theorem noSnapG_congr (nc : Bool) (tr tr' : Option GName) (ls ls' : LogState) (h1 : tr = tr') (h2 : ls = ls') :
    NoSnapG (GF := GF) nc tr ls ⊢ NoSnapG nc tr' ls' := by
  subst h1 h2; exact .rfl

/-- `NoSnapG` reads the log's boundary and storage only: at two logs agreeing there. -/
theorem noSnapG_logst (nc : Bool) (tr tr' : Option GName) (ls ls' : LogState) (h1 : tr = tr')
    (hp : ls.prev = ls'.prev) (hs : ls.storage = ls'.storage) :
    NoSnapG (GF := GF) nc tr ls ⊢ NoSnapG nc tr' ls' := by
  subst h1; cases nc <;> dsimp only [NoSnapG, TrNoSnap] <;> rw [hp, hs]

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

/-- (2026-11-24, #33 S4 P-raft-1b) **No snapshot among the messages** `o`. -/
def NoSnapL (o : List Msg) : Prop := ∀ x ∈ o, x.ty ≠ .snap

theorem NoSnapL.nil : NoSnapL [] := fun _ h => absurd h List.not_mem_nil

theorem NoSnapL.append {o o' : List Msg} (h : NoSnapL o) (h' : NoSnapL o') : NoSnapL (o ++ o') :=
  fun x hx => (List.mem_append.mp hx).elim (h x) (h' x)

theorem NoSnapL.snoc {o : List Msg} {m : Msg} (h : NoSnapL o) (hm : m.ty ≠ .snap) : NoSnapL (o ++ [m]) :=
  h.append (fun x hx => by rw [List.mem_singleton.mp hx]; exact hm)

theorem NoSnapL.single {m : Msg} (hm : m.ty ≠ .snap) : NoSnapL [m] :=
  fun x hx => by rw [List.mem_singleton.mp hx]; exact hm

/-- (2026-11-10, Q8 stage 1 slice 14) A resource family indexed by the outbox up to order: raft's
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
  iprop(notCrashed -∗ |={⊤}=> notCrashed ∗ ∃ tl, r.[raft, go!"traceLogger"] ↦□ tl ∗ TraceFireN tr tl E n Q)

/-- An untraced caller's gate: the struct's nil logger and `Q`. -/
theorem hookGateN_none (r : Loc) (E : TraceEv → Prop) (n : Nat) (tl : GoInterface) (Q : IProp GF)
    (hok : TraceLoggerOk tl) :
    (r.[raft, go!"traceLogger"] ↦□ tl ∗ Q : IProp GF) ⊢ HookGateN none r E n Q := by
  iintro ⟨#Htl, HQ⟩
  iunfold HookGateN
  iintro Hnc
  imodintro
  iframe Hnc
  iexists tl
  iframe Htl
  iapply traceFireN_of_none rfl tl E hok Q n $$ HQ

/-- A hook gate at equal arguments (a gate at a state that reads as `s`). -/
theorem hookGateOpt_congr (tr tr' : Option GName) (r : Loc) (oE oE' : Option (TraceEv → Prop))
    (Q : IProp GF) (h1 : tr = tr') (h2 : oE = oE') :
    HookGateOpt tr r oE Q ⊢ HookGateOpt tr' r oE' Q := by
  subst h1 h2; exact .rfl

end gates

section idxfree
variable [GooseExts] {GF : BundledGFunctors}

/-- (2026-11-24, #33 S4 P-raft-1b) **The callees' demand on an outbox-indexed family, at the flag
`nc`** (`IdxFree` at `nc = false`): untraced, at `nc = false` the family ignores the outbox
(`maybeSendAppend`'s snapshot fallback queues through no gate); at `nc = true` (the fallback refuted
by `NoSnapG true`) it is kept by queueing messages other than snapshots (a received `MsgSnap`'s
answer, `handleSnapshot`'s, queued through no gate). Traced, nothing. -/
def IdxFreeN (nc : Bool) (tr : Option GName) (G : List Msg → IProp GF) : Prop :=
  tr = none → (nc = false → ∀ o o' : List Msg, G o = G o') ∧
    (nc = true → ∀ o ms : List Msg, NoSnapL ms → (G o ⊢ G (o ++ ms)))

/-- (2026-11-10, Q8 stage 1 slice 14) **An untraced cluster's resource ignores the outbox**: a family
`G` of caller resources indexed by the outbox (the broadcasts' and the step functions' gates since
slice 14, `notes/decisions.md`, "Q8 stage 1 (slice 14)") gives the same resource at every index when
the cluster is untraced. A traced caller indexes its resources by the outbox (the capability's pending
share is the outbox's traced messages); an untraced one passes a constant family (`IdxFree.const`).
`maybeSendAppend`'s snapshot fallback, reached only untraced (`TrNoSnap`), queues its messages through
no gate and needs it. (2026-11-24, P-raft-1b) `IdxFreeN` at `nc = false`, an abbreviation, so that a
caller's `IdxFree` fixes a spec's implicit `nc` at `false`. -/
abbrev IdxFree (tr : Option GName) (G : List Msg → IProp GF) : Prop := IdxFreeN false tr G

theorem IdxFree.const (tr : Option GName) (x : IProp GF) : IdxFree tr (fun _ : List Msg => x) :=
  fun _ => ⟨fun _ _ _ => rfl, fun h => absurd h (by decide)⟩

theorem IdxFree.of_some {tr : Option GName} (G : List Msg → IProp GF) (h : tr ≠ none) :
    IdxFree tr G :=
  fun h' => absurd h' h

theorem IdxFreeN.const (nc : Bool) (tr : Option GName) (x : IProp GF) :
    IdxFreeN nc tr (fun _ : List Msg => x) :=
  fun _ => ⟨fun _ _ _ => rfl, fun _ _ _ _ => .rfl⟩

theorem IdxFreeN.of_some (nc : Bool) {tr : Option GName} (G : List Msg → IProp GF) (h : tr ≠ none) :
    IdxFreeN nc tr G :=
  fun h' => absurd h' h

/-- At `nc = false` untraced, the family ignores the outbox. -/
theorem IdxFreeN.eq {nc : Bool} {tr : Option GName} {G : List Msg → IProp GF} (H : IdxFreeN nc tr G)
    (htr : tr = none) (hnc : nc = false) (o o' : List Msg) : G o = G o' :=
  (H htr).1 hnc o o'

/-- **What a send through no gate keeps of the family**: untraced, the family at the outbox `o`
gives it at `o ++ ms`, for messages `ms` that are not snapshots (any, at `nc = false`). -/
theorem IdxFreeN.step {nc : Bool} {tr : Option GName} {G : List Msg → IProp GF} (H : IdxFreeN nc tr G)
    (htr : tr = none) (o ms : List Msg) (hms : nc = true → NoSnapL ms) : G o ⊢ G (o ++ ms) := by
  cases nc with
  | false => rw [(H htr).1 rfl (o ++ ms) o]
  | true => exact (H htr).2 rfl o ms (hms rfl)

/-- ... at an outbox named `o'`. -/
theorem IdxFreeN.step' {nc : Bool} {tr : Option GName} {G : List Msg → IProp GF} (H : IdxFreeN nc tr G)
    (htr : tr = none) {o o' : List Msg} (ms : List Msg) (ho : o' = o ++ ms) (hms : nc = true → NoSnapL ms) :
    G o ⊢ G o' := by
  rw [ho]; exact H.step htr o ms hms

end idxfree

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
