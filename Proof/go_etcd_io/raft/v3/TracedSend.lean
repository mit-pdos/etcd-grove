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
nothing (`trNoSnap_none`). -/
def TrNoSnap (tr : Option GName) (ls : LogState) : IProp GF :=
  iprop(□ (⌜tr ≠ none⌝ -∗ (⌜uint.Z ls.prev.index' ≠ 0⌝ ∨ storPast ls.storage 1) -∗ False))

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
    TrNoSnap (GF := GF) tr ls ⊢ (⌜uint.Z ls.prev.index' ≠ 0⌝ ∨ storPast ls.storage 1) -∗ False := by
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

/-- (Q8 stage 1, slice 6) What a `MsgApp`'s gate knows of the message (`raft.maybeSendAppend.spec`)
reads only the protocol state's term, log and commit, which a send and the `Progress` values leave
alone. -/
theorem appGate_send_prvals (id : w64) (s : NState) (ms : List Msg) (pvs : GMap w64 Progress)
    (to : w64) (mm : Msg)
    (h : AppOk id (toPState { sendMsgs s ms with prvals := pvs }) mm ∧
      mm.commit = (toPState { sendMsgs s ms with prvals := pvs }).commit ∧ mm.dst = to) :
    AppOk id (toPState s) mm ∧ mm.commit = (toPState s).commit ∧ mm.dst = to := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, h3⟩
  unfold AppOk at h1 ⊢
  exact h1

end pure

section gates
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A hook gate at equal arguments (a gate at a state that reads as `s`). -/
theorem hookGateOpt_congr (tr tr' : Option GName) (r : Loc) (oE oE' : Option (TraceEv → Prop))
    (Q : IProp GF) (h1 : tr = tr') (h2 : oE = oE') :
    HookGateOpt tr r oE Q ⊢ HookGateOpt tr' r oE' Q := by
  subst h1 h2; exact .rfl

end gates

end EtcdGrove
end Perennial
