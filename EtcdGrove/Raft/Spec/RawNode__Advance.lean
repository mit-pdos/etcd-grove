/-
Port of `election_proof/spec_RawNode__Advance.v` (857d09190).

Lean notes: As for `raft.Step.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]`. `pstep_commit_mono`, `apply_ack_ok`, `advance_ok` are `PstepCommitMono`,
`ApplyAckOk`, `AdvanceOk`; Rocq's `Forall P l` is `∀ p ∈ l, P p` and stdpp's
`list.last` is `List.getLast?`.
-/
import EtcdGrove.Raft.Spec.raft__Step
import EtcdGrove.Raft.InvRawnode

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The protocol's commit index never moves back across a `Step`: a fact about the
protocol's relation (`Protocol/Model.lean`), stated here as a premise of `Advance`
rather than proved (another agent is reworking the protocol's commit ghost state; every
rule either keeps `commit` or raises it). -/
def PstepCommitMono [FfiSyntax] (cfg : GSet w64) (id : w64) : Prop :=
  ∀ ps recv ps', Step cfg id ps recv ps' → uint.Z ps.commit ≤ uint.Z ps'.commit

/-- What `Advance` needs of the local messages it steps, at the state `s` it is called
in.

- **No self-addressed responses** (`Pending.self`). They are stepped first (they come
  from `msgsAfterAppend`) and `Step`'s spec asks of each message facts `ownRaftPhys`
  does not record for the queue -- its `Entries`' capacity, `Term ≠ 0`, a
  non-rejecting self `MsgAppResp` -- and, for a `MsgPreVoteResp`, a term bound at the
  state the earlier steps left, which `Step`'s postcondition does not describe beyond
  `NStateRel`. A candidate's own vote and a leader's own `MsgAppResp` are such
  messages, so this restricts `Advance` to Readys that queued none (see
  notes/raft-replication-model.md, "Phase 4", for the fix).
- The `MsgStorageAppendResp`, if any, comes first (as `acceptReady` queues it), is not
  from a later term, and if its `stableTo` runs it acknowledges persisted entries
  (`StableOk`) -- true right after `Ready` and the application's append
  (`ready_stable_ok`, `inv_rawnode.v`); a `Step` in between may truncate the log, and
  then it is the protocol's Log Matching that makes it true, not stated here.
- The `MsgStorageApplyResp`'s entries end at or below `committed`. -/
def ApplyAckOk [FfiSyntax] (s : NState) (p : Pending) : Prop :=
  match p with
  | .applyAck ce => ∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z s.logst.committed
  | _ => False

def AdvanceOk [FfiSyntax] (s : NState) (steps : List Pending) : Prop :=
  match steps with
  | .appendAck t e :: rest =>
      (uint.Z t ≤ uint.Z s.term ∧
       (t = W64 0 ∨ t = s.term → e.index' ≠ W64 0 → StableOk s.logst e)) ∧
      ∀ p ∈ rest, ApplyAckOk s p
  | _ => ∀ p ∈ steps, ApplyAckOk s p

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- `rn.Advance(rd)` (`rawnode.go:482`):

    if rn.asyncStorageWrites { Panicf(...) }
    for i, m := range rn.stepsOnAdvance {
        _ = rn.raft.Step(m)
        rn.stepsOnAdvance[i] = pb.Message{}
    }
    rn.stepsOnAdvance = rn.stepsOnAdvance[:0]

Steps the queued local messages through `Step` -- whose spec this proof uses, so the
ghost state moves by `Step`'s protocol steps -- and empties the queue. Like `Step` it is
a top-level entry point and mentions `ownRaftGhost`. The `Ready` argument is unused. -/
abbrev RawNode.Advance.spec : Prop :=
  ∀ (cfg : GSet w64) (γ : RaftNames) (rn : Loc) (id : w64)
    (s : NState) (ps : PState) (rs : RNState) (rd : Ready),
  γ.reCfg = cfg →
  id ∈ cfg →
  NStateRel s ps →
  PstepCommitMono cfg id →
  AdvanceOk s rs.steps →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hrn" ∷ ownRawNode cfg rn id s rs ∗
      "Hghost" ∷ ownRaftGhost γ id ps }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Advance")) (Val #rd))
  {{ (s' : NState) (ps' : PState), RET #();
      ownRawNode cfg rn id s' { rs with steps := [] } ∗
      ownRaftGhost γ id ps' ∗
      ⌜NStateRel s' ps' ∧ ∃ recv, Step cfg id ps recv ps'⌝ }}

end spec

end EtcdGrove
end Perennial
