/-
Lean-first (no Rocq counterpart). The intermediate states `stepLeader`'s gates are stated at
(2026-11-10, trace-check Q8 stage 1 slice 9, `notes/decisions.md`, "Q8 stage 1 (slice 9)"): the
spec (`Spec/go_etcd_io/raft/v3/stepLeader.lean`) names them, and a spec file defines nothing but its
spec (CLAUDE.md, "Package APIs", `--layout`).

Each is a state whose trace-event header (`EvHdrOf`: term, vote, commit, role, last index) and log
are the ones the hook reads there; the fields a hook does not read (`Progress` values, the outbox,
the read-only state, `pendingConfIndex`, the transferee) are the caller's state's, so a callee's
gate at the state it is called in is the spec's gate by `rfl` (`sendOutGate`, `NodeEvOf` and
`AppOk` read none of them).
-/
module

public import Proof.go_etcd_io.raft.v3.Defs
public import Proof.go_etcd_io.raft.v3.TracedSend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section helpers
variable [GooseExts]

/-- `MsgProp`: the state with the batch `ents` appended, stamped with the term and the indices
after the last (`appendEntry`'s, before its self-acknowledgement is queued). -/
def propAppended (s : NState) (ents : List EntryM) : NState :=
  { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }

/-- `MsgAppResp` accepted from `src` at `index`: the `Match` map after `MaybeUpdate` (the sender's
raised to `index` if below it; unchanged if the sender has no `Progress`, where no gate runs). -/
def appRespMatch (s : NState) (src index : w64) : GMap w64 w64 :=
  match prvalsMatch s.prvals !! src with
  | some x => <[src := if uint.Z x < uint.Z index then index else x]> (prvalsMatch s.prvals)
  | none => prvalsMatch s.prvals

theorem appRespMatch_of_some (s : NState) (src index x : w64)
    (h : prvalsMatch s.prvals !! src = some x) :
    appRespMatch s src index =
      <[src := if uint.Z x < uint.Z index then index else x]> (prvalsMatch s.prvals) := by
  unfold appRespMatch; rw [h]

/-- `MsgAppResp` accepted: the state after `maybeCommit`'s outcome `(b, N)` (the commit index moved
to `N` when it commits). -/
def commitAt (s : NState) (b : Bool) (N : w64) : NState :=
  if b then { s with logst := { s.logst with committed := N } } else s

theorem commitAt_true (s : NState) (N : w64) :
    commitAt s true N = { s with logst := { s.logst with committed := N } } := rfl

theorem commitAt_false (s : NState) (N : w64) : commitAt s false N = s := rfl

theorem commitAt_gh (s : NState) (b : Bool) (N : w64) : (commitAt s b N).gh = s.gh := by
  cases b <;> rfl

theorem commitAt_logst (s : NState) (b : Bool) (N : w64) :
    (commitAt s b N).logst = { s.logst with committed := (commitAt s b N).logst.committed } := by
  cases b <;> rfl

/-- A send's gate reads the event's header only (term, vote, log, role): at two states agreeing
there, the same. -/
theorem sendOutGate_hdr (id : w64) (X Y : NState) (c : CfgM) (ty : w32) (out : List Msg)
    (h1 : X.term = Y.term) (h2 : X.vote = Y.vote) (h3 : X.logst = Y.logst) (h4 : X.role = Y.role) :
    sendOutGate id X c ty out = sendOutGate id Y c ty out := by
  simp only [sendOutGate, SendEvOf, plastIndex, toPState, h1, h2, h3, h4]

/-- What a `MsgApp`'s gate knows of the message reads the term and the log only. -/
theorem appOk_hdr (id : w64) (X Y : NState) (mm : Msg) (h1 : X.term = Y.term)
    (h3 : X.logst = Y.logst) :
    AppOk id (toPState X) mm ↔ AppOk id (toPState Y) mm := by
  simp only [AppOk, toPState, h1, h3]

end helpers

section gates
open Iris Iris.BI
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]

/-- A node event's hook gate at equal arguments (a gate at a state that reads as another). -/
theorem hookGate_congr (tr tr' : Option GName) (r : Loc) (E E' : TraceEv → Prop) (Q : IProp GF)
    (h1 : tr = tr') (h2 : E = E') : HookGate tr r E Q ⊢ HookGate tr' r E' Q := by
  subst h1 h2; exact .rfl

/-- `traceReplicate`'s hook gate at equal arguments. -/
theorem hookGateN_congr (tr tr' : Option GName) (r : Loc) (E E' : TraceEv → Prop) (n : Nat)
    (Q : IProp GF) (h1 : tr = tr') (h2 : E = E') : HookGateN tr r E n Q ⊢ HookGateN tr' r E' n Q := by
  subst h1 h2; exact .rfl

/-- `TrNoSnap` reads the log's boundary and storage only: at two logs agreeing there (the commit
index moved), the same. -/
theorem trNoSnap_logst (tr tr' : Option GName) (ls ls' : LogState) (h1 : tr = tr')
    (hp : ls.prev = ls'.prev) (hs : ls.storage = ls'.storage) :
    TrNoSnap (GF := GF) tr ls ⊢ TrNoSnap tr' ls' := by
  subst h1; unfold TrNoSnap; rw [hp, hs]

end gates

end EtcdGrove
end Perennial
