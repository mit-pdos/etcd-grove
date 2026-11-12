/-
Lean-first (no Rocq counterpart): `traceEvent` (`state_trace.go`, translated under the `goose`
tag since 2026-11-08, `notes/trace-validation-hooks.md`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedMsg
public import Proof.go_etcd_io.raft.v3.RaftReadLend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `traceEvent(evt, r, m, prop)`: reads `r.traceLogger` and returns when it is nil; otherwise
builds the event from `r`'s state, the message `m` and the properties `prop`, and calls the logger's
`TraceEvent`.

One spec for both modes (Q8 stage 1, slice 2, 2026-11-09), by the caller's mode `tr`: the logger's
gate `TraceFire tr tl E Q` (untraced: a nil logger and `Q`, `TraceLoggerOk`; traced: the logger's
contract and the update for any event `E` allows, giving `Q`), and under the gate `trOwn tr` what
only the traced branch reads, lent by the caller out of a resource `P` (given back as `R`): raft's
state at some configuration (`RaftLend`), read first, then the message (`MsgLend`: nil, or a message
holding some `ms`), read last (`makeTracingMessage`), and the properties (`tracingPropsRep prop e0`,
read-only: the event's are `e0`'s). Every event of them the builder may log is allowed by `E`: the
header (`EvHdrOf`: the state's term, vote, commit, role, last index, each configuration half's voters
in some order), the message's `traceMsgOf` (`msgArgTrace`), no configuration change, `e0`'s properties.

(Slice 2: the node events only, raft's state lent alone, `m` and `prop` nil. Slice 4: the message and
the properties, and the lending form, so that a caller may hold the message inside `P`, as
`traceSendMessage`'s and `traceReceiveMessage`'s do. Until slice 2 the spec was the untraced case
alone, `⌜TraceLoggerOk tl⌝`, giving `True`.) (2026-11-12, trace-check step 4: raft's state lent
read-only, `RaftReadLend`, what the builder reads -- the header's fields, the log, the `trk` field and
its configuration's maps, never a `Progress` -- so that `switchToConfig`'s hook, whose struct is open at
its tracker, can lend it; a whole struct's lending gives it, `raftReadLend_of_lend`.) -/
abbrev traceEvent.spec : Prop :=
  ∀ (evt : w64) (r m : Loc) (prop : GoMap) (tl : GoInterface) (tr : Option GName)
    (E : TraceEv → Prop) (Q R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      trOwn tr iprop(∃ (c : CfgM) (id : w64) (s : NState) (P : IProp GF) (om : Option MsgArg)
          (e0 : TraceEv),
        P ∗ RaftReadLend P c r id s ∗ MsgLend P m om ∗ tracingPropsRep prop e0 ∗
        ⌜uint.nat evt < evtNames.length ∧
          ∀ e, EvHdrOf evt id s c e → e.msg = msgArgTrace om → e.cc = none →
            e.propCC = e0.propCC → e.propMatch = e0.propMatch → e.propNext = e0.propNext → E e⌝ ∗
        (P -∗ R)) ∗
      TraceFire tr tl E Q }}
    (App (App (App (App (Val #(functions traceEvent [])) (Val #evt)) (Val #r)) (Val #m)) (Val #prop))
  {{ RET #(); trOwn tr R ∗ Q }}

end spec

end EtcdGrove
end Perennial
