/- Port of election_proof/spec_raft__bcastAppend.v (feb5c73d4).

Lean notes: Rocq's untyped binders `id s` and `pvs` get their types written
out; `send_msgs s ms <| nstate.prvals := pvs |>` is `{ sendMsgs s ms with prvals := pvs }`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.TracedSend

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

/-- The broadcast a new leader sends. `bcastAppend` visits every peer's `Progress` and
calls `sendAppend`, which reaches `maybeSendAppend` -- and that sends a `MsgApp` only
when the log and the peer's `Progress` permit it, otherwise a `MsgSnap` or nothing at
all (the peer is paused, or there is nothing to send and `sendIfEmpty` is false).

So this says **not** one `MsgApp` per peer, only that the outbox grew by some list of
messages `ReplOk` allows (`ReplSends`, `Defs.lean`) -- which is exactly what `step_win`
and `step_send_apps` ask for -- and that no `Match` moved. An earlier version of the
model demanded one per peer, which would have made this claim false -- the same trap
`raft.appendEntry.spec` fell into before 2026-09-15 (it was called
`wp_raft__appendEmptyEntry` then, after a Go method that does not exist).

**One spec for both trace modes** (2026-11-09, trace-check Q8 stage 1 slice 6): a loop of sends, as
`raft.bcastHeartbeatWithCtx.spec`'s: a persistent per-message gate (each `MsgApp` to a peer `to`, with
what `maybeSendAppend` knows of it, at `s`: the event's header reads nothing a send changes) taking
the caller's `G` back to `G`, threaded through the `Visit`; and `TrNoSnap` (a traced node's log is
not compacted, so no peer gets a snapshot). Until slice 6 the premise `s.gh.tr = none` (stage 0), now
`raft.bcastAppend.untraced`'s (`TracedUntracedSend.lean`). -/
abbrev raft.bcastAppend.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (G : List Msg → IProp GF),
  -- (2026-10-16, stage R8a) a leader's, as `maybeSendAppend`
  s.role = .leader →
  -- (2026-10-29, stage U7) the term past `0` that `send` stamps (`SentMsgShape`)
  s.term ≠ W64 0 →
  -- (2026-11-10, slice 14) the caller's resource indexed by the outbox (`maybeSendAppend`'s)
  IdxFree s.gh.tr G →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      -- (2026-11-09, Q8 stage 1 slice 6; until then, stage 0, the premise `s.gh.tr = none`) the
      -- `MsgApp`s' hook gates, one per message (to a peer `to`, as `raft.maybeSendAppend.spec`'s),
      -- each taking the caller's `G` back to `G`, at `s`
      -- (2026-11-10, slice 14) `G` indexed by the outbox, as `raft.maybeSendAppend.spec`'s
      -- (2026-11-10, slice 17) with `Match ≤ mm.index`, as `raft.maybeSendAppend.spec`'s
      "#Hgate" ∷ □ (∀ (to : w64) (mm : Msg) (o : List Msg), ⌜to ≠ id ∧ to ∈ domSet s.progress⌝ -∗
          ⌜AppOk id (toPState s) mm ∧ mm.commit = (toPState s).commit ∧ mm.dst = to ∧
            uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0)) ≤ uint.Z mm.index ∧ mm.rejecthint = W64 0⌝ -∗ G o -∗
        HookGateOpt s.gh.tr r (sendOutGate id s c MsgApp [mm]) (G (o ++ [mm]))) ∗
      "HG" ∷ G s.outbox ∗
      "#Hnosnap" ∷ TrNoSnap s.gh.tr s.logst }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"bcastAppend")) (Val #()))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜ReplSends id s ms⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ ∗
      G ({ sendMsgs s ms with prvals := pvs } : NState).outbox }}

end spec

end EtcdGrove
end Perennial
