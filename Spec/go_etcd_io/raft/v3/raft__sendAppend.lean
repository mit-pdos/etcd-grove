/-
Port of election_proof/spec_raft__sendAppend.v (feb5c73d4).

Lean notes:
* Rocq's `send_msgs s ms <| nstate.prvals := pvs |>` is
  `{ sendMsgs s ms with prvals := pvs }`, and the type of the untyped binder `pvs` is
  written out.
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

/-- `r.sendAppend(to)` is `r.maybeSendAppend(to, true)` and nothing else
(`raft.sendAppend.impl`, `Code/go_etcd_io/raft/v3.lean`) -- the boolean
result is dropped. Same postcondition, therefore: the outbox grows by some list of
messages `ReplOk` allows, and `Match` does not move.

**One spec for both trace modes** (2026-11-09, trace-check Q8 stage 1 slice 6): `maybeSendAppend`'s
gate (`raft.maybeSendAppend.spec`): the `MsgApp`'s hook gate from the caller's `G` back to `G`, and
`TrNoSnap`. Until slice 6 the premise `s.gh.tr = none` (stage 0), now `raft.sendAppend.untraced`'s
(`TracedUntracedSend.lean`). -/
abbrev raft.sendAppend.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (to : w64) (G : List Msg → IProp GF),
  to ≠ id →
  to ∈ domSet s.progress →
  -- (2026-10-16, stage R8a) a leader's, as `maybeSendAppend`
  s.role = .leader →
  -- (2026-10-29, stage U7) the term past `0` that `send` stamps (`SentMsgShape`)
  s.term ≠ W64 0 →
  -- (2026-11-10, slice 14) the caller's resource indexed by the outbox (`maybeSendAppend`'s)
  IdxFree s.gh.tr G →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      -- (2026-11-09, Q8 stage 1 slice 6; until then, stage 0, the premise `s.gh.tr = none`)
      -- `maybeSendAppend`'s gate and its no-compaction premise
      -- (2026-11-10, slice 17) with `Match ≤ mm.index`
      "Hgate" ∷ (∀ (mm : Msg) (o : List Msg), ⌜AppOk id (toPState s) mm ∧ mm.commit = (toPState s).commit ∧
          mm.dst = to ∧ uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0)) ≤ uint.Z mm.index⌝ -∗ G o -∗
        HookGateOpt s.gh.tr r (sendOutGate id s c MsgApp [mm]) (G (o ++ [mm]))) ∗
      "HG" ∷ G s.outbox ∗
      "#Hnosnap" ∷ TrNoSnap s.gh.tr s.logst }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendAppend")) (Val #to))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜ReplSends id s ms⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ ∗
      G ({ sendMsgs s ms with prvals := pvs } : NState).outbox }}

end spec

end EtcdGrove
end Perennial
