/-
Port of election_proof/spec_raft__sendAppend.v (feb5c73d4).

Lean notes:
* Rocq's `send_msgs s ms <| nstate.prvals := pvs |>` is
  `{ sendMsgs s ms with prvals := pvs }`, and the type of the untyped binder `pvs` is
  written out.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftPhys

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
messages `ReplOk` allows, and `Match` does not move. -/
abbrev raft.sendAppend.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (to : w64),
  to ≠ id →
  to ∈ domSet s.progress →
  -- (2026-10-16, stage R8a) a leader's, as `maybeSendAppend`
  s.role = .leader →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendAppend")) (Val #to))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜ReplSends id s ms⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

end spec

end EtcdGrove
end Perennial
