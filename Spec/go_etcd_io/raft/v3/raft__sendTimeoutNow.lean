/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `sendTimeoutNow(to)`: `send` of `MsgTimeoutNow{To: to}`, a type the model does not
describe (`mtypeOf` is `none`): it carries no protocol fact and drops out of the abstract
outbox, so the state is unchanged. `to` is another node (`send` panics on a message to
oneself): the leader-transfer target, which `ownRaftPhys` keeps `≠ id`. (raft-final, 2026-10-29,
U9: in every cluster; from 2026-10-19, D21 M2r, until then only with leader transfer on,
`NGhost.xf`.) -/
abbrev raft.sendTimeoutNow.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (to : w64),
  to ≠ id →
  -- (2026-10-29, stage U7) the term past `0` that `send` stamps (`SentMsgShape`)
  s.term ≠ W64 0 →
  -- (2026-11-09, Q8 stage 0 of `notes/trace-validation-plan.md`) an untraced node: its trace
  -- hooks see a nil logger (`TraceLoggerOkS`); stage 1 replaces this premise by the traced
  -- capability (`trCapB s.gh.tr …`, `TracedHooksDraft.lean`)
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendTimeoutNow")) (Val #to))
  {{ RET #(); ownRaftPhysCV c c.voters r id s }}

end spec

end EtcdGrove
end Perennial
