/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.TracedMsg

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
`NGhost.xf`.)

**One spec for both trace modes** (2026-11-09, trace-check Q8 stage 1 slice 5): `send`'s hook logs
nothing for `MsgTimeoutNow` (not a traced type, `sendGate`), so the caller's gate is `send`'s at no
event (`HookGateOpt s.gh.tr r none Q`: the logger field, nil when untraced), and `Q` comes back. Until
slice 5 the premise `s.gh.tr = none` (stage 0), now `raft.sendTimeoutNow.untraced`'s
(`TracedUntraced.lean`). -/
abbrev raft.sendTimeoutNow.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (to : w64) (Q : IProp GF),
  to ≠ id →
  -- (2026-10-29, stage U7) the term past `0` that `send` stamps (`SentMsgShape`)
  s.term ≠ W64 0 →
  -- (2026-11-12, trace-check implementation step 3, the design's §3.6 physical half) not at a traced
  -- node: `MsgTimeoutNow` has no abstraction, and `raft.send.spec` takes none there (a traced node
  -- steps no transfer, `raft.Step.spec`'s premises)
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
      -- (2026-11-09, Q8 stage 1 slice 5) `send`'s hook's gate, at no event
      HookGateOpt s.gh.tr r none Q }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendTimeoutNow")) (Val #to))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

end spec

end EtcdGrove
end Perennial
