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
oneself): the leader-transfer target, which `ownRaftPhys` keeps `≠ id`. (2026-10-19, D21 M2r)
Only with leader transfer on (`NGhost.xf`, `send`'s `SendOk`). -/
abbrev raft.sendTimeoutNow.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (to : w64),
  to ≠ id →
  s.gh.xf = false →
  -- (2026-10-29, stage U7) the term past `0` that `send` stamps (`SentMsgShape`)
  s.term ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendTimeoutNow")) (Val #to))
  {{ RET #(); ownRaftPhysCV c c.voters r id s }}

end spec

end EtcdGrove
end Perennial
