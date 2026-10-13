/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `sendTimeoutNow(to)`: `send` of `MsgTimeoutNow{To: to}`, a type the model does not
describe (`mtypeOf` is `none`): it carries no protocol fact and drops out of the abstract
outbox, so the state is unchanged. `to` is another node (`send` panics on a message to
oneself): the leader-transfer target, which `ownRaftPhys` keeps `≠ id`. -/
abbrev raft.sendTimeoutNow.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (to : w64),
  to ≠ id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendTimeoutNow")) (Val #to))
  {{ RET #(); ownRaftPhys cfg r id s }}

end spec

end EtcdGrove
end Perennial
