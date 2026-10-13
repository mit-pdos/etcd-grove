/- Lean-first (no Rocq counterpart).

## `node.ApplyConfChange(cc)` (node.go:556), 2026-10-13 (reconfiguration stage D)

From any goroutine: `cc.AsV2()` onto `confc` (`confcP`: its changes, read-only, keep the
voters and only drop learners -- `CCShrink`; until 2026-10-13 an unchanged configuration), which `run` applies (`raft.applyConfChange`, the ghost step inside,
`wp_rn_raft_applyConfChange`) and answers with the `ConfState` on `confstatec`
(`confstateP`), which this returns, by pointer. `n.done` never fires.

**Scope**, as `RawNode.ApplyConfChange`'s: a change whose model answer keeps the voters and
some of the learners (`CCShrink` of `ccV2Of o`), e.g. a `ConfChange` with `NodeId = 0`, or a
`RemoveNode` of a learner. The change is held read-only (`DFrac.discard`): `run` reads its `Changes`
on its own goroutine.

**Order with `Advance`** (`issues/raft-advance-before-applyconfchange.md`): an application
must apply a `Ready`'s conf-change entries before it calls `Advance` for that `Ready`, which
node.go's documentation does not say (it allows `Advance` while applying). For the changes
covered here the order does not matter (the configuration in use does not change), so no
premise; a configuration-changing `ApplyConfChange` will need one.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev node.ApplyConfChange.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (c : GoInterface) (o : CCMsg),
  CCShrink γ.raft.reCfg (ccV2Of o).1 (ccV2Of o).2 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      ownCCI c DFrac.discard (some o) }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ApplyConfChange")) (Val #c))
  {{ (csp : Loc) (cs : raftpb.ConfState), RET #csp; csp ↦ cs ∗ confstateP γ cs }}

end spec

end EtcdGrove
end Perennial
