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

**The dynamic mode (2026-10-15, stage N).** In a node of the dynamic mode (`γ.mode`, from
`RestartNode`), any change the driver applies in order: the change of the next conf-change
entry `e` of the committed log `ds` it was handed (`dlvLb`), at position `k` past its
configuration index `ca` (`DynCCPreOp`: the decoder's change, which applies to its
configuration `cfg` with no `confchange` error and is no auto-leave joint configuration). The
driver's view `nodeCfg γ ca cfg` goes along with the change on `confc` (`confcP`) and comes back
on `confstatec` at `(k + 1, cs')` (`confstateP`, recognized by the answer slot `ccq`); the run
loop checks the premises against its `RawNode` (`runCfg_confc`) and applies the change there
(`StepR.applyConf`, a removed leader stepping down). The answer is the new configuration's
`ConfState` (`confstateOk`). A1 at `Advance` (`node.Advance.spec`) is what makes the order
matter.

**raft v3.7 (2026-10-16, stage R5).** `cc.AsV2()` is a `*pb.ConfChangeV2` (for a
`*ConfChangeV2`, `cc` itself), sent on `confc` read-only (`confcP`: `ownCCV2 v □`, hence
`ownCCI c □`); the answer is the `*pb.ConfState` `run`'s `applyConfChange` returned, owned
(`csPts csp 1 cs true`), its lists the record's (`confstateS`/`confstateOk` pure). Go returns
`nil` if `done` fires first, which it never does.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvNode

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
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (c : GoInterface) (o : CCMsg)
    -- (2026-10-15, stage N) the dynamic mode's: the committed log the driver was handed (a
    -- lower bound of `run`'s), its view of the configuration, the conf entry applied (at
    -- position `k`) and the configuration it gives
    (ds : List EntryM) (ca : Nat) (cfg : CCState) (k : Nat) (e : EntryM)
    (cs' : CCState),
  -- the static mode (the voters fixed): a change that keeps the voters, drops learners
  (γ.mode = .static → CCShrink γ.raft.reCfg (ccV2Of o).1 (ccV2Of o).2) →
  -- the dynamic mode: the next committed conf entry's decoded change, which applies
  (∀ dec c0 h0 h1, γ.mode = .dyn dec c0 h0 h1 → DynCCPreOp dec ds ca cfg (ccV2Of o) k e cs') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      ownCCI c DFrac.discard (some o) ∗
      (⌜γ.mode = .static⌝ ∨ nodeCfg γ ca cfg ∗ dlvLb γ ds) }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ApplyConfChange")) (Val #c))
  {{ (csp : Loc) (cs : ConfStateM), RET #csp;
      -- (2026-10-16, stage R5) `applyConfChange`'s fresh `*pb.ConfState`, owned (`confstateP`;
      -- until then `csp ↦ cs` with the slices in `confstateS`/`confstateOk`)
      csPts csp (DFrac.own 1) cs true ∗
      ((⌜γ.mode = .static⌝ ∗ ⌜confstateS γ cs⌝) ∨
       (⌜γ.mode.isDyn = true⌝ ∗ nodeCfg γ (k + 1) cs' ∗ ⌜confstateOk cs cs'.cfg⌝)) }}

end spec

end EtcdGrove
end Perennial
