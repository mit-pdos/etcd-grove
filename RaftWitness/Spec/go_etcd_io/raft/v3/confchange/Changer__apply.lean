/-
`Changer.apply` applies a list of single changes to a config. Lean-first (no Rocq
counterpart); see `InvConfchange.lean`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvConfchange
public import RaftWitness.Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `apply(cfg, trk, ccs)`: `applyM`. On an error the state is left unspecified (every
caller discards it). (Generalized 2026-10-12 from `[AddNode id]`.) (2026-10-15, raft v3.7
retarget, stage R2: `ccs` a slice of `*pb.ConfChangeSingle` pointers `ls`, each `ccsRO` of its
change in `l`, read through the getters; was a slice of the struct values `l`.)

raft#168 added `ConfChangeAddWitness` (type `4`), which `applyM` (the model of the code before
it) rejects as an unexpected type and the PR's code applies (`makeWitness`): the premise
excludes it (a change of type `4` with a non-zero id), so this is the old statement on the
changes that existed before. The PR's other changes (`makeVoter`/`makeLearner` returning an
error) are invisible on a witness-free configuration (`ownWork`). -/
abbrev confchange.Changer.apply.spec : Prop :=
  ∀ (p cfgp trk : Loc) (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (s : CCState) (ccs : GoSlice) (ls : List Loc) (l : List ConfChangeSingleM) (dq dqs : DFrac),
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  -- (2026-10-20, witness support; until then no `AddWitness`) a witness only at a non-joint
  -- configuration (`Simple`'s); `EnterJoint` at a witness-free one, with no `AddWitness`
  (s.cfg.outgoing = ∅ ∨ (s.cfg.wit = W64 0 ∧ ∀ c ∈ l, c.NodeId' ≠ W64 0 → c.Type' ≠ W32 4)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗
      ccs ↦*{dqs} ls ∗ ([∗list] q;c ∈ ls;l, ccsRO q c) ∗ ownWork chg base cfgp trk s }}
    (App (App (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"apply")) (Val #cfgp)) (Val #trk)) (Val #ccs))
  {{ (err : GoInterface), RET #err; p ↦{dq} chg ∗ ccs ↦*{dqs} ls ∗
      match applyM l s with
      | none => ⌜err ≠ interface.nil⌝
      | some s' => ⌜err = interface.nil⌝ ∗ ownWork chg base cfgp trk s' }}

end spec

end EtcdGrove
end Perennial
