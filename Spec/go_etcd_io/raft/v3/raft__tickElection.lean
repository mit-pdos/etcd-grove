/- Lean-first (no Rocq counterpart).

## `raft.tickElection` (raft.go), a non-leader's `r.tick`

`electionElapsed++`; once past the (randomized) election timeout, a node that can be
leader (`promotable`) resets the counter and steps a `MsgHup` from itself: it campaigns.
Specified like `raft.Step` (the ghost state, `NStateRel`), with what `RawNode.Tick` needs
of the physical state: `TickStep`. In any role: a leader's `MsgHup` is ignored.

Lean notes: like `raft.Step.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__Step

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- What a tick does to the physical state beyond the protocol: the log as `NetFrame`
keeps it, the term up by at most one (a campaign), `offsetInProgress` not back. -/
def TickStep [FfiSyntax] (s s' : NState) : Prop :=
  NetFrame s s' ∧ uint.Z s.term ≤ uint.Z s'.term ∧ uint.Z s'.term ≤ uint.Z s.term + 1 ∧
  uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress

theorem TickStep.refl [FfiSyntax] (s : NState) : TickStep s s :=
  ⟨NetFrame.refl s, Int.le_refl _, by omega, Int.le_refl _⟩

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev raft.tickElection.spec : Prop :=
  ∀ (cfg : GSet w64) (γ : RaftNames) (r : Loc) (id : w64) (s : NState) (ps : PState),
  γ.reCfg = cfg →
  -- a campaign increments the term; `send` panics if it wraps
  uint.Z s.term + 1 < 2 ^ 64 →
  NStateRel s ps →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "Hghost" ∷ ownRaftGhost γ id ps }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"tickElection")) (Val #()))
  {{ (s' : NState) (ps' : PState), RET #();
      "Hphys" ∷ ownRaftPhys cfg r id s' ∗
      "Hghost" ∷ ownRaftGhost γ id ps' ∗
      "%Hrel" ∷ ⌜NStateRel s' ps'⌝ ∗
      "%Hrefines" ∷ ⌜∃ recv, Step cfg id ps recv ps'⌝ ∗
      "%Htick" ∷ ⌜TickStep s s'⌝ }}

end spec

end EtcdGrove
end Perennial
