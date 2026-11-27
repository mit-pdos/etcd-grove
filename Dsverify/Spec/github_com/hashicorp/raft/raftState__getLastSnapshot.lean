/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__getLastSnapshot.lean (241f27e).
-/
/-
`raft.(*raftState).getLastSnapshot`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*Raft` (promoted). There is no snapshot.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*raftState).getLastSnapshot`: Called through `*Raft` (promoted). (Stage 3) The last snapshot
`(si, st)`: none, or a committed entry at most `lastApplied`, durable at `i` or installed while `i`
followed (`lastLockInv`). -/
abbrev github_com.hashicorp.raft.raftState.getLastSnapshot.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getLastSnapshot")) (Val #()))
  {{ (si st : w64), RET (PairV #si #st);
      ⌜si = W64 0⌝ ∨ ∃ e : Entry, CIdx γ (uint.nat si) e ∗ ⌜e.term = uint.nat st⌝ ∗
        applLb rc (uint.nat si) ∗
        (durLb γ i (uint.nat si) ∨ snapFollow γ i (uint.nat si) (uint.nat st)) }}

end spec

end Perennial
