/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/snapstore/New.lean (241f27e).
-/
/-
`snapstore.New`'s spec (stage 3).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.snapstore.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.examples.snapstore

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

/-- `New()` (stage 3; hr3's `run`): an empty snapshot store meeting raft's snapshot store contract
(`isSnapStore`, with `io.EOF`'s value `eof`), its abstract state (the latest snapshot: none) owned by
the caller (`own`). -/
abbrev github_com.hashicorp.raft.examples.snapstore.New.spec : Prop :=
  ∀ (eof : GoInterface) (Qc : SnapshotMeta → List w8 → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! github_com.hashicorp.raft.examples.snapstore.New)) (Val #()))
    {{ (st : Loc), RET #st; ∃ own : SnapLatest → IProp GF,
        isSnapStore ⟨go.GoType.PointerType Store.ty, #st⟩ own eof Qc ∗ own none }}

end spec

end Perennial
