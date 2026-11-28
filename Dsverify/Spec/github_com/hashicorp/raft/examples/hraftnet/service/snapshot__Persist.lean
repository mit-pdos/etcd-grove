/-
`service.snapshot.Persist`'s spec (the hraft kit's state machine, notes/dsv-hraft.md, S5).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.FsmDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

/-- `sn.Persist(sink)`: writes the snapshot's bytes (a snapshot of `x`) to the sink and closes it. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.service.snapshot.Persist.spec : Prop :=
  ∀ (γ : GNames) (fc : FCtx GF) (sn : Loc) (x : Nat) (k : GoInterfaceOk) (id : GoString)
    (own : Option (List w8) → IProp GF) (Q R : List w8 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗ snapVal γ fc sn x ∗
      isSink k id own Q R ∗ □ (∀ b, snapP γ fc x b -∗ Q b) ∗ own (some []) }}
    (App (Val (sn @!! go.GoType.PointerType snapshot.ty @!! go!"Persist")) (Val #(GoInterface.ok k)))
  {{ RET #interface.nil; own none }}

end spec

end Perennial
