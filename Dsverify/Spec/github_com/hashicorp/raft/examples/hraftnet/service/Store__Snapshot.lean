/-
`service.Store.Snapshot`'s spec (the hraft kit's state machine, notes/dsv-hraft.md, S5).
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

/-- `s.Snapshot()`: the store's state at `x` (its last command at `k0 ≤ x`, none in `(k0, x]`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.service.Store.Snapshot.spec : Prop :=
  ∀ (γ : GNames) (fc : FCtx GF) (alb : GName) (i : SID) (s : Loc) (k0 x : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗
      isStore γ fc alb i s ∗ fsmOwn alb k0 ∗ ⌜k0 ≤ x⌝ ∗ noCmdBetween γ k0 (x + 1) }}
    (App (Val (s @!! go.GoType.PointerType Store.ty @!! go!"Snapshot")) (Val #()))
  {{ (sn : Loc), RET (PairV #(interface.mkOk (go.GoType.PointerType snapshot.ty) #sn) #interface.nil);
      fsmOwn alb k0 ∗ snapVal γ fc sn x }}

end spec

end Perennial
