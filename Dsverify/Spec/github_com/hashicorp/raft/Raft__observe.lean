/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__observe.lean (241f27e).
-/
/-
`raft.(*Raft).observe`'s spec (raft-internal interface, notes/raft-iface.md). Runs every registered observer's filter on `Observation{r, d}` (no observer has a channel), lending it `obsArg γ i s d`. Takes the observers' read lock (a thread token).
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

/-- `(*Raft).observe`: Runs every registered observer's filter on `Observation{r, d}` (no observer has a channel), lending it `obsArg γ i s d`. Takes the observers' read lock (a thread token). -/
abbrev github_com.hashicorp.raft.Raft.observe.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (d : GoInterface) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ obsArg γ i s d ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"observe")) (Val #d))
  {{ RET #(); obsArg γ i s d ∗ rtok tid }}

end spec

end Perennial
