/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__RemoveServer.lean (241f27e).
-/
/-
`raft.Raft.RemoveServer`'s spec (stage 4 interface).
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

/-- `(*Raft).RemoveServer(id, prevIndex, timeout)` (stage 4), for one of the servers `id`: a future
answering `cfgChangeQ` (`requestConfigChange` of a `RemoveServer` request; a removed server keeps
running, `cfgOk`'s `ShutdownOnRemove` off). -/
abbrev github_com.hashicorp.raft.Raft.RemoveServer.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (id : ServerID) (prev : w64) (tmo : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     ⌜(id : List w8) ∈ γ.srvs ∧
       ((id : List w8) ≠ [] ∧ (id : List w8).length < 2 ^ 63 ∧ γ.srvs.length < 2 ^ 32)⌝ }}
    (App (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"RemoveServer")) (Val #id)) (Val #prev)) (Val #tmo))
  {{ (fi : GoInterface), RET #fi; futWait fi cfgChangeQ }}

end spec

end Perennial
