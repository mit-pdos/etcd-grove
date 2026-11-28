/-
`service.Store.StoreConfiguration`'s spec (the hraft kit's state machine, notes/dsv-hraft.md, S5).
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

/-- `s.StoreConfiguration(index, c)`: does nothing. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.service.Store.StoreConfiguration.spec : Prop :=
  ∀ (s : Loc) (k : w64) (c : Configuration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service }}
    (App (App (Val (s @!! go.GoType.PointerType Store.ty @!! go!"StoreConfiguration")) (Val #k))
      (Val #c))
  {{ RET #(); True }}

end spec

end Perennial
