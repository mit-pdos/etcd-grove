/-
`service.encodeState`'s spec (the hraft kit's state machine, notes/dsv-hraft.md, S5).
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

/-- `encodeState(present, value)`: `"1"` and the value, or `"0"`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.service.encodeState.spec : Prop :=
  ∀ (present : Bool) (value : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service }}
    (App (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.service.encodeState)) (Val #present)) (Val #value))
  {{ RET #(if present then go!"1" ++ value else go!"0"); True }}

end spec

end Perennial
