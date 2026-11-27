/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/snapstore/Store__Latest.lean (241f27e).
-/
/-
`snapstore.Store.Latest`'s spec (stage 3, package-internal).
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

/-- `st.Latest()`: not called by the verified program (main_test.go's checks only). -/
abbrev github_com.hashicorp.raft.examples.snapstore.Store.Latest.spec : Prop :=
  ∀ (st : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗ False }}
      (App (Val (st @!! go.GoType.PointerType Store.ty @!! go!"Latest")) (Val #()))
    {{ RET #(W64 0); True }}

end spec

end Perennial
