/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/inproc/Reader__Close.lean (241f27e),
into snapstore (the `Reader` moved there: examples/snapstore/reader.go).
-/
/-
`snapstore.Reader.Close`'s spec (stage 3, package-internal).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.snapstore.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft.examples.snapstore

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

/-- `rd.Close()`: nil. -/
abbrev github_com.hashicorp.raft.examples.snapstore.Reader.Close.spec : Prop :=
  ∀ (rd : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore }}
      (App (Val (rd @!! go.GoType.PointerType Reader.ty @!! go!"Close")) (Val #()))
    {{ RET #interface.nil; True }}

end spec

end Perennial
