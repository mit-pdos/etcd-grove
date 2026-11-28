/-
`rpctransport.appendFuture.Error`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Trans

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

/-- `f.Error()`: waits for the future's `done` and returns its error (nil or an error). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture.Error.spec : Prop :=
  ∀ (f : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ futDone f }}
      (App (Val (f @!! go.GoType.PointerType appendFuture.ty @!! go!"Error")) (Val #()))
    {{ (e : GoInterface), RET #e; ⌜e = interface.nil⌝ ∨ github_com.hashicorp.raft.errOk e }}

end spec

end Perennial
