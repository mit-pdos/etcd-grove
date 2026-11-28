/-
`rpctransport.appendFuture.Start`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `f.Start()`: its `start` field. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture.Start.spec : Prop :=
  ∀ (f : Loc) (ts : time.Time),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ f.[appendFuture, go!"start"] ↦□ ts }}
      (App (Val (f @!! go.GoType.PointerType appendFuture.ty @!! go!"Start")) (Val #()))
    {{ RET #ts; True }}

end spec

end Perennial
