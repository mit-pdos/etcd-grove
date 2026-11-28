/-
`rpctransport.Transport.EncodePeer`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `t.EncodePeer(id, a)`: `a`'s bytes. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.EncodePeer.spec : Prop :=
  ∀ (t : Loc) (id a : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport }}
      (App (App (Val (t @!! go.GoType.PointerType Transport.ty @!! go!"EncodePeer")) (Val #id)) (Val #a))
    {{ (s : GoSlice), RET #s; s ↦* (a : List w8) }}

end spec

end Perennial
