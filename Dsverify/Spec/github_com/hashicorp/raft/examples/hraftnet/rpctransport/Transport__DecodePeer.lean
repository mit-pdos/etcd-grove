/-
`rpctransport.Transport.DecodePeer`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `t.DecodePeer(buf)`: `buf`'s bytes as an address. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.DecodePeer.spec : Prop :=
  ∀ (t : Loc) (buf : GoSlice) (dq : DFrac) (b : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ buf ↦*{dq} b }}
      (App (Val (t @!! go.GoType.PointerType Transport.ty @!! go!"DecodePeer")) (Val #buf))
    {{ RET #(b : GoString); buf ↦*{dq} b }}

end spec

end Perennial
