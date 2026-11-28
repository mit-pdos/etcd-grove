/-
`hraftnet.Register`'s spec (the hraft kit's generated codec registration, `rpc_model_gen.go`;
notes/dsv-hraft.md, S4).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]
variable [net.rpc.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet

/-- `Register()`: the kit's generated codec (`hraftCodec`) registered with net/rpc, from net/rpc's
unregistered codec state (`SetCodec`'s premise). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.Register.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
      sync.isMutex (globalAddr net.rpc.codecMu) (net.rpc.codecInv (GF := GF)) ∗ net.rpc.codecUnset }}
    (App (Val (@! Register)) (Val #()))
  {{ RET #(); net.rpc.codecSet (hraftCodec (GF := GF)) }}

end spec

end Perennial
