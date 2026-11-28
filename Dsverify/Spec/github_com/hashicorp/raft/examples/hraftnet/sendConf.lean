/-
`hraftnet.sendConf`'s spec (the hraft kit's configuration protocol, notes/dsv-hraft.md, S5g).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ConfDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]
variable [π : NetProtoGS]

open github_com.hashicorp.raft.examples.hraftnet

/-- `sendConf(addr, n0)`: the orchestrator, who drew `n0` (`chosen γc n`), writes its byte to `addr`
(under `confProto γc`) and reads one byte back; any result. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.sendConf.spec : Prop :=
  ∀ (γc : GName) (a : GoString) (n : Nat), N0Ok n →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet ∗
        addrProto (Gg := hG.goose_globalGS) a (confProto γc) ackProto ∗ chosen γc n }}
      (App (App (Val (@! sendConf)) (Val #a)) (Val #(W64 (n : Int))))
    {{ (ok : Bool), RET #ok; True }}

end spec

end Perennial
