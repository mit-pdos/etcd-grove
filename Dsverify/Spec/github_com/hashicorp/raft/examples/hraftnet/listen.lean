/-
`hraftnet.listen`'s spec (the hraft kit, notes/dsv-hraft.md, S5d).
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

open github_com.hashicorp.raft.examples.hraftnet

/-- `listen(a)`: `net.Listen("tcp", a)`, retried until it succeeds (each try's listening token from
the persistent update `net.Listen` asks for, `net.Listen.spec_addrOk`): a listener at `a`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.listen.spec : Prop :=
  ∀ (a : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet ∗
        ⌜addrOk a = true⌝ ∗
        □ (|={⊤,∅}=> netLisTok (extGlobalGS netExt (G := hG.goose_globalGS)) a ∗
          (netLisTok (extGlobalGS netExt (G := hG.goose_globalGS)) a ={∅,⊤}=∗ True)) }}
      (App (Val (@! listen)) (Val #a))
    {{ (li : GoInterface), RET #li; ∃ l, net.isListener li l ∗
        netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
        netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a }}

end spec

end Perennial
