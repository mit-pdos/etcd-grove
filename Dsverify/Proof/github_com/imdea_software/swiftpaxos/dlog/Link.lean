/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/dlog/Link.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`dlog`'s linked results: a non-verbose logger's `Println`, `Printf`, `Fatal` do nothing.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Logger__Println
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Logger__Printf
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Logger__Fatal

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [dlog.Assumptions]

theorem dlog.Logger.wp_Println : dlog.Logger.Println.spec (GF := GF) := dlog.Logger.Println.wp_proof
theorem dlog.Logger.wp_Printf : dlog.Logger.Printf.spec (GF := GF) := dlog.Logger.Printf.wp_proof
theorem dlog.Logger.wp_Fatal : dlog.Logger.Fatal.spec (GF := GF) := dlog.Logger.Fatal.wp_proof

end link

end Perennial.github_com.imdea_software.swiftpaxos
