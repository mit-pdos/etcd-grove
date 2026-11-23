/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/CmdStr.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`CommandId.String` (defs.go:173: `fmt.Sprintf("%v,%v", cmdId.ClientId, cmdId.SeqNum)`): its
function `swift.cmdStr` (the two `int32`s' decimals with a comma between), injective
(`swift.cmdStr_inj`: a decimal has no comma, and a decimal determines its integer), and the
method's specs `swift.CommandId.String.specS swift.cmdStr` and `swift.CommandId.String.specI`
proved from the code over `fmt.Sprintf`'s spec (the `str` the run loop's allocation and the
arms take: ServersLink).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Deliver
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs
public import Perennial.Proof.fmt
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.CmdStrDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## The function and its injectivity (pure) -/

section sprintf
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] [go.string ↓u go.string]

end sprintf

/-! ## The method -/

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

theorem swift.CommandId.String.wp_proof : swift.CommandId.String.specS swift.cmdStr := by
  intro p dq x
  wp_start as Hp
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
    [interface.mkOk go.int32 #x.ClientId', interface.mkOk go.int32 #x.SeqNum']
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_auto
  wp_apply fmt.wp_Sprintf_argsWf _ _ _ _
    (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int32 _)
      (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int32 _) fmt.ArgsWf.nil))
    $$ [Hlit] as %s ⟨-, %Hout⟩
  · iexact Hlit
  rw [swift.SprintfOut_v_comma_v _ _ _ Hout,
    show fmt.decimal (sint.Z x.ClientId') ++ W8 44 :: fmt.decimal (sint.Z x.SeqNum') =
      swift.cmdStr x from rfl]
  iapply HΦ
  iframe

theorem swift.CommandId.String.wp_proofI : swift.CommandId.String.specI := by
  intro p x
  wp_start as Hp
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
    [interface.mkOk go.int32 #x.ClientId', interface.mkOk go.int32 #x.SeqNum']
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_auto
  wp_apply fmt.wp_Sprintf_argsWf _ _ _ _
    (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int32 _)
      (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int32 _) fmt.ArgsWf.nil))
    $$ [Hlit] as %s ⟨-, -⟩
  · iexact Hlit
  iapply HΦ
  iframe

end proof

end Perennial.github_com.imdea_software.swiftpaxos
