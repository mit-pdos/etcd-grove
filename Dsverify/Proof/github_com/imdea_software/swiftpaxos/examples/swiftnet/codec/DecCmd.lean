/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/DecCmd.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The codec's decoders of `state.Operation`, `state.Key`, `state.Value`, `state.Command` and
`swift.Dep` meet their parsers.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.DecList

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]

theorem wp_rpcDec_state_Operation (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_state_Operation)) (Val #b))
    {{ (x : w8) (r : GoSlice) (ok : Bool), RET (PairV (PairV #x #r) #ok);
        decPost pU8 ownPure b dq bs x r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcDec_uint8 $$ Hb as %x %r %ok Hpost
  iapply HΦ $$ Hpost

theorem wp_rpcDec_state_Key (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_state_Key)) (Val #b))
    {{ (x : w64) (r : GoSlice) (ok : Bool), RET (PairV (PairV #x #r) #ok);
        decPost pInt ownPure b dq bs x r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcDec_int64 $$ Hb as %x %r %ok Hpost
  iapply HΦ $$ Hpost

theorem wp_rpcDec_state_Value (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_state_Value)) (Val #b))
    {{ (v : GoSlice) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost pBytes ownSliceOf b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcDec_S_byte $$ Hb as %x %r %ok Hpost
  iapply HΦ $$ Hpost

theorem wp_rpcDec_swift_Dep (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_swift_Dep)) (Val #b))
    {{ (v : GoSlice) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost (pList pCmdId) ownSliceOf b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcDec_S_swift_CommandId $$ Hb as %x %r %ok Hpost
  iapply HΦ $$ Hpost

/-- A decoded command: its operation and key, and a fresh slice holding its value. -/
def ownCmd (c : state.Command) (x : sp.Cmd) : IProp GF :=
  iprop(⌜c.Op' = x.op ∧ c.K' = x.key⌝ ∗ c.V' ↦* x.val)

theorem wp_rpcDec_state_Command (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_state_Command)) (Val #b))
    {{ (c : state.Command) (r : GoSlice) (ok : Bool), RET (PairV (PairV #c #r) #ok);
        decPost pCmd ownCmd b dq bs c r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcDec_state_Operation $$ Hb as %op %r0 %ok0 Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%op', %rest0, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pCmd, H], rfl⟩
  obtain ⟨H, rfl⟩ := H
  subst Hown
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_apply wp_rpcDec_state_Key $$ Hr as %k %r1 %ok1 Hpost
  unfold decPost
  icases Hpost with (⟨%H1, Hr⟩ | ⟨%k', %rest1, %H1, %Hown, Hrest⟩)
  · obtain ⟨H1, rfl⟩ := H1
    ihave Hb := Hback $$ Hr
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pCmd, H, H1], rfl⟩
  obtain ⟨H1, rfl⟩ := H1
  subst Hown
  ihave Hrest := restOf_comp $$ Hback Hrest
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_apply wp_rpcDec_state_Value $$ Hr as %v %r2 %ok2 Hpost
  unfold decPost
  icases Hpost with (⟨%H2, Hr⟩ | ⟨%v', %rest2, %H2, Hown, Hrest⟩)
  · obtain ⟨H2, rfl⟩ := H2
    ihave Hb := Hback $$ Hr
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pCmd, H, H1, H2], rfl⟩
  obtain ⟨H2, rfl⟩ := H2
  ihave Hrest := restOf_comp $$ Hback Hrest
  wp_auto
  iapply HΦ; iright; iexists ⟨op, k, v'⟩, rest2
  iframe Hrest
  isplitr
  · ipureintro; exact ⟨by simp [pCmd, H, H1, H2], rfl⟩
  unfold ownCmd ownSliceOf
  iframe Hown
  ipureintro; exact ⟨rfl, rfl⟩

end wps

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
