/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Client__dialMaster.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`c.dialMaster()` (client/client.go): `fmt.Sprintf("%s:%d", ...)` of the master's address and
port (`sp.addrPort`, port 7001), up to three `rpc.DialHTTP`s.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ConnectSpecs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println
public import Perennial.Proof.errors.NewVar

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
  Perennial.fmt

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [client.Assumptions] [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [examples.swiftnet.Assumptions] [dlog.Assumptions] [fmt.Assumptions] [errors.Assumptions]
-- the codec (decision D6, Proof/swiftnet/KitLike.lean): `kitCodec` for the frozen statements,
-- `kitCodecC` in the link
variable [C : net.rpc.RpcCodec netDistGF]

set_option goose.wp.extras true

theorem client.Client.dialMaster.wp_proof
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) :
    client.Client.dialMaster.specI (hG := hG) := by
  intro cl v W
  wp_start as ⟨Hcl, #Hq, %Hv, #Ha⟩
  wp_auto
  rw [decide_eq_true Hv.1]
  wp_auto
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.string #v.masterAddr', interface.mkOk go.int #v.masterPort']
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_auto
  wp_apply fmt.wp_Sprintf _ _ _ _ (ArgsWf.cons_string _ _ (ArgsWf.cons_int _ _ _
    (IntArgValue.int v.masterPort') ArgsWf.nil)) $$ [$Hasl] as %str ⟨-, %Hs⟩
  have Hs := master.sprintf_str_d _ _ str Hs
  have hport := client.cn.masterAddr_port Hv.2
  rw [master.decimal_addrPort _ _ (by rw [hport]; decide), Hv.2] at Hs
  subst Hs
  ipersist addr
  ihave HI : (∃ t : w64, "Htry" ∷ try_ptr ↦ t ∗ "Hcl" ∷ cl ↦ v ∗
      "%Ht" ∷ ⌜0 ≤ sint.Z t ∧ sint.Z t ≤ 3⌝ : IProp netDistGF) $$ [«try» Hcl]
  · iexists _; iframe; ipureintro; word
  wp_for HI
  wp_if_destruct
  · wp_apply net.rpc.DialHTTP.wp W masterAddr $$ [$Ha] as %mc %err Hd
    icases Hd with (⟨%Herr, #Hmc⟩ | ⟨%Herr, -⟩)
    · subst Herr
      wp_auto
      wp_for_post
      iapply HΦ
      ileft
      iframe Hmc
      isplitr
      · ipureintro; rfl
      iexact Hcl
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ei => ?_
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨-, -⟩
      wp_auto
      wp_method_call
      wp_call
      wp_auto
      wp_apply wp_Println $$ Hq
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro; word
  · wp_apply errors.wp_New_errorString as %x _
    iapply HΦ
    iright
    iframe Hcl
    ipureintro; simp [interface.mkOk]

end proof

end Perennial.github_com.imdea_software.swiftpaxos
