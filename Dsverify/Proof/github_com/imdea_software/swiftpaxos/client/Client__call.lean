/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Client__call.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`c.call(r, method, args, reply)` (client/client.go): `r.Call` in a goroutine whose result is sent
on a buffered channel (a bag carrying the call's postcondition), and a `select` between that
channel and `time.After(3 s)`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ConnectSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcClient
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.time.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace client.cn

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- What the call's goroutine sends: the call's result (`Call.spec`'s postcondition, weakened). -/
def callP (Rargs : IProp netDistGF) (Φ : List w8 → GoString → IProp netDistGF)
    (Θ : List w8 → Bool → IProp netDistGF) (err : GoInterface) : IProp netDistGF :=
  iprop((⌜err = interface.nil⌝ ∗ Rargs ∗ ∃ rep, Φ rep [] ∗ Θ rep true) ∨ ⌜err ≠ interface.nil⌝)

end defs

end client.cn

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [client.Assumptions] [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [examples.swiftnet.Assumptions] [dlog.Assumptions] [errors.Assumptions] [time.Assumptions]
-- the codec (decision D6, Proof/swiftnet/KitLike.lean): `kitCodec` for the frozen statements,
-- `kitCodecC` in the link
variable [C : net.rpc.RpcCodec netDistGF]

set_option goose.wp.extras true

theorem client.Client.call.wp_proof
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) :
    client.Client.call.specI (hG := hG) := by
  intro cl v r W a sm svc M S args reply Φc Rargs D Θ
  wp_start as ⟨Hcl, #Hq, #Hcs, #Hko, #Hrc, %HS, Henc, HD, #HDw⟩
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (t := go.error) (W64 1)) as %ch %γ ⟨#Hch, %Hcap, Hown⟩
  · ipureintro; decide
  imod start_bag (client.cn.callP Rargs Φc Θ) (ChanState.Buffered []) ch γ (by trivial) $$
    Hch Hown with #Hbag
  ipersist method
  ipersist args
  ipersist reply
  ipersist r
  ipersist errs
  wp_apply (lc := 4) wp_fork $$ [Henc HD]
  · wp_auto
    wp_apply net.rpc.swiftClient.Client.Call.wp r W a sm svc M S args reply Φc Rargs D Θ
      net.rpc.RpcCodec.spec $$ [$Hcs $Hrc Henc $HD $HDw] as %err Hres
    · isplitr
      · ipureintro; exact HS
      iexact Henc
    wp_apply wp_bag_send γ ch err (client.cn.callP Rargs Φc Θ) $$ [$Hbag Hres]
    · unfold client.cn.callP
      icases Hres with (⟨%He, HR, %rep, HΦ, HΘ⟩ | ⟨%msg, ⟨%Hm, %He⟩, -, -, -, -⟩ | ⟨⟨%He, -⟩, -, -⟩)
      · ileft; iframe; ipureintro; exact He
      · iright; ipureintro; subst He; simp [net.rpc.serverErr, interface.mkOk]
      · iright; ipureintro; exact He
    itrivial
  wp_apply time.wp_After as %ach %γa #Hafter
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the call's result
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au γ ch _ _ $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %err HP
    wp_auto
    unfold client.cn.callP
    icases HP with (⟨%He, HR, HΦr⟩ | %He)
    · subst He
      wp_auto
      iapply HΦ
      iframe Hcl
      ileft
      iframe
      ipureintro; rfl
    · cases err with
      | nil => exact absurd rfl He
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
      iapply HΦ
      iframe Hcl
      iright
      ipureintro; exact He
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the timeout
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, ach, γa
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hafter
    iapply bag_recv_au γa ach _ _ $$ [$Hlc3 $Hlc4] Hafter
    inext
    iintro %t -
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
    wp_apply errors.wp_New_errorString as %x _
    iapply HΦ
    iframe Hcl
    iright
    ipureintro; simp [interface.mkOk]
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end Perennial.github_com.imdea_software.swiftpaxos
