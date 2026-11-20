/-
The probe's server node (`harness/netprobe/netprobe.go`): `echo`, `Serve`, `ServerMain`.
-/
module

public import Harness.Proof.dsverify_lab.harness.netprobe.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace dsverify_lab.harness.netprobe

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : netprobe.Assumptions] [model_sem : net.model.Assumptions]

set_option goose.wp.extras true

/-- `echo(c)` on the acceptor's end of a connection to an address with protocols `echoProto`:
it writes back what it reads, which the dialer's protocol says is a prefix of `msg`, so it meets
its own protocol. -/
theorem wp_echo (c : Loc) (cid : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.dsverify_lab.harness.netprobe ∗
        net.ownTCPConn c cid true ∗ sendTok cid true echoProto [] ∗
        recvTok cid true echoProto [] }}
      (App (Val (@! echo)) (Val #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hc, Hsend, Hrecv⟩
  ihave #Hnet := net_init_of_pkg $$ Hpkg
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 64)) as %bs0 ⟨Hb, -⟩
  · ipureintro; decide
  ihave HI : (∃ (R bs : List w8), "Hsend" ∷ sendTok cid true echoProto R ∗
      "Hrecv" ∷ recvTok cid true echoProto R ∗ "Hb" ∷ bs0 ↦* bs : IProp GF) $$ [Hsend Hrecv Hb]
  · iexists [], _; iframe
  wp_for HI
  wp_apply net.TCPConn.Read.wp_proof c cid true bs0 bs echoProto R $$ [$Hnet $Hc $Hrecv $Hb]
    as %n %err ⟨%data, %code, %Hd, Hb, Hrecv, -⟩
  ihave ⟨Hrecv, #Hp⟩ := recvTok_proto_closed echoProto_closed $$ Hrecv
  obtain ⟨rfl, -⟩ := Hd
  rcases err with ei | _
  · wp_auto
    wp_apply net.TCPConn.Close.wp_proof c cid true $$ [$Hnet $Hc] as %err2 -
    wp_for_post
    iapply HΦ; itrivial
  wp_auto
  ihave ⟨%hb, Hpre, Hback⟩ := ownSlice_take_acc bs0 _ data _ $$ Hb
  rw [ite_eq_left hb.1]
  wp_auto
  wp_apply net.TCPConn.Write.wp_proof c cid true _ data (DFrac.own 1) echoProto R
    $$ [$Hnet $Hc $Hsend $Hp $Hpre] as %nw %err ⟨%k, %code2, %Hk, Hpre, Hsend, -⟩
  ihave Hb := Hback $$ Hpre
  rcases err with ei | _
  · wp_auto
    wp_apply net.TCPConn.Close.wp_proof c cid true $$ [$Hnet $Hc] as %err2 -
    wp_for_post
    iapply HΦ; itrivial
  rw [Hk.2.2.2 rfl, List.take_length]
  wp_auto
  wp_for_post
  iframe
  iexists R ++ data, _
  iframe

/-- `Serve(a)`, with the token of `a` and its protocols `echoProto`: it listens on `a`, then
accepts connections and echoes each in its own goroutine, until `Accept` fails. -/
theorem wp_Serve (a : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.dsverify_lab.harness.netprobe ∗ addrTok a ∗
        addrProto a echoProto echoProto }}
      (App (Val (@! Serve)) (Val #a))
    {{ RET #(); True }} := by
  wp_start as ⟨Htok, #Hpr⟩
  ihave #Hnet := net_init_of_pkg $$ Hpkg
  wp_auto
  wp_apply net.Listen.wp_proof a $$ [$Hnet $Htok] as %lv %err ⟨Htok, Hres⟩
  icases Hres with (⟨%l, %lid, %Hlv, #Hl⟩ | ⟨%i, %Hlv, -⟩) <;> obtain ⟨rfl, rfl⟩ := Hlv
  rotate_left
  · wp_auto
    iapply HΦ; itrivial
  wp_auto
  wp_for
  wp_apply net.TCPListener.Accept.wp_proof l lid a echoProto echoProto $$ [$Hnet $Hl $Hpr]
    as %cv %err Hres
  unfold net.newConnResult
  icases Hres with (⟨%c, %cid, %Hcv, #Hc, ⟨Hsend, Hrecv⟩, -⟩ | ⟨%i, %Hcv, -⟩) <;>
    obtain ⟨rfl, rfl⟩ := Hcv
  rotate_left
  · wp_auto
    wp_apply net.TCPListener.Close.wp_proof l lid a $$ [$Hnet $Hl] as %err2 -
    wp_for_post
    iapply HΦ; itrivial
  wp_auto
  wp_apply wp_fork $$ [Hsend Hrecv]
  · wp_apply wp_echo c cid $$ [$Hpkg $Hc $Hsend $Hrecv]
    itrivial
  wp_for_post
  iframe

/-- The server node's program: with the token of `ServerAddr` and its protocols `echoProto`, it
does not panic. -/
theorem wp_ServerMain :
    {{ isPkgInit (PROP := IProp GF) pkg_id.dsverify_lab.harness.netprobe ∗ addrTok serverAddr ∗
        addrProto serverAddr echoProto echoProto }}
      (App (Val (@! ServerMain)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Htok, #Hpr⟩
  wp_apply wp_Serve serverAddr $$ [$Hpkg $Htok $Hpr]
  iapply HΦ; itrivial

end proofs

end dsverify_lab.harness.netprobe

end Perennial
