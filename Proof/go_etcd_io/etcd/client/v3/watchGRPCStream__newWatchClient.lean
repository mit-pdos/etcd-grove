/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__newWatchClient.lean` (the watch slice's
unit W-C): `newWatchClient` at its first call. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__newWatchClient
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__joinSubstreams
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__waitCancelSubstreams
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__openWatchClient
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__recvLoop
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__sendLoop
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxHeartbeats 0 in
theorem watchGRPCStream.newWatchClient.wp_proof
    (wp_join : watchGRPCStream.joinSubstreams.spec (GF := GF) (hG := hG))
    (wp_wait : watchGRPCStream.waitCancelSubstreams.spec (GF := GF) (hG := hG))
    (wp_open : watchGRPCStream.openWatchClient.spec (GF := GF) (hG := hG))
    (wp_serve : watchGRPCStream.recvLoop.spec (GF := GF) (hG := hG))
    (wp_sendLoop : watchGRPCStream.sendLoop.spec (GF := GF) (hG := hG))
    (wp_Error : rpctypes.Error.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.newWatchClient.spec (GF := GF) (hG := hG) := by
  intro V G callSl m0 s0 rc γrc γresp cc0 bc0
  wp_start as ⟨#HG, Hsub, Hm0, Hres, Hs0, Hrc, Hrcb, #Hrespc, Hrespo, Fsc, Fsb, Had, Htt⟩
  ihave #HG' := HG
  iunfold isWGS at HG'
  icases HG' with ⟨%Hwgsnn, ⟨%vs, #Hvs, #Hcoo⟩, #Hsf, %Hlg, #Fowner, #Fremote, #Fcall, #Fctx, #Fckey,
    #Fcancel, #Freqc, #Frespc, #Fdonec, #Ferrc, #Fclosingc, #Flg, #Hctx, #Hcancel, #Hreq, #Herr,
    #Hclosing, #Hdone⟩
  wp_auto
  wp_apply wp_broadcast_chan_close rc γrc iprop(True) $$ [$Hrcb] as -
  · imodintro; itrivial
  wp_apply chan.wp_make1 (V := Unit) as %rc' %γrc' ⟨#Hrc'c, %-, Hrc'o⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(False) γrc' rc' $$ Hrc'c Hrc'o with Hrc'b
  iunfold sliceOwn at Hs0
  icases Hs0 with ⟨Hs0, Hs0c⟩
  wp_apply wp_join G.wgs m0 ∅ s0 [] (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
    $$ [$Hsub $Hm0 $Hres $Hs0] as ⟨Hsub, Hm0, Hres, Hs0⟩
  · isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    · iapply BigSepL.bigSepL_nil.2; itrivial
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List w64) (_ : Int) => iprop(True)) $$ Hm0
  iintro %keys ⟨%Hk1, %Hk2, %Hk3⟩
  isplitr
  · itrivial
  isplitr
  · imodintro
    iintro %ik %key %vv ⟨%Hkey, %Hvv⟩ -
    simp [GMap.lookup_empty] at Hvv
  iintro - Hm0
  wp_auto
  ihave %Hs0len := ownSlice_len $$ Hs0
  ihave IH1 : iprop("i" ∷ i_ptr ↦ W64 0) $$ [i]
  · iframe
  wp_for IH1
  wp_if_destruct
  · exfalso; simp at Hs0len; word
  wp_apply (wp_map_make1 (K := w64) (V := Loc) go.int64
    (go.GoType.PointerType go_etcd_io.etcd.client.v3.watcherStream.ty)) as %m' Hm'
  wp_apply chan.wp_make1 (V := Unit) as %stopc %γst ⟨#Hstc, %-, Hsto⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γst stopc $$ Hstc Hsto with Hstb
  ihave Hnil : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  wp_apply wp_wait G.wgs slice.nil stopc (DFrac.own 1) $$ [$Hres $Hnil] as %donec ⟨Hres, Hnil, %γdc, #Hdcb⟩
  wp_apply wp_open V G.wgs G.ctx G.cd callSl vs $$ [] as %wc %err Hopen
  · iframe #
  wp_apply wp_broadcast_chan_close stopc γst iprop(True) $$ [$Hstb] as -
  · imodintro; itrivial
  ihave #Hdcc := ownBroadcastChan_is_chan _ _ _ _ $$ Hdcb
  wp_bind (App (Val (chan.receive _)) (Val #donec))
  wp_apply_core chan.wp_receive (V := Unit) donec γdc $$ Hdcc
  iintro -
  iapply broadcast_chan_receive donec γdc iprop(True) _ .Unknown $$ Hdcb
  iintro ⟨-, -⟩
  wp_auto
  ihave IH2 : iprop("i" ∷ i_ptr ↦ W64 0) $$ [i]
  · iframe
  wp_for IH2
  icases Hopen with (⟨%Herr, %γs, %Dn, %cd', #Hcli, Htok, Hrtok, #Hspec⟩ | ⟨⟨%Hwc, %Herr⟩, #Hse⟩)
  · subst Herr
    (try wp_auto)
    wp_apply chan.wp_make2 (V := Loc) (W64 16) as %cc %γcc ⟨#Hccc, %-, Hcco⟩
    · ipureintro; decide
    (try wp_auto)
    wp_apply chan.wp_make2 (V := Loc) (W64 128) as %bc %γbc ⟨#Hbcc, %-, Hbco⟩
    · ipureintro; decide
    (try wp_auto)
    imod start_spsc (V := Loc) cc (sendElem V) (fun _ => iprop(True)) γcc $$ Hccc [Hcco]
      with ⟨%γc, #Hcsp, Hcprod, Hccons⟩
    · iright; iexact Hcco
    imod start_spsc (V := Loc) bc (sendElem V) (fun _ => iprop(True)) γbc $$ Hbcc [Hbco]
      with ⟨%γb, #Hbsp, Hbprod, Hbcons⟩
    · iright; iexact Hbco
    ipersist Fsc
    ipersist Fsb
    ihave #HQ : sendQIs V G.wgs (SendQ.mk cc γc bc γb) $$ []
    · iunfold sendQIs
      iframe #
    ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
    · iPkgInit
    wp_apply wp_wgsWg_Add $$ [Had Htt] as ⟨Had, Hwd⟩
    · iframe
    imod start_spsc (V := Loc) G.respc (respcElem γs Dn) (fun _ => iprop(False)) γresp $$ Hrespc
      [Hrespo] with ⟨%γr, #Hsp, Hprod, Hcons⟩
    · ileft; iexact Hrespo
    ipersist w
    ipersist wc
    wp_apply wp_fork_tok_self $$ [Hwd Htok Hccons Hbcons] as Htt
    · (try wp_auto)
      wp_apply wp_with_defer as %defer' defer'
      (try wp_auto)
      wp_apply wp_sendLoop V G callSl (SendQ.mk cc γc bc γb) wc γs Dn cd' [] [] [] $$ [Htok Hccons Hbcons]
      · iframe #; iframe
      (try wp_auto)
      wp_apply wp_wgsWg_Done $$ [Hwd] as Htt
      · iframe #; iframe
      (try wp_auto)
      iframe Htt
    wp_apply wp_fork $$ [Hrtok Hprod]
    · wp_apply wp_serve V G callSl wc γs Dn cd' γr $$ [$Hrtok $Hprod]
      · iframe #
      itrivial
    iapply HΦ
    iexists m', slice.nil, rc', γrc'
    iframe
    isplitr
    · iunfold sliceOwn; isplitr
      · iapply ownSlice_nil
      · iapply (ownSliceCap_nil (V := Loc))
    ileft
    isplitr
    · ipureintro; rfl
    iexists γs, Dn, γr, SendQ.mk cc γc bc γb
    iframe #
    iframe
  · cases err with
    | nil => exact absurd rfl Herr
    | ok e =>
      wp_auto
      wp_apply wp_Error (GoInterface.ok e) $$ [$Hse] as %err' ⟨%Hne', #Hse', -⟩
      · ipureintro; simp
      iapply HΦ
      iexists m', slice.nil, rc', γrc'
      iframe
      isplitr
      · iunfold sliceOwn; isplitr
        · iapply ownSlice_nil
        · iapply (ownSliceCap_nil (V := Loc))
      iright
      isplitr
      · ipureintro; exact Hne'
      iframe #
      iframe

end proof

end EtcdGrove
end Perennial
