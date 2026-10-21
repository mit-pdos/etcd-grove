/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/newBridge.lean`: the bridge's
ghost state (the flag, the registry, the receipts), its wait group with `serveListen` counted
(by the flag, not a token: the `go` statement's fresh token goes to `serveListen`), and its mutex
with the empty map and `blackholec` whole. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.newBridge
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__serveListen
public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridge

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.third_party

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

theorem newBridge.wp_proof (wp_serveListen : bridge.serveListen.spec (GF := GF) (hG := hG)) :
    newBridge.spec (GF := GF) (hG := hG) := by
  intro addr l Htb
  wp_start as ⟨#Hrl, Htok⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_map_make1 (K := Loc) (V := Unit) (go.GoType.PointerType bridge.bridgeConn.ty)
    (go.GoType.StructType [])) as %m Hm
  wp_apply chan.wp_make1 (V := Unit) as %sc %γsc ⟨#Hscc, %-, Hsco⟩
  wp_apply chan.wp_make1 (V := Unit) as %pc %γpc ⟨#Hpcc, %-, Hpco⟩
  wp_apply chan.wp_make1 (V := Unit) as %bhc %γbh ⟨#Hbhcc, %-, Hbhco⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γpc pc $$ Hpcc Hpco with Hpcb
  icases ownBroadcastChan_Pending_Unknown _ _ _ $$ Hpcb with ⟨Hpcb, #Hpcu⟩
  wp_apply wp_broadcast_chan_close pc γpc iprop(True) $$ [$Hpcb] as Hpcd
  · imodintro; itrivial
  iStructNamed «$r0»
  imod sync.init_WaitGroup bridgeWGN (bF «$r0_ptr» go!"wg") $$ wg with ⟨%γwg, #Hwgl, Hctr, Hwait⟩
  imod ghostVar_alloc false with ⟨%γh, Hh⟩
  icases ghostVar_split_half γh 1 false $$ Hh with ⟨Hh1, Hh2⟩
  imod ghostVar_alloc false with ⟨%γs, Hs⟩
  icases ghostVar_split_half γs 1 false $$ Hs with ⟨Hs1, Hs2⟩
  imod ownTokAuth_alloc with ⟨%γr, Hr⟩
  imod ghost_map_alloc_empty (K := Loc) (V := Qp × GName) with ⟨%γreg, Hreg⟩
  wp_bind (App (Val (bF «$r0_ptr» go!"wg" @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add"))
    (Val #(W64 1)))
  iapply (sync.WaitGroup.wp_Add (bF «$r0_ptr» go!"wg") (W64 1) γwg bridgeWGN) $$ []
    [Hctr Hwait Hs1 Hs2 Hr HΦ Htok Hm Hsco Hbhco b dialer l conns stopc pausec blackholec mu Hh1 Hh2
     Hreg Hpcd]
  · iframe #
  iapply fupd_mask_intro (fun _ _ => CoPset.mem_full)
  iintro Hmask
  inext
  iexists W32 0
  iframe Hctr
  isplitr
  · ipureintro; decide
  iright
  iframe Hwait
  iintro Hwait Hctr
  imod Hmask with -
  imod ghostVar_update_halves true γs false false $$ Hs1 Hs2 with ⟨Hsl, Hs2⟩
  ihave Hz := threadToks_zero (GF := GF)
  imod inv_alloc bridgeWgInvN ⊤ (wgInv (BridgeNames.mk γh γwg γr γs γreg)) $$ [Hctr Hs2 Hr Hwait Hz]
    with #Hwgi
  · inext
    unfold wgInv
    iexists W32 0 + W32 (sint.Z (W64 1)), 0, true
    simp only [↓reduceIte]
    iframe
    isplitl [Hz]
    · iexact Hz
    ipureintro; decide
  imodintro
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γbh bhc $$ Hbhcc Hbhco with Hbhb
  icases ownBroadcastChan_Pending_Unknown _ _ _ $$ Hbhb with ⟨Hbhb, #Hbhu⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γsc sc $$ Hscc Hsco with Hscb
  ihave #Hscu := ownBroadcastChan_Unknown _ _ _ _ $$ Hscb
  imod sync.init_Mutex (lockInv «$r0_ptr» (BridgeNames.mk γh γwg γr γs γreg)) ⊤
    (bF «$r0_ptr» go!"mu") $$ mu [conns Hm pausec Hpcd blackholec Hh2 Hbhb Hreg] with #Hmu
  · inext
    unfold lockInv
    iexists m, ∅, ∅, ∅, pc, bhc, γpc, γbh, false, 1
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    iframe #
    isplitr
    · ipureintro; intro c; rfl
    isplitl [Hpcd]
    · iright; iexact Hpcd
    isplitr
    · iintro ⟨H, -⟩; iexact H
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    ipureintro; intro c x h; exact h
  ipersist dialer
  ipersist l
  ipersist stopc
  ihave #HB : isBridge «$r0_ptr» (BridgeNames.mk γh γwg γr γs γreg) addr $$ []
  · unfold isBridge
    iexists l, sc, γsc
    iframe #
    ipureintro; exact Htb
  wp_auto
  wp_apply wp_fork_tok_body $$ [Hsl]
  · iintro Htok'
    wp_apply wp_serveListen «$r0_ptr» (BridgeNames.mk γh γwg γr γs γreg) addr $$ [Hsl Htok']
      as Htok'
    · iframe #; iframe
      unfold slRunning; iexact Hsl
    iframe Htok'
    ipureintro; exact isPanic_intoVal _
  iapply HΦ
  iexists BridgeNames.mk γh γwg γr γs γreg
  iframe #
  unfold bridgeHoled
  iframe

end proof

end bridge
end EtcdGrove
end Perennial
