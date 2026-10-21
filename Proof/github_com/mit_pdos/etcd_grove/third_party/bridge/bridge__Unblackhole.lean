/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/bridge__Unblackhole.lean`: the
loop gives back every registered connection's share of `b.blackholec` (`wp_drain`), so the
write of the field has it whole. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__Unblackhole
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridgeConn__Close
public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridgeP

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.third_party

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

theorem bridge.Unblackhole.wp_proof (wp_Close : bridgeConn.Close.spec (GF := GF) (hG := hG)) :
    bridge.Unblackhole.spec (GF := GF) (hG := hG) := by
  intro b γ addr h
  wp_start as ⟨#Hb, Hown⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isBridge at Hb
  icases Hb with ⟨%l, %sc, %γsc, #Hd, #Hl, #Hrl, #Hsc, #Hscb, #Hmu, #Hwg, #Hwgi, %Htb⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, Hi⟩
  · iframe #
  iunfold lockInv at Hi
  icases Hi with ⟨%m, %conns, %shares, %reg, %pc, %bhc, %γpc, %γbh, %holed, %q, Hconns, Hm, %Hdom,
    Hpausec, #Hpc, Hpcst, Hbh, #Hbhc, Hholed, Hbhst, Hwand, Hregs, Hreg, #Hregf, %Hsub⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) (Val #m)) _)
  iapply (wp_drain b m _ conns shares q bhc iprop(∃ v : Loc, bc_ptr ↦ v) _ Hdom) $$ [] [bc] Hm Hbh
    Hwand Hregs
  · iintro !> %c %q' %γt #Hc ⟨%v, Hbcp⟩
    wp_auto
    wp_apply wp_Close b c q' γt $$ [] as #HQ
    · iframe #
    isplitr
    · ipureintro; rfl
    iframe #
    iexists _; iexact Hbcp
  · iexists _; iexact bc
  iintro %q' ⟨%v, bc⟩ Hm Hbh Hwand
  ihave Hfull := share_all b bhc q' $$ [Hbh Hwand]
  · iframe
  wp_auto
  wp_apply (wp_map_make1 (K := Loc) (V := Unit) (go.GoType.PointerType bridge.bridgeConn.ty)
    (go.GoType.StructType [])) as %m' Hm'
  wp_apply chan.wp_make1 (V := Unit) as %nc %γnc ⟨#Hnc, %-, Hnco⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γnc nc $$ Hnc Hnco with Hncb
  icases ownBroadcastChan_Pending_Unknown _ _ _ $$ Hncb with ⟨Hncb, #Hncu⟩
  iunfold bridgeHoled at Hown
  imod ghostVar_update_halves false γ.holed h holed $$ Hown Hholed with ⟨Hown, Hholed⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hpausec Hpcst Hreg Hm' Hconns Hfull Hncb Hholed]
  · iframe #
    iunfold lockInv
    iexists m', ∅, ∅, reg, pc, nc, γpc, γnc, false, 1
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    iframe #
    isplitr
    · ipureintro; intro c; simp
    isplitr
    · inext; iintro ⟨H, -⟩; iexact H
    isplitr
    · inext; iapply BigSepM.bigSepM_empty.2; itrivial
    inext; ipureintro; intro c x h; simp at h
  iapply HΦ
  iunfold bridgeHoled
  iexact Hown

end proof

end bridgeP
end EtcdGrove
end Perennial
