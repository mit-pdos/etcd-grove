/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/bridge__DropConnections.lean`:
the loop gives back every registered connection's share (`wp_drain`), so the emptied map has
none out. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__DropConnections
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

theorem bridge.DropConnections.wp_proof (wp_Close : bridgeConn.Close.spec (GF := GF) (hG := hG)) :
    bridge.DropConnections.spec (GF := GF) (hG := hG) := by
  intro b γ addr
  wp_start as #Hb
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isBridge at Hb
  icases Hb with ⟨%l, %sc, %γsc, #Hd, #Hl, #Hrl, #Hsc, #Hscb, #Hmu, #Hwg, #Hwgi, %Htb⟩
  wp_apply wp_with_defer as %defer defer
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
  wp_auto
  wp_apply (wp_map_make1 (K := Loc) (V := Unit) (go.GoType.PointerType bridge.bridgeConn.ty)
    (go.GoType.StructType [])) as %m' Hm'
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hpausec Hpcst Hreg Hm' Hconns Hbh Hwand Hholed Hbhst]
  · iframe #
    iunfold lockInv
    iexists m', ∅, ∅, reg, pc, bhc, γpc, γbh, holed, q'
    iframe
    iframe #
    isplitr
    · ipureintro; intro c; simp
    isplitr
    · inext; iapply BigSepM.bigSepM_empty.2; itrivial
    inext; ipureintro; intro c x h; simp at h
  iapply HΦ
  itrivial

end proof

end bridgeP
end EtcdGrove
end Perennial
