/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/wait/timeList__Trigger.lean`. Lean-first (no Rocq counterpart); the
request path's unit 4b.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.timeList__Trigger

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

theorem wait.timeList.Trigger.wp_proof : wait.timeList.Trigger.spec (GF := GF) (hG := hG) := by
  intro tl P d
  wp_start as ⟨#Htl, #HPd⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isTimeList at Htl
  icases Htl with ⟨%mref, #Hm, #Hmu, #Hmono, #Hcl⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold timeListR at HR
  icases HR with ⟨%last, %M, Hlast, HM, #Hlastp, Hchs⟩
  (try wp_auto)
  (try wp_func_lits)
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_mut (fun (_ : Nat) (m' : GMap w64 Loc) =>
      iprop(∃ (c0 : Loc) (t0 : w64),
      "ch" ∷ ch_ptr ↦ c0 ∗ "t" ∷ t_ptr ↦ t0 ∗ "deadline" ∷ deadline_ptr ↦ d ∗ "tl" ∷ tl_ptr ↦ tl ∗
      "Hchs" ∷ [∗map] t ↦ c ∈ m', iprop(∃ γ : ChanNames, ownBroadcastChan c γ (P t) Broadcast.Pending)))
    _ _ _ mref M $$ HM
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [ch t deadline tl Hchs]
  · iexists _, _
    simp only [named]
    iframe
  isplitr
  · imodintro
    iintro %i %key %v %m' ⟨%Hki, %Hmv, %Hagree⟩ HP Hm
    iNamed HP
    have hm'v : m' !! key = some v := by rw [Hagree i key (Nat.le_refl _) Hki]; exact Hmv
    wp_auto
    wp_if_destruct
    · icases (BigSepM.bigSepM_delete (Φ := fun t c =>
          iprop(∃ γ : ChanNames, ownBroadcastChan c γ (P t) Broadcast.Pending)) hm'v).1 $$ Hchs
        with ⟨⟨%γ, Hb⟩, Hchs⟩
      wp_apply wp_mapDelete $$ [$Hm] as Hm
      (try wp_auto)
      ihave #HPk : iprop(□ P key) $$ []
      · iunfold waitMono at Hmono
        imodintro
        iapply Hmono $$ %d %key %Hif HPd
      wp_apply wp_broadcast_chan_close v γ (P key) $$ [$Hb] as -
      · iexact HPk
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hm
      isplitl
      · iexists v, key
        simp only [named]
        iframe
      ipureintro
      intro k hk
      rw [GMap.lookup_delete_ne _ (Ne.symm hk)]
    · (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists m'
      iframe Hm
      isplitl
      · iexists v, key
        simp only [named]
        iframe
      ipureintro
      intro k _; rfl
  iintro %m' HP Hm
  iNamed HP
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlast Hm Hchs]
  · inext; iunfold timeListR; iexists d, m'; iframe; iframe #
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
