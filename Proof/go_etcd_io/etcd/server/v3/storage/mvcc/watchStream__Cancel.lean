/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Cancel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchStream.Cancel.wp_proof :
    mvcc.watchStream.Cancel.spec (GF := GF) (hG := hG) := by
  intro ws wa P γ id
  wp_start as Hws
  iunfold mvcc.isWatchStream at Hws
  iNamed Hws
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨%enx, #Henx⟩, -⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold mvcc.watchStreamInv at HR
  iNamed HR
  wp_auto
  wp_apply wp_map_lookup2 $$ [$Hcm] as Hcm
  wp_apply wp_map_lookup1 $$ [$Hwm] as Hwm
  have hdomid := Hdom id
  cases hc : CM !! id with
  | none =>
    simp only [hc, Option.isSome_none, Option.getD_none] at hdomid ⊢
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hcl]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, closed, cm, wm, CM, WM
      simp only [named]
      iframe
      iframe #
      ipureintro; exact ⟨Hdom, Hnn⟩
    iapply HΦ
    iright
    iexact Henx
  | some c =>
    obtain ⟨w, hw⟩ : ∃ w, WM !! id = some w := by
      cases h : WM !! id with
      | none => simp [hc, h] at hdomid
      | some w => exact ⟨w, rfl⟩
    have hwnn := Hnn id w hw
    ihave #Hc := Hcs $$ %id %c %w %hc %hw
    simp only [hw, Option.isSome_some, Option.getD_some]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hcl]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, closed, cm, wm, CM, WM
      simp only [named]
      iframe
      iframe #
      ipureintro; exact ⟨Hdom, Hnn⟩
    cases closed with
    | true =>
      wp_auto
      iapply HΦ
      iright
      iexact Henx
    | false =>
      wp_auto
      iunfold mvcc.cancelSpec at Hc
      wp_apply Hc as #Hwc
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
      iunfold mvcc.watchStreamInv at HR
      icases HR with ⟨%nextID', %closed', %cm', %wm', %CM', %WM', HR⟩
      simp only [named]
      icases HR with ⟨HnextID, Hclosed, Hcf, Hwf, Hcm, Hwm, %Hdom', %Hnn', #Hws', #Hcs', Hcl⟩
      wp_auto
      wp_apply wp_map_lookup1 $$ [$Hwm] as Hwm
      wp_if_destruct
      · obtain ⟨w', hw'⟩ : ∃ w', WM' !! id = some w' := by
          cases h : WM' !! id with
          | none => simp only [h, Option.getD_none] at hwnn; exact absurd rfl hwnn
          | some w' => exact ⟨w', rfl⟩
        have hweq : (WM' !! id).getD (zero_val Loc) = w' := by simp [hw']
        rw [hweq]
        wp_apply wp_mapDelete $$ [$Hcm] as Hcm
        wp_apply wp_mapDelete $$ [$Hwm] as Hwm
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hcl]
        · inext
          iunfold mvcc.watchStreamInv
          iexists nextID', closed', cm', wm', GMap.delete id CM', GMap.delete id WM'
          simp only [named]
          iframe HnextID Hclosed Hcf Hwf Hcm Hwm
          isplitr
          · ipureintro
            intro i
            simp only [GMap.lookup_delete_iff]; split
            · rfl
            · exact Hdom' i
          isplitr
          · ipureintro
            intro i w0 h
            simp only [GMap.lookup_delete_iff] at h; split at h
            · simp at h
            · exact Hnn' i w0 h
          isplitr
          · imodintro
            iintro %i %w0 %h
            simp only [GMap.lookup_delete_iff] at h
            split at h
            · simp at h
            · iapply Hws' $$ %i %w0 %h
          isplitr
          · imodintro
            iintro %i %c0 %w0 %h1 %h2
            simp only [GMap.lookup_delete_iff] at h1 h2
            split at h1
            · simp at h1
            · split at h2
              · simp at h2
              · iapply Hcs' $$ %i %c0 %w0 %h1 %h2
          cases closed' with
          | true =>
            simp only [↓reduceIte]
            iexact Hcl
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at ⊢
            icases Hcl with ⟨%L, HCR, #HL⟩
            iexists L
            iframe HCR
            imodintro
            iintro %w0 %hin
            icases HL $$ %w0 %hin with (⟨%i, %hi⟩ | #Hc0)
            · by_cases hii : id = i
              · subst hii
                rw [hw'] at hi
                cases hi
                iright
                iexact Hwc
              · ileft
                iexists i
                ipureintro
                simp only [GMap.lookup_delete_iff, hii, ite_false]
                exact hi
            · iright
              iexact Hc0
        iapply HΦ
        ileft
        ipureintro; rfl
      · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hcl]
        · inext
          iunfold mvcc.watchStreamInv
          iexists nextID', closed', cm', wm', CM', WM'
          simp only [named]
          iframe
          iframe #
          ipureintro; exact ⟨Hdom', Hnn'⟩
        iapply HΦ
        ileft
        ipureintro; rfl

end proof

end EtcdGrove
end Perennial
