/-
Proof of the spec of the same name: `WatchStream.Cancel.contract` at `*watchStream` (stage 2 of the
mvcc API, 2026-11-05). Lean-first (no Rocq counterpart).

The update fires at the first check, under the stream's lock, with the channel's invariant open
(`Api/StreamHandle.cancel_fire`: the cancel appended to the stream's history; for a watcher of the
client's state, the cancel's tokens). The stream's fields against the client's state (`wsRel`)
give the result: a cancel closure of an open stream is a watcher's, and a live watcher of an open
stream has its closure. The second critical section drops the closure of an id the stream records
cancelled (`idCancelled`), its watcher cancelled with the history's token (`cancelledFor`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Cancel
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamHandle

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchStream.Cancel.wp_proof :
    mvcc.watchStream.Cancel.spec (GF := GF) (hG := hG) := by
  intro w γ ι id Q
  wp_start as ⟨Hws, Hau⟩
  icases mvcc.api.isMvccWatchStream_open w γ ι $$ Hws with
    ⟨%γw, %γc, %s, %st, %γo, %hι, #Hinv, #Hws, -, -, -⟩
  obtain ⟨hι, hγ⟩ := hι
  generalize hch : (ι : api.WsAbs).ch = ch at hι
  have hι' : ι = (mvcc.wsAbsOf γw ch γc : api.WsAbs) := hι
  subst hι'
  have hγ' : γ = (γw.st : api.MvccName) := hγ.symm
  subst hγ'
  iunfold mvcc.isWatchStreamAt at Hws
  iNamed Hws
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨%enx, #Henx⟩, -⟩
  wp_auto_lc 1
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold mvcc.watchStreamInv at HR
  iNamed HR
  icases Hacl with ⟨%lm, %CS, Hm, Hcsl, %Hrel⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ [$Hcm] as Hcm
  wp_apply wp_map_lookup1 $$ [$Hwm] as Hwm
  -- the update, at the first check
  iapply fupd_wp
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑mvcc.watchN) $$ Hlc1 Hi with Hi
  imod mvcc.api.cancel_fire γw ch γc γo id Q nextID closed CM CS lm Hrel $$ [$Hi $Hm $Hcsl $Hau]
    with ⟨Hi, %lm', %CS', %S, Hm, Hcsl, HQ, %Hrels, Htoks⟩
  obtain ⟨hrelS, hrel'⟩ := Hrels
  obtain ⟨hScl, -, hCMS, hlive, -⟩ := hrelS
  imod Hclose $$ [Hi] with -
  · inext; iexact Hi
  imodintro
  have hdomid := Hdom id
  cases hc : CM !! id with
  | none =>
    simp only [hc, Option.isSome_none, Option.getD_none] at hdomid ⊢
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hm Hcsl Hcl]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, closed, cm, wm, CM, WM
      simp only [named]
      iframe HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hcl
      iframe #
      isplitr
      · ipureintro; exact Hdom
      isplitr
      · ipureintro; exact Hnn
      iexists lm', CS'
      iframe Hm Hcsl
      ipureintro; exact hrel'
    iapply HΦ
    iexists S
    iframe HQ
    iright
    iframe Henx
    ipureintro
    intro w0 hw0 hl
    cases hcl : closed
    · have := hlive id w0 hw0 hl hcl; rw [hc] at this; cases this
    · rw [hScl, hcl]
  | some c =>
    obtain ⟨w0, hw⟩ : ∃ w, WM !! id = some w := by
      cases h : WM !! id with
      | none => simp [hc, h] at hdomid
      | some w => exact ⟨w, rfl⟩
    have hwnn := Hnn id w0 hw
    ihave #Hc := Hcs $$ %id %c %w0 %hc %hw
    simp only [hw, Option.isSome_some, Option.getD_some]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hm Hcsl Hcl]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, closed, cm, wm, CM, WM
      simp only [named]
      iframe HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hcl
      iframe #
      isplitr
      · ipureintro; exact Hdom
      isplitr
      · ipureintro; exact Hnn
      iexists lm', CS'
      iframe Hm Hcsl
      ipureintro; exact hrel'
    cases closed with
    | true =>
      wp_auto
      iapply HΦ
      iexists S
      iframe HQ
      iright
      iframe Henx
      ipureintro
      intro _ _ _; exact hScl
    | false =>
      have hSome : (S.ws !! id).isSome := hCMS id (by rw [hc]; rfl)
      icases Htoks with (%hnone | ⟨#Hctok, #Hcan⟩)
      · rw [hnone] at hSome; cases hSome
      wp_auto
      iunfold mvcc.cancelSpec at Hc
      wp_apply Hc as #Hwc
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
      iunfold mvcc.watchStreamInv at HR
      icases HR with ⟨%nextID', %closed', %cm', %wm', %CM', %WM', HR⟩
      simp only [named]
      icases HR with ⟨HnextID, Hclosed, Hcf, Hwf, Hcm, Hwm, %Hdom', %Hnn', #Hws', #Hcs', Hids,
        ⟨%lm'', %CS'', Hm, Hcsl, %Hrel''⟩, Hcl⟩
      -- the id is recorded cancelled
      iunfold mvcc.idCancelled at Hcan
      icases Hcan with ⟨%lc, #Hlb, %hin⟩
      ihave %Hpre := mono_list_auth_lb_valid _ _ _ _ $$ Hcsl Hlb
      have hinCS : id ∈ CS'' := Hpre.2.subset hin
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
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hm Hcsl Hcl]
        · inext
          iunfold mvcc.watchStreamInv
          iexists nextID', closed', cm', wm', GMap.delete id CM', GMap.delete id WM'
          simp only [named]
          iframe HnextID Hclosed Hcf Hwf Hcm Hwm Hids
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
          isplitl [Hm Hcsl]
          · iexists lm'', CS''
            iframe Hm Hcsl
            ipureintro
            intro d
            exact mvcc.wsRel_delete (Hrel'' d) id hinCS
          cases closed' with
          | true =>
            simp only [↓reduceIte]
            icases Hcl with #Hall
            iintro !> %i %w0 %h
            simp only [GMap.lookup_delete_iff] at h
            split at h
            · simp at h
            · iapply Hall $$ %i %w0 %h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at ⊢
            icases Hcl with ⟨%L, HCR, #HL, %Hcnt⟩
            iexists L
            iframe HCR
            isplitr
            · imodintro
              iintro %w0 %hin
              icases HL $$ %w0 %hin with (⟨%i, %hi⟩ | #Hc0)
              · by_cases hii : id = i
                · subst hii
                  rw [hw'] at hi
                  cases hi
                  iright
                  iunfold mvcc.cancelledFor
                  simp only [mvcc.storeWatchParams]
                  iframe Hwc
                  icases Hws' $$ %id %w' %hw' with ⟨-, -, %r0, %fcs0, %lo0, #Hiwf, %hrid⟩
                  iexists r0, fcs0, lo0
                  iframe Hiwf
                  rw [hrid]
                  iexact Hctok
                · ileft
                  iexists i
                  ipureintro
                  simp only [GMap.lookup_delete_iff, hii, ite_false]
                  exact hi
              · iright
                iexact Hc0
            ipureintro
            exact ⟨by have := mvcc.aboveCnt_delete nextID' id WM'; omega, Hcnt.2⟩
        iapply HΦ
        iexists S
        iframe HQ
        ileft
        ipureintro; exact ⟨rfl, hSome, hScl⟩
      · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hm Hcsl Hcl]
        · inext
          iunfold mvcc.watchStreamInv
          iexists nextID', closed', cm', wm', CM', WM'
          simp only [named]
          iframe HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hcl
          iframe #
          isplitr
          · ipureintro; exact Hdom'
          isplitr
          · ipureintro; exact Hnn'
          iexists lm'', CS''
          iframe Hm Hcsl
          ipureintro; exact Hrel''
        iapply HΦ
        iexists S
        iframe HQ
        ileft
        ipureintro; exact ⟨rfl, hSome, hScl⟩

end proof

end EtcdGrove
end Perennial
