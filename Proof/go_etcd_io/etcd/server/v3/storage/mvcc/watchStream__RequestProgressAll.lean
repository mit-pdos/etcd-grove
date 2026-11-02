/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__RequestProgressAll
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

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

theorem mvcc.watchStream.RequestProgressAll.wp_proof :
    mvcc.watchStream.RequestProgressAll.spec (GF := GF) (hG := hG) := by
  intro ws wa P γ
  wp_start as ⟨Hws, #Hpf, HPR⟩
  iunfold mvcc.isWatchStream at Hws
  iNamed Hws
  irevert Hpf; rw [Hγc.2.1]; iintro #Hpf
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold mvcc.isWatchable at Hwable
  icases Hwable with ⟨%wi, %hwa, #Hwatch, #Hprog, #HprogAll, #Hrev⟩
  subst hwa
  iunfold mvcc.watchStreamInv at HR
  iNamed HR
  wp_auto
  -- what the store is lent (K1b): open, the close right with the registered watchers, each in the
  -- map or cancelled for its reason; closed, every watcher of the map cancelled
  ihave #Hws2 : iprop(□ ∀ (id : w64) (w : Loc), ⌜WM !! id = some w⌝ -∗ P.IW w ∗ P.OC w γc) $$ []
  · iintro !> %id %w %h
    icases Hws $$ %id %w %h with ⟨#H1, #H2, -⟩
    iframe H1 H2
  cases closed with
  | true =>
    simp only [↓reduceIte]
    icases Hcl with ⟨Hop, #Hall⟩
    ihave #Hpa := HprogAll $$ %wm %(DFrac.own 1) %WM %γc %false %ch %([] : List Loc)
    wp_apply Hpa $$ [$Hwm $Hws2 $Hpf $HPR]
      as %b ⟨Hwm, -, HPR⟩
    · iunfold mvcc.progCompl
      simp only [Bool.false_eq_true, ↓reduceIte]
      iintro !> %id %w %h
      iapply Hall $$ %id %w %h
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hop]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, true, cm, wm, CM, WM
      simp only [named, ↓reduceIte]
      iframe
      iframe #
      ipureintro; exact ⟨Hdom, Hnn⟩
    iapply HΦ
    iframe HPR
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hcl with ⟨%L, HCR, #HL, %Hcnt⟩
    ihave #Hpa := HprogAll $$ %wm %(DFrac.own 1) %WM %γc %true %ch %L
    wp_apply Hpa $$ [$Hwm $Hws2 $Hpf $HPR HCR]
      as %b ⟨Hwm, HPC, HPR⟩
    · iunfold mvcc.progCompl
      simp only [↓reduceIte]
      iframe HCR HL
    iunfold mvcc.progCompl at HPC
    simp only [↓reduceIte]
    icases HPC with ⟨HCR, -⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids HCR]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, false, cm, wm, CM, WM
      simp only [named, Bool.false_eq_true, ↓reduceIte]
      iframe
      iframe #
      ipureintro; exact ⟨Hdom, Hnn, Hcnt⟩
    iapply HΦ
    iframe HPR

/-- **The candidate `RequestProgressAll`** (`specC`): `spec`'s, the progress fact the stream's
(`True`), the watchable store's reader borrowed from the readers' pool for the thread token. -/
theorem mvcc.watchStream.RequestProgressAll.wp_proofC :
    mvcc.watchStream.RequestProgressAll.specC (GF := GF) (hG := hG) := by
  intro st γ ι
  wp_start as ⟨#Hstr, Htt⟩
  iunfold mvcc.isMvccWatchStream at Hstr
  iunfold mvcc.isMvccWatchStreamI at Hstr
  icases Hstr with ⟨%Hn, #Hws, -, -, -, #Hpr0, -, -, #Hwm⟩
  obtain ⟨-, hw, -⟩ := Hn
  iunfold mvcc.isWatchableMvccI at Hwm
  icases Hwm with ⟨-, %s, -, #Hmv⟩
  ihave %Hsl := mvcc.isMvccI_loc s γ $$ Hmv
  ihave #Hpf : mvcc.progFact (GF := GF) ι.o.prog $$ []
  · iunfold mvcc.progFact; iexists iprop(True); iframe Hpr0; iintro !>; itrivial
  generalize (interface.mkOk (go.GoType.PointerType watchableStore.ty) #γ.wl : GoInterface) = wa
  iunfold mvcc.isWatchStream at Hws
  iNamed Hws
  irevert Hpf; rw [Hγc.2.1]; iintro #Hpf
  wp_auto_lc 1
  imod mvcc.mvccBorrowW s γ hw $$ [$Hlc1 $Hmv $Htt] with ⟨HPR, Hback⟩
  ihave HPR : (mvcc.storeWatchParams (GF := GF) γ.wl γ.sl γ.ws).R $$ [HPR]
  · simp only [mvcc.storeWatchParams]; rw [Hsl]; iexact HPR
  generalize hP : (mvcc.storeWatchParams (GF := GF) γ.wl γ.sl γ.ws) = P
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold mvcc.isWatchable at Hwable
  icases Hwable with ⟨%wi, %hwa, #Hwatch, #Hprog, #HprogAll, #Hrev⟩
  subst hwa
  iunfold mvcc.watchStreamInv at HR
  iNamed HR
  wp_auto
  -- what the store is lent (K1b): open, the close right with the registered watchers, each in the
  -- map or cancelled for its reason; closed, every watcher of the map cancelled
  ihave #Hws2 : iprop(□ ∀ (id : w64) (w : Loc), ⌜WM !! id = some w⌝ -∗ P.IW w ∗ P.OC w γc) $$ []
  · iintro !> %id %w %h
    icases Hws $$ %id %w %h with ⟨#H1, #H2, -⟩
    iframe H1 H2
  cases closed with
  | true =>
    simp only [↓reduceIte]
    icases Hcl with ⟨Hop, #Hall⟩
    ihave #Hpa := HprogAll $$ %wm %(DFrac.own 1) %WM %γc %false %ch %([] : List Loc)
    wp_apply Hpa $$ [$Hwm $Hws2 $Hpf $HPR]
      as %b ⟨Hwm, -, HPR⟩
    · iunfold mvcc.progCompl
      simp only [Bool.false_eq_true, ↓reduceIte]
      iintro !> %id %w %h
      iapply Hall $$ %id %w %h
    iapply wp_fupd
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hop]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, true, cm, wm, CM, WM
      simp only [named, ↓reduceIte]
      iframe
      iframe #
      ipureintro; exact ⟨Hdom, Hnn⟩
    imod Hback $$ [HPR] with Htt
    · subst hP; rw [← Hsl]; simp only [mvcc.storeWatchParams]; iexact HPR
    imodintro
    (try wp_auto)
    iapply HΦ
    iframe Htt
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hcl with ⟨%L, HCR, #HL, %Hcnt⟩
    ihave #Hpa := HprogAll $$ %wm %(DFrac.own 1) %WM %γc %true %ch %L
    wp_apply Hpa $$ [$Hwm $Hws2 $Hpf $HPR HCR]
      as %b ⟨Hwm, HPC, HPR⟩
    · iunfold mvcc.progCompl
      simp only [↓reduceIte]
      iframe HCR HL
    iunfold mvcc.progCompl at HPC
    simp only [↓reduceIte]
    icases HPC with ⟨HCR, -⟩
    iapply wp_fupd
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids HCR]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, false, cm, wm, CM, WM
      simp only [named, Bool.false_eq_true, ↓reduceIte]
      iframe
      iframe #
      ipureintro; exact ⟨Hdom, Hnn, Hcnt⟩
    imod Hback $$ [HPR] with Htt
    · subst hP; rw [← Hsl]; simp only [mvcc.storeWatchParams]; iexact HPR
    imodintro
    (try wp_auto)
    iapply HΦ
    iframe Htt

end proof

end EtcdGrove
end Perennial
