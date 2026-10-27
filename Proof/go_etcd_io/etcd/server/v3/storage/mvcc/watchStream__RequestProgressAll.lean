/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__RequestProgressAll

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

end proof

end EtcdGrove
end Perennial
