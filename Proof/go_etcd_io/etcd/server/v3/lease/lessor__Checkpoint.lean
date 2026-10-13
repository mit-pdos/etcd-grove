/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Checkpoint.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Checkpoint
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__isPrimary
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__shouldPersistCheckpoints
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__persistTo
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__scheduleCheckpointIfNeeded
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.Checkpoint.wp_proof
    (hShould : lease.lessor.shouldPersistCheckpoints.spec (GF := GF) (hG := hG))
    (hPersist : lease.Lease.persistTo.spec (GF := GF) (hG := hG))
    (hPrim : lease.lessor.isPrimary.spec (GF := GF) (hG := hG))
    (hSched : lease.lessor.scheduleCheckpointIfNeeded.spec (GF := GF) (hG := hG)) :
    lease.lessor.Checkpoint.spec (GF := GF) (hG := hG) := by
  intro lp γl id rem P f Pre Q Post
  wp_start as ⟨#Hinv, #Hcfg, #Hbe, Hcs⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold lessorInv at Hinv'
  icases Hinv' with ⟨%Hlp, #Hpin, #Hmu⟩
  ihave #Hbe' := Hbe
  iunfold lessorBackend at Hbe'
  icases Hbe' with ⟨%b, #Hb, #Hbk⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I, %rd0, %L, Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hls, Hx⟩
  iunfold lessorExtra at Hx
  icases Hx with ⟨%dc, %np, %h, %hx, %cp, Hdc, Hnp, Hnot, Hh, Hhq, Hcp, Hmeta⟩
  (try wp_auto)
  wp_apply (wp_map_lookup2 LeaseID.ty (go.GoType.PointerType Lease.ty) lm M id) $$ HM as HM
  cases hM : M !! id with
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    (try wp_auto)
    ihave Hx : lessorExtra lp M 1 $$ [Hdc Hnp Hnot Hh Hhq Hcp Hmeta]
    · iunfold lessorExtra; iexists dc, np, h, hx, cp; iframe
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx]
    · iframe #
      inext
      iunfold lessorMu
      iexists lm, im, M, I, rd0, L
      iframe
      iframe Hls
      ipureintro; exact HL
    iapply HΦ
    iunfold mvcc.csContract at Hcs
    icases Hcs with ⟨HPre, -, -⟩
    isplitr
    · ipureintro; rfl
    iright; iexact HPre
  | some l =>
    simp only [Option.getD_some, Option.isSome_some, decide_true]
    (try wp_auto)
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun i x => leaseMeta (GF := GF) i x 1) hM).1 $$ Hmeta
      with ⟨Hml, Hmeta⟩
    iunfold leaseMeta at Hml
    icases Hml with ⟨#HID, ⟨%t, #Httl⟩, #Hrc, ⟨%r, Hrem⟩, Hexp, #HexG⟩
    (try wp_auto)
    wp_apply (hShould lp) $$ [$Hpkg $Hcfg] as %sp -
    wp_join iprop(le_ptr ↦ lp ∗ l_ptr ↦ l ∗ lsF go!"remainingTTL" l ↦ rem ∗ (Post ∨ Pre))
      with [le l Hrem Hcs] as ⟨le, l, Hrem, HPP⟩
    · iunfold mvcc.csContract at Hcs
      icases Hcs with ⟨HPre, -, -⟩
      iframe
    · (try wp_auto)
      wp_apply (hPersist l b P f Pre Q Post id t rem DFrac.discard DFrac.discard (DFrac.own 1))
        $$ [$Hpkg $Hbk $Hcs $HID $Httl $Hrem] as ⟨HPost, -, -, Hrem⟩
      wp_join_done
    wp_apply (hPrim lp dc (DFrac.own 1)) $$ [$Hdc] as Hdc
    wp_join iprop(le_ptr ↦ lp ∗ l_ptr ↦ l ∗ lsF go!"remainingTTL" l ↦ rem ∗ lF go!"cp" lp ↦ cp ∗
        ∃ (h' : GoSlice) (hx' : List (Loc × w64)), lF go!"leaseCheckpointHeap" lp ↦ h' ∗
          queueAt h' hx' 1)
      with [le l Hrem Hcp Hh Hhq] as ⟨le, l, Hrem, Hcp, %h', %hx', Hh, Hhq⟩
    · (try wp_auto)
      wp_apply (hSched lp l cp h hx rem t (DFrac.own 1) (DFrac.own 1) DFrac.discard)
        $$ [$Hpkg $Hcfg $Hcp $Hh $Hhq $Hrem $Httl] as ⟨Hcp, ⟨%h', %hx', Hh, Hhq⟩, Hrem, -⟩
      wp_join_done
    (try wp_auto)
    ihave Hmeta := Hmeta $$ [Hrem Hexp]
    · iunfold leaseMeta
      iframe HID HexG
      isplitr
      · iexists t; iexact Httl
      iframe Hrc
      isplitl [Hrem]
      · iexists _; iexact Hrem
      iexact Hexp
    ihave Hx : lessorExtra lp M 1 $$ [Hdc Hnp Hnot Hh Hhq Hcp Hmeta]
    · iunfold lessorExtra; iexists dc, np, h', hx', cp; iframe
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx]
    · iframe #
      inext
      iunfold lessorMu
      iexists lm, im, M, I, rd0, L
      iframe
      iframe Hls
      ipureintro; exact HL
    iapply HΦ
    iframe
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
