/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Demote.lean`. Lean-first (no Rocq
counterpart). (The lessor-noax stage, 2026-11-18) until then the trust boundary: `close(le.demotec)`
needs the channel's close right, which the lessor's invariant did not keep; the expiry loop's
invariant (`lessorLoopInv`) now keeps it, with the other half of `demotec`.

Under the write lock: every lease of the map `forever()` (its `leaseMeta`'s half of `expiry` and
its `expiryMu`); the fresh checkpoint heap (`lessorExtra`'s); the notifier and `demotec`'s other
half and close right from the loop's invariant for the writers' token (`lessorLoop_wtake`); the
fresh notifier; `demotec` closed if set, then `nil` (both halves); all given back, and the lock.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Demote
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__forever
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__clearScheduledLeasesCheckpoints
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__clearLeaseExpiredNotifier
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.Demote.wp_proof
    (hForever : lease.Lease.forever.spec (GF := GF) (hG := hG))
    (hClrCk : lease.lessor.clearScheduledLeasesCheckpoints.spec (GF := GF) (hG := hG))
    (hClrN : lease.lessor.clearLeaseExpiredNotifier.spec (GF := GF) (hG := hG)) :
    lease.lessor.Demote.spec (GF := GF) (hG := hG) := by
  intro lp γl
  wp_start as #Hinv
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold lessorInv at Hinv'
  icases Hinv' with ⟨%Hlp, #Hpin, #Hmu, #Hrd, #Hloop⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I, %rd0, %L, Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hsz, #Hls,
    Hx, Hhist⟩
  iunfold lessorExtra at Hx
  icases Hx with ⟨%dc, %h, %hx, %bl, Hdc, Hh, Hhq, Hcp, Hmeta, Hbl, Hwt⟩
  (try wp_auto)
  -- every lease of the map, `forever()`
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (_ : List w64) (_ : Int) =>
      iprop(∃ x : Loc, "l" ∷ l_ptr ↦ x ∗
        "Hmeta" ∷ [∗map] id ↦ l ∈ M, leaseMeta (GF := GF) id l 1)) $$ HM
  iintro %keys -
  isplitl [l Hmeta]
  · iexists _; simp only [named]; iframe
  isplitr
  · imodintro
    iintro %p %k %o ⟨-, %Ho⟩ HP
    iNamed HP
    (try wp_auto)
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun i x => leaseMeta (GF := GF) i x 1) Ho).1
      $$ Hmeta with ⟨Hm, Hmback⟩
    iunfold leaseMeta at Hm
    icases Hm with ⟨#HID, #Httl, #Hrc, Hrem, ⟨%e, Hexp⟩, #HexG⟩
    wp_apply (hForever o e) $$ [$Hpkg $Hexp $HexG] as Hexp
    ihave Hmeta := Hmback $$ [Hrem Hexp]
    · iunfold leaseMeta; iframe Hrem HID Httl Hrc HexG; iexists _; iexact Hexp
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists o; simp only [named]; iframe
  iintro HP HM
  iNamed HP
  (try wp_auto)
  -- the fresh checkpoint heap
  wp_apply (hClrCk lp h) $$ [$Hpkg $Hh] as ⟨%h', Hh, Hhq'⟩
  (try wp_auto)
  -- the notifier and `demotec`'s other half and close right, for the writers' token
  icases Hwt with ⟨%γrw, #Hprw, Hwt⟩
  iapply fupd_wp
  imod lessorLoop_wtake lp γl γrw ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hloop $Hprw $Hwt]
    with ⟨⟨%np, %dc2, HT, HD⟩, Hwback⟩
  iunfold notifierFreeT at HT
  icases HT with ⟨Hnp, -, Hdc2⟩
  icases ptsto_halves_combine _ _ _ $$ [Hdc Hdc2] with ⟨%Hdd, Hdc⟩
  · iframe
  subst Hdd
  imodintro
  wp_apply (lc := 1) (hClrN lp np) $$ [$Hpkg $Hnp] as ⟨%np', Hnp, Hnot⟩
  imod lc_fupd_elim_later $$ Hlc1 HD with HD
  -- `if le.demotec != nil { close(le.demotec); le.demotec = nil }`
  wp_join iprop(le_ptr ↦ lp ∗ lF go!"demotec" lp ↦ chan.nil) with [le Hdc HD] as ⟨le, Hdc⟩
  · (try wp_auto)
    iunfold demotecRight at HD
    icases HD with (%Hnil | Hcl)
    · exact absurd Hnil (by assumption)
    wp_apply (wp_revokec_close dc2) $$ [$Hcl]
    (try wp_auto)
    iframe
    try (ipureintro; rfl)
  (try wp_auto)
  icases ptsto_halves_split _ _ $$ Hdc with ⟨Hdc, Hdc2⟩
  iapply fupd_wp
  imod Hwback $$ [Hnp Hnot Hdc2] with Hwt
  · iexists np', chan.nil; iunfold notifierFreeT; iframe
    inext; iunfold demotecRight; ileft; ipureintro; rfl
  imodintro
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hh Hhq' Hcp Hmeta
      Hbl Hwt Hhist]
  · iframe #
    inext
    iunfold lessorMu
    iexists lm, im, M, I, rd0, L
    iframe
    iframe Hsz Hls
    isplitr
    · ipureintro; exact HL
    iunfold lessorExtra
    iexists chan.nil, h', [], bl
    iframe
    try iexists γrw
    try iframe Hprw Hwt
    try iexact Hprw
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
