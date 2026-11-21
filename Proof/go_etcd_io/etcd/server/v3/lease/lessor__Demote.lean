/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Demote.lean` (prove-ps2-lease, 2026-11-21;
an axiom until then, for want of `demotec`'s close right). Under the write lock: every lease's
expiry set to `forever` (the lessor's half of it, `leaseMeta`), a fresh checkpoint heap and expiry
notifier, and, if `demotec` is set, its close (`demote_close`: the token of the current channel
out of the lessor's `demotec` invariant, `demoteOuter`, through the ghost variable the lock holds
the other half of, `demoteTie`) and `demotec = nil`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Demote
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__forever
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__clearScheduledLeasesCheckpoints
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__clearLeaseExpiredNotifier
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas
public import Proof.go_etcd_io.etcd.server.v3.lease.NotifCell

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

/-- **`close(dc)` of the lessor's current `demotec`** `dc` (not nil), with the lock's half of its
ghost variable `γd`: the token out of `demoteOuter` (the variable set to `nil` there), then the
close, which puts the token into the channel's invariant. -/
theorem demote_close {ty : go.GoType} {dir : go.ChanDir}
    [ty ↓u go.ChannelType dir (go.StructType [])] (dc : GoChan) (γd : GName) (hdc : dc ≠ chan.nil) :
    {{ £ 1 ∗ ghostVar (GF := GF) γd (1 : Qp).half dc ∗ inv demoteOuterN (demoteOuter γd) }}
      (App (Val #(functions go.close [ty])) (Val #dc))
    {{ RET #(); ghostVar γd (1 : Qp).half chan.nil }} := by
  iintro %Φ ⟨Hlc, Hv, #Hout⟩ HΦ
  iapply fupd_wp
  iinv Hout with Ho Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑demoteOuterN) $$ Hlc Ho with Ho
  iunfold demoteOuter at Ho
  icases Ho with ⟨%dc', Hv', Hor⟩
  ihave %Heq := ghostVar_agree _ _ _ _ _ $$ Hv Hv'
  subst Heq
  icases Hor with (%Hnil | ⟨%γt, #Hrecv, Htok⟩)
  · exact absurd Hnil hdc
  imod ghostVar_update_halves chan.nil _ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv'] with -
  · inext; iunfold demoteOuter; iexists chan.nil; iframe Hv'; ileft; ipureintro; rfl
  imodintro
  iunfold onceRecv at Hrecv
  icases Hrecv with ⟨%γc, #Hch, #Hci⟩
  iapply chan.wp_close (ct := ty) (V := Unit) dc γc $$ Hch
  iintro _
  unfold closeAu
  iapply ncfupd_of_fupd
  iinv Hci with Hi Hclose2
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold onceChanInv at Hi
  icases Hi with ⟨%st, Hc, Hs⟩
  iexists st
  iframe Hc
  rcases st with _ | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iintro Hc
    imod Hmask with -
    imod Hclose2 $$ [Hc Htok] with -
    · inext; iunfold onceChanInv; iexists .Closed []; dsimp only; iframe
    imodintro
    iapply HΦ $$ Hv
  case Closed.nil =>
    iapply (token_exclusive γt) $$ Htok Hs
  all_goals first | itrivial | (iexfalso; iexact Hs)

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
  icases Hinv' with ⟨%Hlp, #Hpin, #Hmu, #Hrdi⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I, %rd0, %L, Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hsz, #Hls, Hx, Hhist⟩
  iunfold lessorExtra at Hx
  icases Hx with ⟨%dc, %np, %h, %hx, %bl, Hdc, Hnp, Hnot, Hh, Hhq, Hcp, Hmeta, Hbl, Hdt, #Hstr⟩
  imod (notif_wopen lp γl np ⊤ (fun _ _ => CoPset.mem_full)) $$ [$Hnp $Hnot] with ⟨Hnp, Hnot, Hntk⟩
  (try wp_auto)
  -- every lease's expiry to `forever`
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (_keys : List w64) (_p : Int) =>
      iprop(∃ x : Loc, "l" ∷ l_ptr ↦ x ∗
        "Hmeta" ∷ [∗map] id ↦ l ∈ M, leaseMeta (GF := GF) id l 1)) $$ HM
  iintro %keys -
  isplitl [l Hmeta]
  · iexists _; iframe
  isplitr
  · imodintro
    iintro %p %k %o ⟨-, %Ho⟩ HP
    iNamed HP
    wp_auto
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun i x => leaseMeta (GF := GF) i x 1) Ho).1 $$ Hmeta
      with ⟨Hml, Hmeta⟩
    iunfold leaseMeta at Hml
    icases Hml with ⟨#HID, #Httl, #Hrc, Hrem, ⟨%e, Hexp⟩, #HexG⟩
    wp_apply (hForever o e) $$ [$Hexp $HexG] as Hexp
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists o
    iframe
    iapply Hmeta
    iunfold leaseMeta
    iframe HID Httl Hrc Hrem HexG
    iexists _; iexact Hexp
  iintro HP HM
  iNamed HP
  wp_auto
  wp_apply (hClrCk lp h) $$ [$Hh] as ⟨%h', Hh, Hhq⟩
  (try wp_auto)
  wp_apply (hClrN lp np) $$ [$Hnp] as ⟨%np', Hnp, Hnot⟩
  (try wp_auto)
  iunfold demoteTie at Hdt
  icases Hdt with ⟨%γr, #Hpr, Hgv, #Hout⟩
  by_cases hdc : dc = chan.nil
  · subst hdc
    simp only [decide_true, Bool.not_true]
    (try wp_auto)
    imod (notif_wclose lp γl np' ⊤ (fun _ _ => CoPset.mem_full)) $$ [$Hnp $Hnot $Hntk] with ⟨Hnp, Hnot⟩
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hnp Hnot Hh Hhq Hcp
        Hmeta Hbl Hgv Hhist]
    · iframe #
      inext
      iunfold lessorMu
      iexists lm, im, M, I, rd0, L
      iframe
      iframe Hsz Hls
      isplitr
      · ipureintro; exact HL
      iunfold lessorExtra
      iexists chan.nil, np', h', [], bl
      iframe
      iframe Hstr
      iunfold demoteTie
      iexists γr
      iframe Hpr Hout Hgv
    iapply HΦ
    itrivial
  · simp only [hdc, decide_false, Bool.not_false]
    wp_auto_lc 1
    wp_apply (demote_close dc γr.2.2.2.2.2.2.1 hdc) $$ [$Hlc1 $Hgv $Hout] as Hgv
    (try wp_auto)
    imod (notif_wclose lp γl np' ⊤ (fun _ _ => CoPset.mem_full)) $$ [$Hnp $Hnot $Hntk] with ⟨Hnp, Hnot⟩
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hnp Hnot Hh Hhq Hcp
        Hmeta Hbl Hgv Hhist]
    · iframe #
      inext
      iunfold lessorMu
      iexists lm, im, M, I, rd0, L
      iframe
      iframe Hsz Hls
      isplitr
      · ipureintro; exact HL
      iunfold lessorExtra
      iexists chan.nil, np', h', [], bl
      iframe
      iframe Hstr
      iunfold demoteTie
      iexists γr
      iframe Hpr Hout Hgv
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
