/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/wait/timeList__Wait.lean`. Lean-first (no Rocq counterpart); the
request path's unit 4b.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.timeList__Wait

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

/-- An unclosed broadcast channel's owner view gives a waiter's view too. -/
theorem bcast_pending_unknown' (ch : Loc) (γ : ChanNames) (Q : IProp GF) :
    ownBroadcastChan ch γ Q .Pending ⊢
      ownBroadcastChan ch γ Q .Pending ∗ ownBroadcastChan ch γ Q .Unknown := by
  iintro H
  icases ownBroadcastChan_open _ _ _ _ $$ H with ⟨%γch, #Hint, Hd⟩
  isplitl [Hd]
  · iapply ownBroadcastChan_close _ _ _ _ γch; iframe Hint Hd
  · iapply ownBroadcastChan_close _ _ _ .Unknown γch; iframe Hint

theorem wait.timeList.Wait.wp_proof : wait.timeList.Wait.spec (GF := GF) (hG := hG) := by
  intro tl P d
  wp_start as #Htl
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
  wp_if_destruct
  · -- already triggered: `closec`
    ihave #Hcl' := Hcl
    iunfold waitClosecInit at Hcl'
    icases Hcl' with ⟨%cc, %γc, #Hcc, #Hccb⟩
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlast HM Hchs]
    · inext; iunfold timeListR; iexists last, M; iframe; iframe #
    (try wp_auto)
    iapply HΦ
    iexists iprop(True)
    isplitr
    · iunfold waitBcast; iexists γc; iexact Hccb
    iintro !> -
    iunfold waitMono at Hmono
    iapply Hmono $$ %last %d %Hif Hlastp
  wp_apply wp_map_lookup1 $$ [$HM] as HM
  cases hk : M !! d with
  | none =>
    simp only [Option.getD_none]
    wp_apply chan.wp_make1 (V := Unit) as %ch %γch ⟨#Hch, %_, Hoc⟩
    imod alloc_broadcast_chan (E := ⊤) (P d) γch ch $$ Hch Hoc with Hbc
    icases bcast_pending_unknown' _ _ _ $$ Hbc with ⟨Hbc, #Hbu⟩
    (try wp_auto)
    wp_apply wp_mapInsert $$ [$HM] as HM
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlast HM Hchs Hbc]
    · inext; iunfold timeListR; iexists last, _; iframe; iframe #
      iapply (BigSepM.bigSepM_insert (Φ := fun d ch =>
        iprop(∃ γ : ChanNames, ownBroadcastChan ch γ (P d) Broadcast.Pending)) hk).2
      iframe
    (try wp_auto)
    iapply HΦ
    iexists P d
    isplitr
    · iunfold waitBcast; iexists γch; iexact Hbu
    iintro !> H
    iexact H
  | some ch =>
    simp only [Option.getD_some]
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun d ch =>
        iprop(∃ γ : ChanNames, ownBroadcastChan ch γ (P d) Broadcast.Pending)) hk).1 $$ Hchs
      with ⟨⟨%γ, Hb⟩, Hchs⟩
    ihave #Hisch := ownBroadcastChan_is_chan _ _ _ _ $$ Hb
    ihave %Hnn := isChan_not_null _ _ _ $$ Hisch
    rw [decide_eq_false (show ¬ ch = chan.nil from Hnn)]
    wp_auto
    icases bcast_pending_unknown' _ _ _ $$ Hb with ⟨Hb, #Hbu⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlast HM Hchs Hb]
    · inext; iunfold timeListR; iexists last, M; iframe; iframe #
      iapply Hchs; iexists γ; iexact Hb
    (try wp_auto)
    iapply HΦ
    iexists P d
    isplitr
    · iunfold waitBcast; iexists γ; iexact Hbu
    iintro !> H
    iexact H

end proof

end EtcdGrove
end Perennial
