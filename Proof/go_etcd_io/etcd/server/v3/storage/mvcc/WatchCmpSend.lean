/-
**The compaction response's send** (watches across a compaction, W1, 2026-11-01;
`notes/watch-compaction-plan.md`, D4): `chooseAll` sends a watcher whose next revision was
compacted `WatchResponse{WatchID: w.id, CompactRevision: compactRev}` on its channel without
blocking (`watcher_group.go:255-262`). The channel's invariant records it as a sent delivery of no
events (`entries_deliver`), a response that covers nothing and claims no revision (`respCov`'s
compaction arm).

* `cmpSendPre γ w ch ql`: what the send needs of the watcher `w` (channel `ch`): its names, fixed
  fields and filters, its channel's invariant, and its liveness fragment at `ql` (a live watcher's
  channel is open).
* `cmp_send_inner`: the send's update (`nonblockingSendAuInner`), with the liveness back.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchSendLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

namespace mvcc

/-- **What the compaction response's send needs of the watcher `w`** (its channel `ch`): its
names, fixed fields and filters, its channel's invariant, and its liveness fragment at `ql`. -/
def cmpSendPre (γ : WsNames) (w : Loc) (ch : Loc) (ql : Qp) : IProp GF :=
  iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice),
    watcherMeta γ w γw ∗ watcherFixed w r fcs ∗ filtersOk fcs ∗ watcherChan γ w γw ch ∗
    dghostVar γw.live (DFrac.own ql) true)

/-- The compaction response's model: `w`'s, its id, no events, no revision, no coverage, at the
channel's next position, the compaction revision `c`. -/
def cmpResp (w : Loc) (id : w64) (k : Nat) (c : w64) : RespM :=
  { w := w, id := id, evs := [], rev := W64 0, cov := [], regs := [], idx := k, compactRev := c }

/-- **The compaction response's send** (see the file header): the update of a non-blocking send of
`v` (`WatchResponse{WatchID: r.id, CompactRevision: c}`, `c > 0`, permitted: `crevPermAt`, C3's
store law) on `w`'s channel; with the liveness fragment back, the continuation `Φ`. -/
theorem cmp_send_inner (γ : WsNames) (w : Loc) (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice)
    (ch : Loc) (ql : Qp) (v : WatchResponse) (c : w64)
    (hv : v.WatchID' = r.id ∧ v.Revision' = W64 0 ∧ v.CompactRevision' = c ∧ v.Events' = slice.nil)
    (hcp : 0 < sint.Z c) (Φ : IProp GF) :
    crevPermAt γ.st (sint.Z c) ∗ watcherMeta γ w γw ∗ watcherFixed w r fcs ∗ filtersOk fcs ∗ watcherChan γ w γw ch ∗
      dghostVar γw.live (DFrac.own ql) true ∗ (dghostVar γw.live (DFrac.own ql) true -∗ Φ) ⊢
      nonblockingSendAuInner γw.wc.ch v Φ := by
  have hc : c ≠ W64 0 := by intro h; rw [h] at hcp; exact absurd hcp (by decide)
  iintro ⟨#Hperm, #Hmeta, #Hfix, #Hfok, #Hwc, Hlive, HΦ⟩
  iunfold watcherChan at Hwc
  icases Hwc with ⟨#Hisch, #Hinv, #Hregw⟩
  iunfold filtersOk at Hfok
  icases Hfok with ⟨%fs, #Hfi⟩
  unfold nonblockingSendAuInner
  iinv Hinv with Hi Hclose
  all_goals try exact CoPset.subseteq_top
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold watchChanInv at Hi
  iNamed Hi
  ihave %Hwl := reg_mem _ _ _ $$ Hreg Hregw
  -- the response's id is `w`'s own, not `-1` (its registration)
  ihave %Hrid : ⌜r.id ≠ W64 (-1)⌝ $$ []
  · icases BigSepL.bigSepL_mem_acc Hwl $$ Hrf with ⟨Hrw, -⟩
    iunfold chanRegFact at Hrw
    icases Hrw with ⟨%rr, %fcs', #Hf', -, %Hrr⟩
    ihave %Hag := watcherFixed_agree w r rr fcs fcs' $$ [$Hfix $Hf']
    ipureintro; rw [Hag.1]; exact Hrr
  -- the response's coverage: none, its compaction arm
  ihave #Hrc : respCov γ γw.wc sent (cmpResp w r.id sent.length c) $$ []
  · iunfold respCov
    isplitr
    · iintro !> %w' %hw'; simp [cmpResp] at hw'
    isplitr
    · iunfold respCompl; ileft; ipureintro; exact Hrid
    isplitr
    · ipureintro; intro _ h; exact absurd h hc
    iunfold respRev
    isplitl []
    · iright; iright; ipureintro; exact ⟨hc, rfl⟩
    iunfold cmpPermOf; simp only [cmpResp]; iright; iframe Hperm; ipureintro; exact hcp
  iexists s
  iframe Hch
  have hpre := Hpre.length_le
  rcases s with (_ | ⟨b0, bs⟩) | _ | _ | _ | _ | _ | (_ | ⟨b0, bs⟩)
  all_goals dsimp only
  all_goals first | itrivial | skip
  case Closed.nil | Closed.cons =>
    irevert Hws; simp only [EtcdGrove.chanIsClosed]; iintro Hws
    ihave Hw := (BigSepL.bigSepL_mem (Φ := fun x => chanWatcher γ γw.wc true sent x) Hwl) $$ Hws
    iapply chanWatcher_closed_live γ γw.wc sent w γw ql $$ Hmeta Hlive Hw
  all_goals
    iintro Hchan
    ihave #Hnil : (slice.nil ↦*□ ([] : List Loc) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave #Hresp : respIs v (cmpResp w r.id sent.length c) $$ []
    · iunfold respIs
      isplitr
      · ipureintro; exact ⟨hv.1, hv.2.1, hv.2.2.1⟩
      iexists []
      rw [hv.2.2.2]
      iframe Hnil
      simp only [cmpResp, List.zip_nil_left, List.length_nil]
      isplitr
      · ipureintro; trivial
      iapply BigSepL.bigSepL_nil.2; itrivial
    ihave #Hrok : respOk (cmpResp w r.id sent.length c) $$ []
    · iunfold respOk
      simp only [cmpResp]
      isplitr
      · ipureintro; intro ev hev; simp at hev
      iexists r, fcs
      iframe Hfix
      ipureintro
      simp [Hrid]
    imod entries_deliver γ γw.wc _ sent L w γw r fcs fs [] 0 [] [] (cmpResp w r.id sent.length c)
      Hnd.1 Hwl (by rfl) rfl rfl $$ Hmeta Hfix Hfi [] Hws with ⟨-, Hws⟩
    · simp only [↓reduceIte]; itrivial
    have hs2 : sent ++ (if Deliv.sent (([] : List EvM), ([] : List EvM)) then
        [cmpResp w r.id sent.length c] else []) = sent ++ [cmpResp w r.id sent.length c] := by
      simp [Deliv.sent]
    irevert Hws; rw [hs2]; iintro Hws
    ihave #Hvs' := respsIs_snoc vs sent recv.length hpre _ _ $$ [$Hvs $Hresp]
    imod sentAuth_snoc γ γw.wc sent L (cmpResp w r.id sent.length c)
      (fun h => absurd h Hrid) rfl $$ Hsentl Hrc with Hsentl
    imod Hmask with -
    imod Hclose $$ [Hchan Hrecv Hregl Hcl Hreg Hws Hsentl] with -
    · inext
      iunfold watchChanInv
      iexists _, sent ++ [cmpResp w r.id sent.length c], recv, vs ++ [v], L
      simp only [named]
      isplitl [Hchan]
      · iexact Hchan
      isplitl [Hrecv]
      · iexact Hrecv
      isplitr
      · ipureintro; exact Hpre.trans (List.prefix_append _ _)
      isplitr
      · ipureintro; simp_all [EtcdGrove.chanInflight]
      isplitr
      · iexact Hvs'
      isplitr
      · iintro !>
        iapply BigSepL.bigSepL_snoc.2
        iframe Hok Hrok
      isplitl [Hregl]
      · iexact Hregl
      isplitl [Hcl]
      · iapply closedFlag_congr (by simp [EtcdGrove.chanIsClosed]) $$ Hcl
      isplitl [Hreg]
      · iexact Hreg
      isplitr
      · ipureintro
        refine ⟨Hnd.1, fun x hx => ?_⟩
        rcases List.mem_append.1 hx with h | h
        · exact Hnd.2 x h
        · simp only [List.mem_singleton] at h; subst h; exact Hwl
      isplitr
      · iexact Hrf
      isplitr
      · iintro !>
        iapply BigSepL.bigSepL_snoc.2
        iframe Hpf
        iintro %h; exact absurd h Hrid
      isplitl [Hsentl]
      · iexact Hsentl
      iapply chanWatchers_congr γ γw.wc (by simp [EtcdGrove.chanIsClosed]) $$ Hws
    imodintro
    iapply HΦ $$ Hlive

end mvcc

end defs

end EtcdGrove
end Perennial
