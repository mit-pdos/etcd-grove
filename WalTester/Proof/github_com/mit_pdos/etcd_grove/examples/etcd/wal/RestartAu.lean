/-
The restart's WAL updates committed on the tester's invariant (W4c U5, `restartRead`): `ValidSnapshotEntries`'
and `Repair`'s (the state unchanged, over `walDirIs`), `ReadAll`'s (unchanged, over `walDiskAt` with
`ReadAll`'s newest-pair premise), and `Open`'s (the unlock position raised: both halves of the WAL state
moved, the invariant's relation re-established by the member's candidate, `tCandOk_open`).
Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__closeLemmas
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RestartOk
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSnap

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

/-! ## The newest-pair loop (pure) -/

/-- `restartRead`'s loop step: a pair whose index is at least the current one's replaces it. -/
def tNewestStep (q p : w64 × w64) : w64 × w64 := if uint.nat q.1 ≤ uint.nat p.1 then p else q

theorem walNewestPair_some_foldl (l : List (w64 × w64)) (q : w64 × w64) :
    l.foldl (fun acc p => match acc with
      | none => some p
      | some q => if uint.nat q.1 ≤ uint.nat p.1 then some p else some q) (some q) =
      some (l.foldl tNewestStep q) := by
  induction l generalizing q with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    unfold tNewestStep
    split <;> rfl

/-- **The loop computes the newest pair**: from `(0, 0)`, over a non-empty list, the Go loop's result is
`walNewestPair`'s (the first pair is always taken, its index being at least 0). -/
theorem walNewestPair_loop (l : List (w64 × w64)) (h : l ≠ []) :
    walNewestPair l = some (l.foldl tNewestStep (W64 0, W64 0)) := by
  obtain ⟨p, l', rfl⟩ := List.exists_cons_of_ne_nil h
  unfold walNewestPair
  simp only [List.foldl_cons]
  rw [show tNewestStep (W64 0, W64 0) p = p by unfold tNewestStep; simp]
  exact walNewestPair_some_foldl l' p

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- `Open`'s update of the WAL state: the unlock position raised to the open's position. -/
abbrev walOpenRaise (s : w64 × w64) (d : WalDur) : WalDur :=
  { d with unl := max d.unl (walOpenPos (d.H.map WalOpG.toM) s.1) }

/-- **`tRelW` survives appended opens** (the mark and `created` unchanged, `tPre` kept). -/
theorem tRelW_withOpens (W : WalGS GF) (area : GoString) (o : TOracle) (cd : TCand) (l : List w64) :
    tRelW (W := W) (GF := GF) area o cd ⊢ tRelW (W := W) area (tWithOpens o l) cd := by
  unfold tRelW
  rw [tWithOpens_created]
  cases o.created with
  | true =>
    simp only [ite_true, tCandMark_withOpens]
    iintro ⟨%hw, H⟩; iframe H; ipureintro; exact tCheckWf_withOpens l hw
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    iintro %h; ipureintro; exact tPre_withOpens l h

/-- **An update over the WAL directory, committed with the state unchanged** (`ValidSnapshotEntries`,
`Repair`). -/
theorem tInv_dirAu (W : WalGS GF) (e : TEnv) (γ : TGS) (od : Option WalDur) :
    TInv (W := W) e γ ∗ tWalOwn γ od ⊢
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIsI (W := W) (tWalDir e.area) 0 o }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDirIsI (W := W) (tWalDir e.area) 0 o, COMM ⌜o = od⌝ ∗ tWalOwn γ od }> := by
  iintro ⟨#Hinv, Hwo⟩
  iauintro
  unfold atomic_acc
  iunfold TInv at Hinv
  imod inv_acc (E := WalFs.walAuMask) tN_sub_walAu $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi
  iunfold TInvBody at Hi
  icases Hi with ⟨%s, %o1, %oa, %od1, Hs, %hfile, Ho1, Hwd, Hw1, #Hr1, #Ha1⟩
  ihave %hag := tWalOwn_agree γ od od1 $$ Hwo Hw1
  subst od1
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ WalFs.walAuMask \ ↑tN from LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists od
  iframe Hwd
  isplit
  · iintro Hwd
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, o1, oa, od; iframe; iframe #; ipureintro; exact hfile
    imodintro
    iframe
  · iintro Hwd
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, o1, oa, od; iframe; iframe #; ipureintro; exact hfile
    imodintro
    iframe
    ipureintro; rfl

/-- **`ReadAll`'s update, committed with the state unchanged**, given its premise on the state. -/
theorem tInv_readAu (W : WalGS GF) (e : TEnv) (γ : TGS) (d : WalDur) (P : WalDur → Prop) (hP : P d) :
    TInv (W := W) e γ ∗ tWalOwn γ (some d) ⊢
      AU <{ ∃∃ d' : WalDur, WalFs.walDiskAtI (W := W) (tWalDir e.area) 0 d' ∗ ⌜P d'⌝ }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := W) (tWalDir e.area) 0 d', COMM ⌜d' = d⌝ ∗ tWalOwn γ (some d) }> := by
  iintro ⟨#Hinv, Hwo⟩
  iauintro
  unfold atomic_acc
  iunfold TInv at Hinv
  imod inv_acc (E := WalFs.walAuMask) tN_sub_walAu $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi
  iunfold TInvBody at Hi
  icases Hi with ⟨%s, %o1, %oa, %od1, Hs, %hfile, Ho1, Hwd, Hw1, #Hr1, #Ha1⟩
  ihave %hag := tWalOwn_agree γ (some d) od1 $$ Hwo Hw1
  subst hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ WalFs.walAuMask \ ↑tN from LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  unfold WalFs.walDiskAtI
  iexists d
  iframe Hwd
  isplitr
  · ipureintro; exact hP
  isplit
  · iintro ⟨Hwd, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, o1, oa, some d; iframe; iframe #; ipureintro; exact hfile
    imodintro
    iframe
  · iintro Hwd
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, o1, oa, some d; iframe; iframe #; ipureintro; exact hfile
    imodintro
    iframe
    ipureintro; rfl

/-- **`Open`'s update, committed with the unlock position raised**: the stored oracle `o1` (no `Write`
pending) accounts for the raised state through the member's candidate `cd` (`tCandOk o1 cd` of the
raised state, `tRelW`: created with `cd`'s mark synced, or fresh up to its opens); both halves of the WAL
state move. -/
theorem tInv_openAu (W : WalGS GF) (e : TEnv) (γ : TGS) (o1 : TOracle) (cd : TCand) (d : WalDur)
    (s : w64 × w64) (hcd : cd ∈ o1.cands)
    (hok : tCandOk o1 cd (walOpenRaise s d)) :
    TInv (W := W) e γ ∗ tOrOwn γ o1 none ∗ tWalOwn γ (some d) ∗ tRelW (W := W) e.area o1 cd ⊢
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIsI (W := W) (tWalDir e.area) 0 o }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDirIsI (W := W) (tWalDir e.area) 0 (o.map (fun d =>
            { d with unl := max d.unl (walOpenPos (d.H.map WalOpG.toM) s.1) })),
          COMM ⌜o = some d⌝ ∗ tOrOwn γ o1 none ∗ tWalOwn γ (some (walOpenRaise s d)) }> := by
  iintro ⟨#Hinv, Ho, Hwo, #HrW⟩
  iauintro
  unfold atomic_acc
  iunfold TInv at Hinv
  imod inv_acc (E := WalFs.walAuMask) tN_sub_walAu $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi
  iunfold TInvBody at Hi
  icases Hi with ⟨%s0, %o2, %oa, %od1, Hs, %hfile, Ho1, Hwd, Hw1, #Hr1, #Ha1⟩
  ihave %hag := tWalOwn_agree γ (some d) od1 $$ Hwo Hw1
  subst hag
  ihave %hag2 := tOrOwn_agree γ o1 o2 none oa $$ Ho Ho1
  obtain ⟨h1, h2⟩ := hag2
  subst h2; subst o2
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ WalFs.walAuMask \ ↑tN from LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists some d
  iframe Hwd
  isplit
  · iintro Hwd
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s0, o1, none, some d; iframe; iframe #; ipureintro; exact hfile
    imodintro
    iframe
  · iintro Hwd
    imod Hclose2 with -
    iunfold tWalOwn at Hwo
    imod ghostVar_update_halves (some (walOpenRaise s d)) γ.γw _ _ $$ Hwo Hw1 with ⟨Hwo, Hw1⟩
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody
      iexists s0, o1, none, some (walOpenRaise s d)
      iframe Hs Ho1 Hw1
      isplitr
      · ipureintro; exact hfile
      isplitl [Hwd]
      · isimp only [Option.map_some] at Hwd; iexact Hwd
      isplitl
      · iapply tRelI_of_relW e.area o1 cd (walOpenRaise s d) hcd hok
        iexact HrW
      · iunfold tRelA; iempintro
    imodintro
    iframe
    isplitr
    · ipureintro; rfl
    iunfold tWalOwn; iexact Hwo

end proof

section lit
open _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal _root_.Perennial.EtcdGrove.go_etcd_io.etcd.server.v3.storage.wal WalEnc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [walpb_sem : go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

instance walSnapsAt_persistent' (ps : List Loc) (l : List (w64 × w64)) :
    Persistent (walSnapsAt (GF := GF) ps l) := by
  unfold walSnapsAt; infer_instance

instance walEntsIn_persistent' (P : WalPbIn GF) (esL : List Loc) (es : List EntryM) :
    Persistent (walEntsIn P esL es) := by
  unfold walEntsIn; infer_instance

/-- **`&walpb.Snapshot{Index: p, Term: q}` frozen** (`restartRead`'s `Open` argument): its getters read
the cells' values. As `CreateSnap.walSnapAt_lit`, with any values. -/
theorem walSnapIdTerm_lit (l pi pt : Loc) (st : google_golang_org.protobuf.internal.impl.MessageState)
    (sc : w32) (x y : w64) :
    ⊢ l ↦ (walpb.Snapshot.mk st pi pt null slice.nil sc) -∗ pi ↦ x -∗ pt ↦ y ={⊤}=∗
      walSnapIdTerm (GF := GF) l (x, y) := by
  iintro Hl Hi Ht
  ihave ⟨Hl, %Hln⟩ := typedPointsto_not_null_dup _ _ _ $$ Hl
  iStructNamed Hl
  ipersist Index
  ipersist Term
  ipersist ConfState
  ipersist Hi
  ipersist Ht
  imod inv_alloc (nroot.@"protobuf") ⊤ (iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
      (sc : w32) (us : GoSlice),
    l.[walpb.Snapshot, go!"state"] ↦ st ∗ l.[walpb.Snapshot, go!"sizeCache"] ↦ sc ∗
      l.[walpb.Snapshot, go!"unknownFields"] ↦ us ∗ us ↦* ([] : List w8))) $$ [state sizeCache unknownFields]
    with #Hinv
  · inext
    iexists st, sc, slice.nil
    iframe
    iapply ownSlice_nil
  imodintro
  iunfold walSnapIdTerm
  iexists (⟨some x, some y, none, []⟩ : WalSnapC)
  isplitl
  · iunfold walSnapRoC
    iexists pi, pt, null
    simp only [recCell, walCsOptRoC, snapHidden]
    isplitr
    · ipureintro; exact Hln
    iframe #
    ipureintro; exact ufWire_nil _
  ipureintro
  rfl

end lit

end etcd_wal
end EtcdGrove
end Perennial
