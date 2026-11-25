/-
**`member.saveSnap`'s vocabulary and update** (W4c U5, after the user's decision of 2026-11-15: the tester's
conf state is `{Voters: [1], AutoLeave: new(bool)}`, raft's canonical form). As `SavePure`/`SaveAu` for
`save`: the WAL state after the snapshot record (`tSnapD`), the appended oracle's accounting
(`tCandOk_snap1`, `tMemOk_snap1`), the last hard state unchanged (`tMemHs_snap`), `SaveSnapshot`'s update
committed on the tester's invariant (`tInv_snapAu`); the literal frozen is `walSnapAt walRaftMr` of
`absSnapMd` (`walSnapAt_litCs`: its object is `walSnapCanon`, so its encoding is the model's), short
(`absSnapMd_enc_lt`). Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SaveAu
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SnapPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Marshal

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs WalEnc

section pure
variable [GooseExts]

/-- The WAL state after the snapshot record's update. -/
def tSnapD (d : WalDur) (idx term : w64) : WalDur :=
  { d with H := d.H ++ [WalOpG.snap (absSnapMd idx term) true] }

theorem tSnapD_hist (d : WalDur) (idx term : w64) :
    (tSnapD d idx term).H.map WalOpG.toM = d.H.map WalOpG.toM ++ [absOp (tSnapOp idx term)] := by
  unfold tSnapD; rw [List.map_append, List.map_singleton]; rfl

theorem tSnapO1_hist (o : TOracle) (c : TCand) (idx term : w64) :
    tCandHist (tSnapO1 o idx term) c = tCandHist o c ++ [tSnapOp idx term] := by
  unfold tCandHist tSnapO1; simp

theorem tSnapO1_mark (o : TOracle) (c : TCand) (idx term : w64) :
    tCandMark (tSnapO1 o idx term) c = tCandMark o c := rfl

/-- **The appended oracle accounts for the WAL before the call.** -/
theorem tCandOk_snap1 {o : TOracle} {c : TCand} {d : WalDur} (hok : tMemOk o c d) {idx term : w64}
    (hi : uint.nat idx < 2 ^ 63) (ht : uint.nat term < 2 ^ 63)
    (hs : tSim ((tCandHist (tSnapO1 o idx term) c).map absOp) (tCandMark o c)) :
    tCandOk (tSnapO1 o idx term) c d := by
  obtain ⟨-, -, -, h4, h5, h6, h7, h8, h9, h10, -⟩ := hok
  refine ⟨?_, h5, h6, Nat.le_trans h7 (Nat.le_max_left _ _), h8, ?_, hs⟩
  · rw [tSnapO1_hist, h4]
    refine ⟨(tCandHist o c).length, ?_, ?_, Or.inl ?_⟩
    · unfold tCandMark tCandHist tSnapO1
      simp only [List.length_append]; omega
    · simp
    · rw [List.map_append, List.take_append_of_le_length (by simp)]
      exact (List.take_of_length_le (by simp)).symm
  · rw [tSnapO1_hist]; exact tHistWf_snoc h9 (tSnapOp_wf hi ht)

/-- **The appended oracle's candidate is the WAL after the snapshot record.** -/
theorem tMemOk_snap1 {o : TOracle} {c : TCand} {d : WalDur} (hok : tMemOk o c d) {idx term : w64}
    (hi : uint.nat idx < 2 ^ 63) (ht : uint.nat term < 2 ^ 63)
    (hs : tSim ((tCandHist (tSnapO1 o idx term) c).map absOp) (tCandMark o c)) :
    tMemOk (tSnapO1 o idx term) c (tSnapD d idx term) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hok
  refine ⟨h1, h2, h3, ?_, h5, h6, h7, h8, ?_, ?_, hs⟩
  · rw [tSnapD_hist, h4, tSnapO1_hist, List.map_append, List.map_singleton]
  · rw [tSnapO1_hist]; exact tHistWf_snoc h9 (tSnapOp_wf hi ht)
  · show uint.nat o.synced ≤ (o.since ++ [tSnapOp idx term]).length
    simp only [List.length_append, List.length_singleton]; omega

/-- **A snapshot record leaves the last hard state.** -/
theorem tMemHs_snap {o : TOracle} {d : WalDur} (hhs : tMemHs o d) (idx term : w64) :
    tMemHs (tSnapO o idx term) (tSnapD d idx term) := by
  unfold tMemHs at *
  rw [tSnapO_lastHS, tSnapD_hist, hhs]
  unfold walLastHS; rw [List.foldl_append]; rfl

/-- `absSnapMd`'s conf state is not the zero one. -/
theorem absSnapMd_cs_ne (idx term : w64) : (absSnapMd idx term).ConfState' ≠ walCsZero := by
  unfold absSnapMd walCsZero; simp

/-- **The canonical object of `absSnapMd`.** -/
theorem walSnapCanon_absSnapMd (idx term : w64) :
    walSnapCanon (absSnapMd idx term) true = ⟨some idx, some term, some ⟨[W64 1], [], [], [], some false, []⟩, []⟩ := by
  unfold walSnapCanon
  rw [if_neg (absSnapMd_cs_ne idx term)]
  rfl

/-- **The snapshot record's encoding is short.** -/
theorem absSnapMd_enc_lt (idx term : w64) : (walRaftMr.encSnap (absSnapMd idx term) true).length < 2 ^ 40 := by
  show (snapEnc (walSnapCanon (absSnapMd idx term) true)).length < 2 ^ 40
  rw [walSnapCanon_absSnapMd]
  have h1 := varintEnc_length_w64 (uint.nat idx) (by word)
  have h2 := varintEnc_length_w64 (uint.nat term) (by word)
  simp only [snapEnc, optVarintField, optBytesField, csEnc, repVarintField, Option.map_some,
    Option.map_none, List.flatMap_cons, List.flatMap_nil, List.length_append, List.append_nil] at *
  have hs : ∀ n : Nat, n < 128 → (varintEnc n).length ≤ 1 := fun n hn =>
    varintEnc_length_le 1 n (Nat.le_refl _) (by simpa using hn)
  have a1 := hs (1 * 8) (by decide)
  have a2 := hs (2 * 8) (by decide)
  have a3 := hs (3 * 8 + 2) (by decide)
  have a5 := hs (5 * 8) (by decide)
  have a6 := hs (uint.nat (W64 1)) (by simp)
  have a7 := hs (if false = true then 1 else 0) (by simp)
  have a8 := hs ((varintEnc (1 * 8)).length + (varintEnc (uint.nat (W64 1))).length +
    ((varintEnc (5 * 8)).length + (varintEnc (if false = true then 1 else 0)).length)) (by omega)
  omega

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- The appended oracle's relation to a WAL state its candidate is. -/
theorem tRelI_snap1 (W : WalGS GF) (area : GoString) (o : TOracle) (c : TCand) (d : WalDur)
    (idx term : w64) (hcr : o.created = true) (hc0 : c ∈ o.cands)
    (hc : tCandOk (tSnapO1 o idx term) c d) (hw : tCheckWf (tSnapO1 o idx term)) :
    WalFs.walSyncedLb (W := W) (tWalDir area) 0 (tCandMark o c) ∗ WalFs.walNamed (W := W) (tWalDir area) 0 ⊢
      tRelI (W := W) (GF := GF) area (tSnapO1 o idx term) (some d) := by
  iintro ⟨#Hs, #Hn⟩
  unfold tRelI
  simp only [show (tSnapO1 o idx term).created = true from hcr, ↓reduceIte]
  iexists d, c
  isplitr
  · ipureintro; exact ⟨rfl, hc0, hc, hw⟩
  rw [tSnapO1_mark]
  isplitl []
  · iexact Hs
  · iexact Hn

/-- **`SaveSnapshot`'s update, committed on the tester's invariant.** -/
theorem tInv_snapAu (W : WalGS GF) (e : TEnv) (γ : TGS) (o : TOracle) (c : TCand) (d : WalDur)
    (idx term : w64) (hok : tMemOk o c d) (hi : uint.nat idx < 2 ^ 63) (ht : uint.nat term < 2 ^ 63)
    (hs : tSim ((tCandHist (tSnapO1 o idx term) c).map absOp) (tCandMark o c)) :
    TInv (W := W) e γ ∗ tWalOwn γ (some d) ∗ tOrOwn γ (tSnapO1 o idx term) none ∗
      WalFs.walSyncedLb (W := W) (tWalDir e.area) 0 (tCandMark o c) ∗
      WalFs.walNamed (W := W) (tWalDir e.area) 0 ⊢
      AU <{ ∃∃ d' : WalDur, WalFs.walDiskAtI (W := W) (tWalDir e.area) 0 d' ∗ ⌜d'.sized = true⌝ }>
          @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := W) (tWalDir e.area) 0
            { d' with H := d'.H ++ [WalOpG.snap (absSnapMd idx term) true] },
          COMM ⌜d' = d⌝ ∗ tWalOwn γ (some (tSnapD d idx term)) ∗ tOrOwn γ (tSnapO1 o idx term) none }> := by
  iintro ⟨#Hinv, Hwo, Hoo, #Hsl, #Hnm⟩
  iauintro
  unfold atomic_acc
  iunfold TInv at Hinv
  imod inv_acc (E := WalFs.walAuMask) tN_sub_walAu $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi
  iunfold TInvBody at Hi
  icases Hi with ⟨%s, %o1, %oa, %od1, Hs, %hfile, Ho1, Hwd, Hw1, #Hr1, #Ha1⟩
  ihave %hag := tWalOwn_agree γ (some d) od1 $$ Hwo Hw1
  subst hag
  ihave %hao := tOrOwn_agree (W := W) γ (tSnapO1 o idx term) o1 none oa $$ Hoo Ho1
  obtain ⟨rfl, rfl⟩ := hao
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ WalFs.walAuMask \ ↑tN from LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  unfold WalFs.walDiskAtI
  iexists d
  iframe Hwd
  isplitr
  · ipureintro; exact hok.2.2.2.2.2.2.2.1
  isplit
  · iintro ⟨Hwd, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, tSnapO1 o idx term, none, some d; iframe; iframe #
      ipureintro; exact hfile
    imodintro
    iframe
  · iintro Hwd
    iunfold tWalOwn at Hwo
    imod ghostVar_update_halves (some (tSnapD d idx term)) γ.γw _ _ $$ Hwo Hw1 with ⟨Hwo, Hw1⟩
    have hok' := tMemOk_snap1 hok hi ht hs
    ihave %hw1 := tRelI_checkWf e.area (tSnapO1 o idx term) (some d) hok.1 $$ Hr1
    ihave #Hrel := tRelI_snap1 W e.area o c (tSnapD d idx term) idx term hok.1 hok.2.1
      (by
        have h2 := tMemOk_candOk0 hok'
        obtain ⟨h21, h22, h23, -, h25, h26, h27⟩ := h2
        exact ⟨h21, h22, h23, Nat.le_trans hok'.2.2.2.2.2.2.1 (Nat.le_max_left _ _), h25, h26, h27⟩) hw1
      $$ [Hsl Hnm]
    · isplitl []
      · iexact Hsl
      · iexact Hnm
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, tSnapO1 o idx term, none, some (tSnapD d idx term)
      unfold tSnapD
      iframe; iframe #
      isplitr
      · ipureintro; exact hfile
      simp only [tRelA]
      iempintro
    imodintro
    iframe
    isplitr
    · ipureintro; rfl
    iunfold tWalOwn; iexact Hwo

end proof

section lit
open _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal
open _root_.Perennial.go_etcd_io.raft.v3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [walpb_sem : go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]
variable [raftpb_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- **`saveSnap`'s literal frozen**: `&walpb.Snapshot{Index: p, Term: q, ConfState:
&raftpb.ConfState{Voters: []uint64{1}, AutoLeave: new(bool)}}` is `walSnapAt walRaftMr` of `absSnapMd`
with a conf state (its object `walSnapCanon (absSnapMd idx term) true`, so its encoding is the model's). -/
theorem walSnapAt_litCs (l pi pt pc pa : Loc) (sv : GoSlice)
    (st : google_golang_org.protobuf.internal.impl.MessageState) (sc : w32)
    (st2 : google_golang_org.protobuf.internal.impl.MessageState) (sc2 : w32) (idx term : w64) :
    ⊢ l ↦ (walpb.Snapshot.mk st pi pt pc slice.nil sc) -∗ pi ↦ idx -∗ pt ↦ term -∗
      pc ↦ (raftpb.ConfState.mk st2 sv slice.nil slice.nil slice.nil pa slice.nil sc2) -∗
      sv ↦* [W64 1] -∗ pa ↦ false ={⊤}=∗
      walSnapAt (GF := GF) walRaftMr l (absSnapMd idx term) true true := by
  iintro Hl Hi Ht Hc Hsv Ha
  ihave ⟨Hl, %Hln⟩ := typedPointsto_not_null_dup _ _ _ $$ Hl
  ihave ⟨Hc, %Hcn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hc
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
  iStructNamed Hc
  ipersist Voters
  ipersist Learners
  ipersist VotersOutgoing
  ipersist LearnersNext
  ipersist AutoLeave
  ipersist Ha
  ipersist Hsv
  imod inv_alloc (nroot.@"protobuf") ⊤ (iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
      (sc : w32) (us : GoSlice),
    pc.[raftpb.ConfState, go!"state"] ↦ st ∗ pc.[raftpb.ConfState, go!"sizeCache"] ↦ sc ∗
      pc.[raftpb.ConfState, go!"unknownFields"] ↦ us ∗ us ↦* ([] : List w8))) $$ [state sizeCache unknownFields]
    with #Hinv2
  · inext
    iexists st2, sc2, slice.nil
    iframe
    iapply ownSlice_nil
  ihave Hnil : (slice.nil : GoSlice) ↦* ([] : List w64) $$ []
  · iapply ownSlice_nil
  ipersist Hnil
  imodintro
  iunfold walSnapAt
  iexists walSnapCanon (absSnapMd idx term) true
  rw [walSnapCanon_absSnapMd]
  isplitl
  · iunfold walSnapRoC
    iexists pi, pt, pc
    simp only [recCell, walCsOptRoC, snapHidden]
    isplitr
    · ipureintro; exact Hln
    iframe #
    isplitr
    · iunfold walCsRoC
      iexists sv, slice.nil, slice.nil, slice.nil, pa
      simp only [recCell, walCsHidden]
      iframe #
      isplitr
      · ipureintro; exact Hcn
      ipureintro; exact ufWire_nil _
    ipureintro; exact ufWire_nil _
  ipureintro
  refine ⟨?_, rfl, rfl, rfl, ?_⟩
  · rw [← walSnapCanon_absSnapMd, walSnapCanon_model]
  · show _ = snapEnc (walSnapCanon (absSnapMd idx term) true)
    rw [walSnapCanon_absSnapMd]

end lit

end etcd_wal
end EtcdGrove
end Perennial
