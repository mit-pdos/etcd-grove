/-
# `persist`'s write: `durable.Write`'s atomic updates over the file's invariant (2026-11-22)

`notes/kvnet-part.md`, "`persist`" (decision C). `kd_writeAU` is the first atomic update `durable.Write`
takes, over the replica's file invariant (`kdFileInvK`), for the image `M`, with what the writer holds
(`kdWriter ph.fl S o`, under `dmu`) and the pending batch, if any (`kdPendIn`):

* at the rename, the file enters the write's window: `cur` is `M`'s encoding, `alt` the old contents.
  The old contents hold `S`. The new ones hold `S` too (`pb = none`) or the batch's state `S2`, whose
  *enter* (`readyEnter`, with its saved results) moves into the invariant;
* at the directory's sync (`durWriteSync`, with the crash token and a later credit), the window
  closes. A batch in the invariant is entered there with the caller's `nodeRunning`: the durable
  state moves to `S2`, and its results are left at `γb` (`kdPendOut`, what `dmu`'s `fired` phase holds).
  The writer then holds `kdWriter ph.fl S' (some M)`.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- The durable state after a write with the pending batch `pb`. -/
def pbTarget (S : RaftState) : Option (GName × RaftState × Qp) → RaftState
  | none => S
  | some (_, S2, _) => S2

/-- The share of `nodeRunning` the writer gets back after a write with the pending batch `pb`: its
own `q`, or the batch's (which waited in the file's invariant). -/
def pbQ (q : Qp) : Option (GName × RaftState × Qp) → Qp
  | none => q
  | some (_, _, q') => q'

/-- The pending batch as the writer's variable records it, `γr` the name of its record's saved
proposition (`KdWv`). -/
def pbW (γr : GName) : Option (GName × RaftState × Qp) → Option (GName × RaftState × Qp × GName)
  | none => none
  | some (γb, S2, q') => some (γb, S2, q', γr)

/-- **The pending batch a write takes**: nothing, or a batch from `S` to `S2`, its *enter*, the share
`q'` of `nodeRunning` that waits with it (raft's `readyCrashEnter` needs it), and its results' saved
proposition at `γb`. -/
def kdPendIn (γ : KdNames) (id : w64) (n : NodeH) (S : RaftState) :
    Option (GName × RaftState × Qp) → IProp GF
  | none => iprop(emp)
  | some (γb, S2, q') => iprop(∃ (st st' : NodeDriverState) (ms : List QMsg),
      readyEnter n γ.r.cluster kdRaftN id st st' ms ∗ nodeRunning n γ.r.cluster kdRaftN q' ∗
      savedPropOwn γb DFrac.discard (kdBatchRes γ id n st' ms) ∗ ⌜st.durable = S ∧ st'.durable = S2⌝)

/-- The record a pending batch leaves in the file's invariant (`kdBatchRec`), at the writer's node. -/
def kdPendRec (γ : KdNames) (id : w64) (x : CrashNames) (n : NodeH) (S : RaftState) :
    Option (GName × RaftState × Qp) → IProp GF
  | none => iprop(emp)
  | some (γb, S2, q') => kdBatchRec γ id x S S2 q' γb n

/-- The writer's `nodeRunning` kept through a write with no pending batch. -/
def kdRunKeep (γ : KdNames) (n : NodeH) (q : Qp) : Option (GName × RaftState × Qp) → IProp GF
  | none => nodeRunning n γ.r.cluster kdRaftN q
  | some _ => iprop(emp)

/-- **What a write leaves of the pending batch**: its results, saved at `γb` (`dmu`'s `fired`). -/
def kdPendOut : Option (GName × RaftState × Qp) → IProp GF
  | none => iprop(emp)
  | some (γb, _, _) => iprop(∃ R : IProp GF, savedPropOwn γb DFrac.discard R ∗ R)

/-- The encoding of a file `openStorage` accepts, which holds `S`, holds `S`. -/
theorem fileHolds_some (γ : KdNames) (S : RaftState) (M : StorFile) (hM : KdFileOk M)
    (hS : StorageHolds S (kdContents (some M))) :
    kdSnapCert (GF := GF) γ M.snap ⊢ fileHolds γ S (some (encStor M)) := by
  iintro #Hcert
  iunfold fileHolds
  iexists some M
  isplitr
  · ipureintro; exact ⟨rfl, fun f hf => by cases hf; exact hM, hS⟩
  iintro %f %hf
  cases hf
  iexact Hcert

/-- **`durable.Write`'s first atomic update for `persist`** (see the file header). The rename's update
has no crash token: on the invariant's crashed side it moves only `durSt` and the writer, dropping the
pending batch; the sync's (`durWriteSync`, with the token) refutes that side. The batch's record names
its node existentially (`kdFileState`); the writer recognizes it by the saved proposition it allocates
at the rename (`γr`), which costs the sync a second later credit. -/
theorem kd_writeAU (γ : KdNames) (id : w64) (n : NodeH) (ph : KdDmuNames) (q : Qp) (S : RaftState)
    (o : Option StorFile) (M : StorFile) (pb : Option (GName × RaftState × Qp)) (Ψ0 : IProp GF)
    (hM : KdFileOk M) (hS : StorageHolds (pbTarget S pb) (kdContents (some M))) :
    ⊢ kdFileInvK γ id ph.fl -∗ nodeArm n γ.r.cluster ph.fl.x -∗ kdWriter ph.fl S o -∗ £ 1 -∗ £ 1 -∗
      kdRunKeep γ n q pb -∗ kdSnapCert γ M.snap -∗ kdPendIn γ id n S pb -∗
      (kdWriter ph.fl (pbTarget S pb) (some M) -∗ nodeRunning n γ.r.cluster kdRaftN (pbQ q pb) -∗
        kdPendOut pb -∗ Ψ0) -∗
      AU <{ ∃∃ s : DurFs.DurSt, DurFs.durSt (GF := GF) ph.fl.γd s }> @ DurFs.durAuMask, ∅
        <{ DurFs.durSt (GF := GF) ph.fl.γd ⟨some (encStor M), some s.cur⟩,
           COMM DurFs.durWriteSync (GF := GF) ph.fl.γd Ψ0 }> := by
  iintro #Hinv #Harm Hwr Hlc Hlc' Hrun #Hcert Hpend HK
  iauintro
  unfold atomic_acc
  iunfold kdFileInvK at Hinv
  imod inv_acc (E := DurFs.durAuMask) (kdRepN_sub_durAu id) $$ Hinv with ⟨Hi, Hclose⟩
  iunfold kdFileBody at Hi
  imod later_exists_except0 $$ Hi with ⟨%S0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%s0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%pb0, Hi⟩
  icases Hi with ⟨Hds, Hwv, Hb⟩
  imod Hds
  imod Hwv
  iunfold kdWriter at Hwr
  ihave %Hag := ghostVar_agree ph.fl.wr _ _ _ _ $$ Hwr Hwv
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑(kdRepN .@ uint.nat id) from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists ⟨kdFileVal o, none⟩
  iframe Hds
  isplit
  · -- abort: nothing changed
    iintro Hds
    imod Hclose2 with -
    imod Hclose $$ [Hds Hwv Hb] with -
    · inext
      iunfold kdFileBody
      iexists S, ⟨kdFileVal o, none⟩, none
      iframe Hds Hwv Hb
    imodintro
    iunfold kdWriter
    iframe
  -- the rename: the write's window opens, the pending batch moves into the invariant (or, on the
  -- crashed side, is dropped)
  iintro Hds
  imod Hclose2 with -
  imod saved_prop_alloc (GF := GF) (kdPendRec γ id ph.fl.x n S pb) DFrac.discard DFrac.valid_discard
    with ⟨%γr, #Hsr⟩
  imod ghostVar_update_halves ((S, ⟨some (encStor M), some (kdFileVal o)⟩, pbW γr pb) : KdWv) ph.fl.wr
    _ _ $$ Hwr Hwv with ⟨Hwr, Hwv⟩
  ihave Hb' : iprop(▷ ((raftState γ.r.cluster id S ∗
      kdFileState γ id ph.fl.x S ⟨some (encStor M), some (kdFileVal o)⟩ (pbW γr pb)) ∨
      crashed ∗ token ph.fl.tk)) $$ [Hb Hpend]
  · icases later_or.1 $$ Hb with (Hb | Hb)
    · inext
      ileft
      icases Hb with ⟨HrS, Hfs⟩
      iunfold kdFileState at Hfs
      icases Hfs with ⟨Hfh, -⟩
      iframe HrS
      iunfold kdFileState
      isplitl [Hfh]
      · iexact Hfh
      cases pb with
      | none =>
        simp only [pbW]
        rw [show pbTarget S none = S from rfl] at hS
        iapply fileHolds_some γ S M hM hS $$ Hcert
      | some p =>
        obtain ⟨γb, S2, q'⟩ := p
        simp only [pbW]
        rw [show pbTarget S (some (γb, S2, q')) = S2 from rfl] at hS
        iunfold kdPendIn at Hpend
        icases Hpend with ⟨%st, %st', %ms, Henter, Hrun', #Hsv, %Hst⟩
        iexists n
        isplitl [Henter Hrun']
        · iunfold kdBatchRec
          iexists st, st', ms
          iframe Harm Henter Hrun' Hsv
          ipureintro; exact Hst
        isplitr
        · iunfold kdPendRec at Hsr
          iexact Hsr
        iapply fileHolds_some γ S2 M hM hS $$ Hcert
    · inext
      iright
      iexact Hb
  imod Hclose $$ [Hds Hwv Hb'] with -
  · inext
    iunfold kdFileBody
    iexists S, ⟨some (encStor M), some (kdFileVal o)⟩, pbW γr pb
    iframe Hds Hwv Hb'
  imodintro
  -- the directory's sync: the window closes, the batch is entered
  iintro Hnc
  iauintro
  unfold atomic_acc
  imod inv_acc (E := DurFs.durAuMask) (kdRepN_sub_durAu id) $$ Hinv with ⟨Hi, Hclose⟩
  iunfold kdFileBody at Hi
  imod later_exists_except0 $$ Hi with ⟨%S0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%s0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%pb0, Hi⟩
  icases Hi with ⟨Hds, Hwv, Hb⟩
  imod Hds
  imod Hwv
  ihave %Hag := ghostVar_agree ph.fl.wr _ _ _ _ $$ Hwr Hwv
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  imod notCrashed_or_crashed $$ [$Hnc $Hb] with ⟨Hnc, Hb⟩
  icases Hb with ⟨HrS, Hfs⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑(kdRepN .@ uint.nat id) from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists ⟨some (encStor M), some (kdFileVal o)⟩
  iframe Hds
  isplit
  · -- abort
    iintro Hds
    imod Hclose2 with -
    imod Hclose $$ [HrS Hds Hwv Hfs] with -
    · inext
      iunfold kdFileBody
      iexists S, ⟨some (encStor M), some (kdFileVal o)⟩, pbW γr pb
      iframe Hds Hwv
      ileft
      iframe
    imodintro
    iframe
  iintro Hds
  imod Hclose2 with -
  ihave Hb : iprop(▷ (raftState γ.r.cluster id S ∗
      kdFileState γ id ph.fl.x S ⟨some (encStor M), some (kdFileVal o)⟩ (pbW γr pb))) $$ [HrS Hfs]
  · iframe
  imod lc_fupd_elim_later $$ Hlc Hb with ⟨HrS, Hfs⟩
  iunfold kdFileState at Hfs
  cases pb with
  | none =>
    simp only [pbW]
    icases Hfs with ⟨-, Hfh⟩
    imod ghostVar_update_halves ((S, ⟨some (encStor M), none⟩, none) : KdWv) ph.fl.wr _ _
      $$ Hwr Hwv with ⟨Hwr, Hwv⟩
    imod Hclose $$ [HrS Hds Hwv Hfh] with -
    · inext
      iunfold kdFileBody
      iexists S, ⟨some (encStor M), none⟩, none
      iframe Hds Hwv
      ileft
      iframe HrS
      iunfold kdFileState
      isplitl [Hfh]
      · iexact Hfh
      ipureintro; rfl
    imodintro
    iframe Hnc
    iunfold kdRunKeep at Hrun
    rw [show pbQ q none = q from rfl]
    iapply HK $$ [Hwr] Hrun []
    · iunfold kdWriter
      rw [show kdFileVal (some M) = some (encStor M) from rfl, show pbTarget S none = S from rfl]
      iexact Hwr
    · iunfold kdPendOut; iempintro
  | some p =>
    obtain ⟨γb, S2, q'⟩ := p
    simp only [pbW]
    icases Hfs with ⟨-, %n', Hrec, #Hsr', Hfh⟩
    -- the record is the writer's: its saved proposition agrees with the one allocated at the rename
    iunfold kdPendRec at Hsr
    ihave #Heq := saved_prop_agree γr DFrac.discard DFrac.discard _ _ $$ Hsr' Hsr
    ihave Hrec' : ▷ kdBatchRec γ id ph.fl.x S S2 q' γb n $$ [Hrec]
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨Hiff, -⟩
      iapply Hiff $$ Hrec
    imod lc_fupd_elim_later $$ Hlc' Hrec' with Hrec
    iunfold kdBatchRec at Hrec
    icases Hrec with ⟨%st, %st', %ms, -, Henter, Hrun', #Hsv, %Hst⟩
    obtain ⟨Hst1, Hst2⟩ := Hst
    ihave HrS : raftState γ.r.cluster id st.durable $$ [HrS]
    · rw [Hst1]; iexact HrS
    iunfold readyEnter at Henter
    icases Henter with ⟨Henter, -⟩
    iunfold readyEnterLive at Henter
    imod Henter $$ %(DurFs.durAuMask \ ↑(kdRepN .@ uint.nat id)) %q' %(kdRaftN_sub_durAu id) Hnc
      [$HrS $Hrun'] with ⟨Hnc, HrS, Hrun', Hdrv, Hmsgs⟩
    imod ghostVar_update_halves ((S2, ⟨some (encStor M), none⟩, none) : KdWv) ph.fl.wr _ _
      $$ Hwr Hwv with ⟨Hwr, Hwv⟩
    imod Hclose $$ [HrS Hds Hwv Hfh] with -
    · inext
      iunfold kdFileBody
      iexists S2, ⟨some (encStor M), none⟩, none
      rw [Hst2]
      iframe Hds Hwv
      ileft
      iframe HrS
      iunfold kdFileState
      isplitl [Hfh]
      · iexact Hfh
      ipureintro; rfl
    imodintro
    iframe Hnc
    rw [show pbQ q (some (γb, S2, q')) = q' from rfl]
    iapply HK $$ [Hwr] Hrun' [Hdrv Hmsgs]
    · iunfold kdWriter
      rw [show kdFileVal (some M) = some (encStor M) from rfl,
        show pbTarget S (some (γb, S2, q')) = S2 from rfl]
      iexact Hwr
    · iunfold kdPendOut
      iexists kdBatchRes γ id n st' ms
      iframe Hsv
      iunfold kdBatchRes
      iframe

end lemmas

end raft_kvnet
end EtcdGrove
end Perennial
