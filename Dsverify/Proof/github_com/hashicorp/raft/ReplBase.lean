/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/ReplBase.lean (241f27e).
-/
/-
Shared definitions and lemmas of the replication subsystem (replication.go, commitment.go):

* `prevOk`, `aeBody`: what a replication goroutine builds into an `AppendEntriesRequest`
  (`aeReq` is `aeBody` and `aeValid`, `aeReq_intro`);
* `wp_getLog_repl`: a read of the leader's own log store by its replication goroutine (the
  store's atomic `GetLog`, opening the log coupling cell and running `readLog_repl`);
* atomic `uint64` loads/stores of a location the caller owns.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Dsverify.Proof.github_com.hashicorp.raft.leader.DurView
public import Perennial.Spec.sync.atomic.LoadUint64
public import Perennial.Spec.sync.atomic.StoreUint64
public import Perennial.Proof.sync.Results

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

/-! ## The commitment's quorum (pure) -/

theorem filter_drop_le {α} (l : List α) (p : α → Bool) (k : Nat) :
    ((l.drop k).filter p).length ≤ (l.filter p).length := by
  induction l generalizing k with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.drop_succ_cons, List.filter_cons]
      have := ih k
      split <;> simp <;> omega

theorem quorum_of_sorted {K : Type} (keys : List K) (f : K → w64) (xs : List w64)
    (hperm : (keys.map f).Perm xs) (hs : xs.Pairwise (fun x y => uint.Z x ≤ uint.Z y))
    (q : w64) (hq : xs[(xs.length - 1) / 2]? = some q) :
    xs.length < 2 * (keys.filter (fun j => decide (uint.Z q ≤ uint.Z (f j)))).length := by
  have hn : (xs.length - 1) / 2 < xs.length := (List.getElem?_eq_some_iff.mp hq).1
  have hq' : xs[(xs.length - 1) / 2] = q := (List.getElem?_eq_some_iff.mp hq).2
  generalize hidx : (xs.length - 1) / 2 = idx at hq hn hq'
  let p : w64 → Bool := fun y => decide (uint.Z q ≤ uint.Z y)
  have hall : ∀ y ∈ xs.drop idx, p y = true := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    simp only [p, List.getElem_drop, decide_eq_true_eq]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; rw [← hq']; simp
    · rw [← hq']
      exact List.pairwise_iff_getElem.mp hs idx (idx + k) hn (by simp at hk; omega) (by omega)
  have h1 : ((xs.drop idx).filter p).length = xs.length - idx := by
    rw [List.filter_eq_self.mpr hall]; simp
  have h2 := filter_drop_le xs p idx
  have h3 : ((keys.map f).filter p).length = (xs.filter p).length := (hperm.filter _).length_eq
  rw [List.filter_map, List.length_map] at h3
  show xs.length < 2 * (keys.filter (p ∘ f)).length
  omega


section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

instance hdrOk_persistent h snd : Persistent (hdrOk (GF := GF) h snd) := by
  unfold hdrOk; infer_instance

instance aeReq_persistent γ rq snd T prev pt ents lci ss :
    Persistent (aeReq (GF := GF) γ rq snd T prev pt ents lci ss) := by
  unfold aeReq hdrOk aeValid; infer_instance

instance aeResp_persistent γ rp j T k hb ss : Persistent (aeResp (GF := GF) γ rp j T k hb ss) := by
  unfold aeResp hdrOk respWit; infer_instance

/-- The voters of `Q` (each with a match index `≥ k > 0`) acknowledged at least `k` in `T`, or
received a valid install of `T` whose commit index is at least `k` (stage 3). -/
theorem acks_of_matches (γ : GNames) (T : Nat) (mm : GMap SID w64) (Q : List SID) (k : Nat)
    (hQ : ∀ j ∈ Q, ∃ m, mm.lookup j = some m ∧ k ≤ uint.nat m ∧ 0 < uint.nat m) :
    ([∗map] j ↦ m ∈ mm, ⌜m = W64 0⌝ ∨ ackIs (GF := GF) γ j T (uint.nat m) ∨ lciOk γ T (uint.nat m)) ⊢
      [∗list] j ∈ Q, ∃ m, ⌜k ≤ m⌝ ∗ (ackIs γ j T m ∨ lciOk γ T m) := by
  iintro #H
  iapply BigSepL.bigSepL_intro (P := iprop(□ ([∗map] j ↦ m ∈ mm, ⌜m = W64 0⌝ ∨ ackIs (GF := GF) γ j T (uint.nat m) ∨ lciOk γ T (uint.nat m))))
  · intro idx j hj
    obtain ⟨m, hm, hkm, hpos⟩ := hQ j (List.mem_of_getElem? hj)
    iintro #H
    ihave #Hj := BigSepM.bigSepM_lookup (Φ := fun j m => iprop(⌜m = W64 0⌝ ∨ ackIs (GF := GF) γ j T (uint.nat m) ∨ lciOk γ T (uint.nat m))) (m := mm) hm $$ H
    icases Hj with (%h0 | #Ha | #Ha)
    · exfalso; subst h0; simp at hpos
    · iexists (uint.nat m); isplitr; · ipureintro; exact hkm
      ileft; iexact Ha
    · iexists (uint.nat m); isplitr; · ipureintro; exact hkm
      iright; iexact Ha
  iexact H

set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 2000000 in
instance replShared_persistent r γ rc i T j s : Persistent (replShared (GF := GF) r γ rc i T j s) := by
  unfold replShared stopChan; infer_instance

theorem notifyChan_bag (ch : Loc) :
    notifyChan (GF := GF) ch ⊢ ∃ γc : ChanNames, isChanBag (V := Unit) γc ch (fun _ => iprop(True)) := by
  unfold notifyChan; exact .rfl

/-- An observation whose data is not a `RaftState` value carries no protocol facts. -/
theorem obsArg_named (γ : GNames) (i : SID) (st : SState) (ty : go.GoType) (v : val)
    (hty : ty ≠ RaftState.ty) : ⊢ obsArg (GF := GF) γ i st (interface.mkOk ty v) := by
  apply obsArg_other
  · intro h; unfold leaderObs at h
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h
    exact hty h.1
  · intro v' h
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h
    exact absurd h.1 hty

theorem failedHb_ne : FailedHeartbeatObservation.ty ≠ RaftState.ty := by
  simp [FailedHeartbeatObservation.ty, RaftState.ty]

theorem resumedHb_ne : ResumedHeartbeatObservation.ty ≠ RaftState.ty := by
  simp [ResumedHeartbeatObservation.ty, RaftState.ty]

theorem replStopCh_elim (s : Loc) (γs : StopNames) :
    replStopCh (GF := GF) s γs ⊢
      ∃ ch : Loc, s.[followerReplication, go!"stopCh"] ↦□ ch ∗ stopChan γs ch := by
  unfold replStopCh; exact .rfl

theorem logIs_pure (lv : Log) (k : Nat) (e : Entry) :
    logIs (GF := GF) lv k e ⊢ ⌜uint.nat lv.Index' = k ∧ uint.nat lv.Term' = e.term ∧ uint.nat lv.Type' = e.kind⌝ := by
  unfold logIs
  iintro ⟨%h, -⟩
  ipureintro; exact h

/-- A raft error value is a `*errorString` (unfolds Base.lean's `isRaftErr`/`errVals`). -/
theorem isRaftErr_ptr (c : RaftErr) (e : GoInterface) :
    isRaftErr (GF := GF) c e ⊢
      ∃ x : Loc, ⌜e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x⌝ := by
  unfold isRaftErr errVals
  iintro ⟨%f, ⟨%hinj, #Hall⟩, %hfc⟩
  have hc : c ∈ RaftErr.all := by cases c <;> simp [RaftErr.all]
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hc
  ihave ⟨#H1, #H2⟩ := BigSepL.bigSepL_lookup (Φ := fun _ c => iprop(globalAddr c.var ↦□ f c ∗ errors.newVar (GF := GF) c.var c.msg)) hk $$ Hall
  unfold errors.newVar
  icases H2 with ⟨%x, #Hx, -⟩
  icombine H1 Hx gives %Heq
  iexists x
  ipureintro
  rw [← hfc, Heq]

/-- The facts of `replShared` the replication goroutine uses most. -/
theorem replShared_core (r : Loc) (γ : GNames) (i : SID) (T : Nat) (j : SID) (s : Loc) :
    replShared (GF := GF) r γ rc i T j s ⊢
      s.[followerReplication, go!"currentTerm"] ↦□ (W64 T) ∗
      (∃ sf : ServerSuffrage, s.[followerReplication, go!"peer"] ↦□ Server.mk sf j j) ∗ isSrv γ j ∗
      rwLock peerLockN (s.[followerReplication, go!"peerLock"]) (fun _ => iprop(True)) ∗
      (∃ cm : Loc, s.[followerReplication, go!"commitment"] ↦□ cm ∗ isCommitment γ i T cm) ∗
      (∃ ch : Loc, s.[followerReplication, go!"triggerCh"] ↦□ ch ∗ notifyChan ch) ∗
      (∃ ch : Loc, s.[followerReplication, go!"notifyCh"] ↦□ ch ∗ notifyChan ch) ∗
      (∃ ch : Loc, s.[followerReplication, go!"stepDown"] ↦□ ch ∗ notifyChan ch) ∗
      (∃ ch : Loc, s.[followerReplication, go!"triggerDeferErrorCh"] ↦□ ch ∗
        ∃ γt : ChanNames, isChanBag (V := Loc) γt ch (fun d => deferResp d (fun _ => iprop(True)))) ∗
      inv nextIdxN iprop(∃ v : w64,
        s.[followerReplication, go!"nextIndex"] ↦{DFrac.own (1 : Qp).half} v) := by
  unfold replShared
  iintro ⟨%cm, %stopCh, %trig, %notif, %sd, %tde, %γs, #H1, #H2, #H3, -, #H5, #H6, #H7, -, -, #H10,
    #H11, #H12, #H13, #H14, #H15, #H16, #H17, #H18, -, -⟩
  isplitr; · iexact H1
  isplitr; · iexact H2
  isplitr; · iexact H3
  isplitr; · iexact H5
  isplitr; · iexists cm; iframe #
  isplitr; · iexists trig; iframe #
  isplitr; · iexists notif; iframe #
  isplitr; · iexists sd; iframe #
  isplitr; · iexists tde; iframe #
  iexact H18

instance replStopCh_persistent s γs : Persistent (replStopCh (GF := GF) s γs) := by
  unfold replStopCh stopChan; infer_instance

/-- (stage 2) The writer's half of `nextIndex` (the replication goroutine's, `replOwn`; in pipeline
mode lent to the decoder). -/
def nextHalf (s : Loc) : IProp GF :=
  iprop(∃ v : w64, s.[followerReplication, go!"nextIndex"] ↦{DFrac.own (1 : Qp).half} v)

/-- (stage 2) The shared half of `nextIndex` (`replShared`'s cell: atomic loads by any goroutine
open it; a store needs it and the writer's half). -/
def nextCell (s : Loc) : IProp GF :=
  inv nextIdxN iprop(∃ v : w64, s.[followerReplication, go!"nextIndex"] ↦{DFrac.own (1 : Qp).half} v)

instance nextCell_persistent s : Persistent (nextCell (GF := GF) s) := by
  unfold nextCell; infer_instance

theorem replShared_nextCell (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID)
    (s : Loc) : replShared (GF := GF) r γ rc i T j s ⊢ nextCell s := by
  unfold replShared nextCell
  iintro ⟨%cm, %stopCh, %trig, %notif, %sd, %tde, %γs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, #H, -, -⟩
  iexact H

/-- The replication goroutine's own fields (`failures`, `allowPipeline`; stage 2: the writer's half
of `nextIndex`, the other half being the shared cell `nextCell`). -/
def replFields (s : Loc) : IProp GF :=
  iprop((∃ v : w64, s.[followerReplication, go!"failures"] ↦ v) ∗
    (∃ b : Bool, s.[followerReplication, go!"allowPipeline"] ↦ b) ∗ nextHalf s)

theorem replFields_intro (s : Loc) (fv : w64) (ap : Bool) (nv : w64) :
    s.[followerReplication, go!"failures"] ↦ fv ∗
      s.[followerReplication, go!"allowPipeline"] ↦ ap ∗
      s.[followerReplication, go!"nextIndex"] ↦{DFrac.own (1 : Qp).half} nv ⊢ replFields (GF := GF) s := by
  unfold replFields nextHalf
  iintro ⟨H1, H2, H3⟩
  isplitl [H1]; · iexists fv; iexact H1
  isplitl [H2]; · iexists ap; iexact H2
  iexists nv; iexact H3

theorem replFields_elim (s : Loc) :
    replFields (GF := GF) s ⊢ ∃ (fv : w64) (ap : Bool) (nv : w64),
      s.[followerReplication, go!"failures"] ↦ fv ∗
      s.[followerReplication, go!"allowPipeline"] ↦ ap ∗
      s.[followerReplication, go!"nextIndex"] ↦{DFrac.own (1 : Qp).half} nv := by
  unfold replFields nextHalf
  iintro ⟨⟨%fv, H1⟩, ⟨%ap, H2⟩, ⟨%nv, H3⟩⟩
  iexists fv, ap, nv
  iframe

/-- A replication goroutine's resources as its loop uses them. -/
theorem replOwn_fields (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (s : Loc) :
    replOwn (GF := GF) r γ rc i T s ⊢ ∃ j : SID, replShared r γ rc i T j s ∗ leaderIs γ T i ∗
      termLb γ i T ∗ (∃ γs : StopNames, replStopCh s γs) ∗ replFields s := by
  unfold replOwn replFields nextHalf
  iintro ⟨%j, Hs, Hl, Hlb, Hst, Hf, Ha, Hn⟩
  iexists j
  iframe

/-- The heartbeat goroutine's stop channel (`replicate`'s `stopHeartbeat`): never sent on, closed
once by `replicate` (the producer); the heartbeat goroutine is the consumer. -/
def hbStop (γh : SpscNames) (ch : Loc) : IProp GF :=
  isSpsc (V := Unit) γh ch (fun _ _ => iprop(False)) (fun _ => iprop(True))

instance hbStop_persistent γh ch : Persistent (hbStop (GF := GF) γh ch) := by
  unfold hbStop; infer_instance

/-- The previous entry `(prev, pt)` of a request of term `T` (the premise of `aeValid_intro`). -/
def prevOk (γ : GNames) (T prev pt : Nat) : IProp GF :=
  iprop(⌜prev = 0 ∧ pt = 0⌝ ∨ ∃ e, ⌜1 ≤ prev ∧ e.term = pt⌝ ∗ llogIdx γ T prev e)

instance prevOk_persistent γ T prev pt : Persistent (prevOk (GF := GF) γ T prev pt) := by
  unfold prevOk; infer_instance

/-- The entries `ents` of a request, starting at index `prev + 1`, are `llog T`'s. -/
def entsOk (γ : GNames) (T prev : Nat) (ents : List Entry) : IProp GF :=
  iprop([∗list] j ↦ e ∈ ents, llogIdx γ T (prev + 1 + j) e)

instance entsOk_persistent γ T prev ents : Persistent (entsOk (GF := GF) γ T prev ents) := by
  unfold entsOk; infer_instance

/-- The entries' pointers of a request. -/
def entPtrs (sl : GoSlice) (prev : Nat) (ents : List Entry) : IProp GF :=
  iprop(∃ ptrs : List Loc, sl ↦*□ ptrs ∗ ⌜ptrs.length = ents.length⌝ ∗
    [∗list] j ↦ p ∈ ptrs, ∃ e, ⌜ents[j]? = some e⌝ ∗ logPtr p (prev + 1 + j) e)

instance entPtrs_persistent sl prev ents : Persistent (entPtrs (GF := GF) sl prev ents) := by
  unfold entPtrs; infer_instance

/-- An `AppendEntriesRequest` as `setupAppendEntries` builds it (all of `aeReq` but the validity;
the term is `W64 T`). -/
def aeBody (rq : AppendEntriesRequest) (snd : SID) (T prev pt : Nat) (ents : RLog) (lci : Nat) :
    IProp GF :=
  iprop(⌜rq.Term' = W64 T ∧ uint.nat rq.PrevLogEntry' = prev ∧ uint.nat rq.PrevLogTerm' = pt ∧
      uint.nat rq.LeaderCommitIndex' = lci⌝ ∗
    hdrOk rq.RPCHeader' snd ∗ rq.Leader' ↦*□ snd ∗ entPtrs rq.Entries' prev ents)

instance aeBody_persistent rq snd T prev pt ents lci :
    Persistent (aeBody (GF := GF) rq snd T prev pt ents lci) := by
  unfold aeBody hdrOk; infer_instance

theorem aeReq_intro (γ : GNames) (rq : AppendEntriesRequest) (snd : SID) (T prev pt : Nat)
    (ents : RLog) (lci : Nat) (ss : Snap) (hT : T < 2 ^ 64) :
    aeBody (GF := GF) rq snd T prev pt ents lci ∗ aeValid γ T prev pt ents lci ∗ histLb γ ss ⊢
      aeReq γ rq snd T prev pt ents lci ss := by
  unfold aeBody aeReq entPtrs
  iintro ⟨⟨%h, Hh, Hl, He⟩, Hv, Hs⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  isplitr
  · ipureintro
    refine ⟨?_, h2, h3, h4⟩
    rw [h1]; word
  iframe

/-- The validity of what was read: each read gives a fact of term `T` or `termLb γ i (T + 1)`. -/
abbrev orStale (γ : GNames) (i : SID) (T : Nat) (P : IProp GF) : IProp GF :=
  iprop(P ∨ termLb γ i (T + 1))

theorem ptrs_snoc (ptrs : List Loc) (ents : List Entry) (prev : Nat) (lp : Loc) (e : Entry)
    (hlen : ptrs.length = ents.length) :
    ([∗list] j ↦ p ∈ ptrs, ∃ e', ⌜ents[j]? = some e'⌝ ∗ logPtr (GF := GF) p (prev + 1 + j) e') ∗
      logPtr lp (prev + 1 + ents.length) e ⊢
    [∗list] j ↦ p ∈ ptrs ++ [lp], ∃ e', ⌜(ents ++ [e])[j]? = some e'⌝ ∗ logPtr p (prev + 1 + j) e' := by
  iintro ⟨Hl, He⟩
  iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
  isplitl [Hl]
  · iapply BigSepL.bigSepL_mono (Φ := fun j p => iprop(∃ e', ⌜ents[j]? = some e'⌝ ∗ logPtr (GF := GF) p (prev + 1 + j) e')) ?_ $$ Hl
    intro k x hk
    iintro ⟨%e', %he', Hp⟩
    iexists e'
    iframe
    ipureintro
    have : k < ents.length := by
      have := (List.getElem?_eq_some_iff.mp he').1; exact this
    rw [List.getElem?_append_left this]; exact he'
  · iexists e
    rw [hlen]
    iframe
    ipureintro; simp

theorem entsOk_snoc (γ : GNames) (i : SID) (T prev : Nat) (ents : List Entry) (e : Entry) :
    orStale (GF := GF) γ i T (entsOk γ T prev ents) ∗
      (llogIdx γ T (prev + 1 + ents.length) e ∨ termLb γ i (T + 1)) ⊢
    orStale γ i T (entsOk γ T prev (ents ++ [e])) := by
  unfold entsOk
  iintro ⟨#H1 | #H1, #H2 | #H2⟩
  · ileft
    iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
    iframe #
  · iright; iexact H2
  · iright; iexact H1
  · iright; iexact H1

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

/-- (Stage 3) `LogAbs` is inhabited (to open `logCell`'s `▷ ∃ A`). -/
instance logAbs_inhabited : Inhabited LogAbs := ⟨LogAbs.empty⟩

/-- (Unfolds gprot's `logCouple`: ghost ownership, timeless.) -/
instance logCouple_timeless γ i L : Timeless (logCouple (GF := GF) γ i L) := by
  unfold logCouple; infer_instance

/-- (Unfolds gprot's `termCouple`: ghost ownership, timeless.) -/
instance termCouple_timeless γ i t : Timeless (termCouple (GF := GF) γ i t) := by
  unfold termCouple; infer_instance

/-- A term lower bound of `i` fits in a `uint64` (the term cell holds a `w64` above it). -/
theorem termLb_bound (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) :
    termCell (GF := GF) r γ rc i ∗ srvDurInv γ rc i ∗ termLb γ i T ⊢ |NC={⊤}=> ⌜T < 2 ^ 64⌝ := by
  iintro ⟨#Hc, #Hd, #Hlb⟩ Hnc
  unfold termCell termV
  iinv Hc with ⟨%t, >Ht, >Htv⟩ Hclose
  ihave Hacc := durAcc γ rc i (E := ⊤ \ ↑termN) durN_diff_termN $$ Hd
  imod Hacc $$ Hnc with ⟨Hnc, HX, Hcl2⟩
  imod later_exists_except0 $$ HX with ⟨%X, HX⟩
  unfold durBody
  icases HX with ⟨Hs, Hdv, Hlc, >Htc, Hcc, Hsv, Hst, >Htv2, Hrest⟩
  ihave %Heq := ghostVar_agree _ _ _ _ _ $$ Htv Htv2
  ihave %Hle := termCouple_lb γ i X.s.term T $$ [Htc]
  · iframe Htc; iexact Hlb
  imod Hcl2 $$ [Hs Hdv Hlc Htc Hcc Hsv Hst Htv2 Hrest] with -
  · inext; iexists X; iframe
  imod Hclose $$ [Ht Htv] with -
  · inext; iexists t; iframe
  imodintro
  iframe Hnc
  ipureintro
  have : uint.nat t < 2 ^ 64 := by word
  omega

/-- An entry of a prefix is an entry of the whole log. -/
theorem ent_append_some (L ps : RLog) (k : Nat) (e : Entry) (h : ent L k = some e) :
    ent (L ++ ps) k = some e := by
  unfold ent at *
  split at h
  · cases h
  · rename_i hk
    rw [if_neg hk]
    have := (List.getElem?_eq_some_iff.mp h).1
    rw [List.getElem?_append_left this]; exact h

/-- What `GetLog(idx, ptr)` on the leader's own store gives its replication goroutine (leader `i`
of term `T`): an error, or the entry at `idx`, which is `llog T`'s or the term has moved on. -/
def getLogRepl (γ : GNames) (i : SID) (T : Nat) (ptr : Loc) (idx : Nat) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err ≠ interface.nil⌝ ∗ (∃ c, isRaftErr c err) ∗ ∃ lv : Log, ptr ↦ lv) ∨
    (⌜err = interface.nil⌝ ∗ ∃ (lv : Log) (e : Entry), ptr ↦ lv ∗ logIs lv idx e ∗
      ⌜1 ≤ idx ∧ idx < 2 ^ 62⌝ ∗ (llogIdx γ T idx e ∨ termLb γ i (T + 1))))

theorem wp_getLog_repl (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (x : GoInterfaceOk)
    (idx : w64) (ptr : Loc) (lv0 : Log) (tid : Nat) :
    {{ Inv γ ∗ srvDurInv γ rc i ∗ isLogStore x rc.ownL ∗ leaderIs γ T i ∗ termLb γ i T ∗
       ptr ↦ lv0 ∗ rtok tid }}
      (App (App (Val #(methods x.ty go!"GetLog" x.v)) (Val #idx)) (Val #ptr))
    {{ (err : GoInterface), RET #err; rtok tid ∗ getLogRepl γ i T ptr (uint.nat idx) err }} := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

/-- An atomic load of a `uint64` the caller owns. -/
theorem wp_loadUint64_own (wp_LoadUint64 : sync.atomic.LoadUint64.spec (GF := GF) (hG := hG))
    (addr : Loc) (v : w64) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ addr ↦{dq} v }}
      (App (Val (@! sync.atomic.LoadUint64)) (Val #addr))
    {{ RET #v; addr ↦{dq} v }} := by
  iintro %Φ ⟨#Hpkg, Ha⟩ HΦ
  iapply wp_LoadUint64 addr dq $$ Hpkg
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iexists v
  iframe Ha
  iintro Ha
  imod Hmask with -
  imodintro
  iapply HΦ $$ Ha

/-- An atomic store of a `uint64` the caller owns. -/
theorem wp_storeUint64_own (wp_StoreUint64 : sync.atomic.StoreUint64.spec (GF := GF) (hG := hG))
    (addr : Loc) (v0 v : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ addr ↦ v0 }}
      (App (App (Val (@! sync.atomic.StoreUint64)) (Val #addr)) (Val #v))
    {{ RET #(); addr ↦ v }} := by
  iintro %Φ ⟨#Hpkg, Ha⟩ HΦ
  iapply wp_StoreUint64 addr v $$ Hpkg
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iexists v0
  iframe Ha
  iintro Ha
  imod Hmask with -
  imodintro
  iapply HΦ $$ Ha

/-- An atomic load of `nextIndex` (through the shared cell). -/
theorem wp_loadUint64_cell (wp_LoadUint64 : sync.atomic.LoadUint64.spec (GF := GF) (hG := hG))
    (s : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ nextCell s }}
      (App (Val (@! sync.atomic.LoadUint64)) (Val #(s.[followerReplication, go!"nextIndex"])))
    {{ (v : w64), RET #v; True }} := by
  iintro %Φ ⟨#Hpkg, #Hc⟩ HΦ
  iapply wp_LoadUint64 _ (DFrac.own (1 : Qp).half) $$ Hpkg
  unfold nextCell
  iinv Hc with ⟨%x, >Hx⟩ Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iexists x
  iframe Hx
  iintro Hx
  imod Hmask with -
  imod Hclose $$ [Hx] with -
  · inext; iexists x; iexact Hx
  imodintro
  iapply HΦ; itrivial

/-- An atomic store of `nextIndex` by its writer (its half and the shared cell). -/
theorem wp_storeUint64_cell (wp_StoreUint64 : sync.atomic.StoreUint64.spec (GF := GF) (hG := hG))
    (s : Loc) (v0 v : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ nextCell s ∗
       s.[followerReplication, go!"nextIndex"] ↦{DFrac.own (1 : Qp).half} v0 }}
      (App (App (Val (@! sync.atomic.StoreUint64)) (Val #(s.[followerReplication, go!"nextIndex"])))
        (Val #v))
    {{ RET #(); s.[followerReplication, go!"nextIndex"] ↦{DFrac.own (1 : Qp).half} v }} := by
  iintro %Φ ⟨#Hpkg, #Hc, Hh⟩ HΦ
  iapply wp_StoreUint64 _ v $$ Hpkg
  unfold nextCell
  iinv Hc with ⟨%x, >Hx⟩ Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  ihave ⟨%Heq, Hfull⟩ := typedPointsto_half_combine _ v0 x 1 $$ [Hh Hx]
  · iframe
  iexists x
  iframe Hfull
  iintro Hfull
  ihave ⟨Hh, Hx⟩ := (typedPointsto_half_split _ v 1).1 $$ Hfull
  imod Hmask with -
  imod Hclose $$ [Hx] with -
  · inext; iexists v; iexact Hx
  imodintro
  iapply HΦ $$ Hh

theorem aeValid_of_reads (γ : GNames) (i : SID) (T prev pt : Nat) (ents : List Entry) (lci : Nat) :
    leaderIs (GF := GF) γ T i ∗ orStale γ i T (prevOk γ T prev pt) ∗
      orStale γ i T (entsOk γ T prev ents) ∗ orStale γ i T (lciOk γ T lci) ⊢
    orStale γ i T (aeValid γ T prev pt ents lci) := by
  iintro ⟨#Hl, #Hp | #Hp, #He | #He, #Hc | #Hc⟩
  all_goals first | (iright; iexact Hp) | (iright; iexact He) | (iright; iexact Hc) | skip
  ileft
  iapply aeValid_intro γ T prev pt ents lci i
  unfold prevOk entsOk
  iframe #

set_option maxHeartbeats 800000 in
/-- A nonblocking receive on a stop channel (stage 4: it may hold one value, `startStopReplication`'s
`lastIdx`; it may be closed): either it is not ready, or it gives the value or the close (stage 2: a
broadcast channel, the receiver keeps its right). -/
theorem stopChan_nb_rcv_au (γs : StopNames) (ch : Loc) (Φ : w64 → Bool → IProp GF) :
    ⊢ stopChan γs ch -∗ £ 1 -∗
      ▷ (∀ (v : w64) (ok : Bool), Φ v ok) -∗ nonblockingRecvAuInner γs.ch w64 Φ := by
  unfold stopChan nonblockingRecvAuInner
  iintro ⟨#Hchan, #Hinv⟩ Hlc1 Hcont
  iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑stopN) $$ Hlc1 Hi with Hi
  unfold stopInv
  icases Hi with ⟨%st, Hch, Hm⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists st
  iframe Hch
  rcases st with (_ | ⟨v, (_ | ⟨_, _⟩)⟩) | _ | _ | _ | _ | _ | (_ | ⟨v, (_ | ⟨_, _⟩)⟩)
  all_goals dsimp only
  case Closed.nil =>
    iintro Hch
    imod Hmask with -
    imod Hclose $$ [Hch Hm] with -
    · inext; iexists .Closed []; dsimp only; iframe
    imodintro
    iapply Hcont
  case Buffered.cons.nil =>
    iintro Hch
    imod Hmask with -
    icases Hm with ⟨Hd, -⟩
    imod Hclose $$ [Hch Hd] with -
    · inext; iexists .Buffered []; dsimp only; iframe
    imodintro
    iapply Hcont
  case Closed.cons.nil =>
    iintro Hch
    imod Hmask with -
    icases Hm with ⟨Hd, -⟩
    imod Hclose $$ [Hch Hd] with -
    · inext; iexists .Closed []; dsimp only; iframe
    imodintro
    iapply Hcont
  all_goals first | itrivial | (iexfalso; iexact Hm)

set_option maxHeartbeats 800000 in
/-- A blocking receive on a stop channel (stage 4: it may hold one value, `startStopReplication`'s
`lastIdx`): it completes with that value, or once the channel is closed and drained (the zero value
and `false`); the receiver keeps its right (a broadcast channel). -/
theorem stopChan_rcv_au (γs : StopNames) (ch : Loc) (Φ : w64 → Bool → IProp GF) :
    ⊢ stopChan γs ch -∗ £ 1 -∗
      ▷ (∀ (v : w64) (ok : Bool), Φ v ok) -∗ recvAu γs.ch w64 Φ := by
  unfold stopChan recvAu
  iintro ⟨#Hchan, #Hinv⟩ Hlc1 Hcont
  iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑stopN) $$ Hlc1 Hi with Hi
  unfold stopInv
  icases Hi with ⟨%st, Hch, Hm⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists st
  iframe Hch
  rcases st with (_ | ⟨v, (_ | ⟨_, _⟩)⟩) | _ | _ | _ | _ | _ | (_ | ⟨v, (_ | ⟨_, _⟩)⟩)
  all_goals dsimp only
  case Closed.nil =>
    iintro Hch
    imod Hmask with -
    imod Hclose $$ [Hch Hm] with -
    · inext; iexists .Closed []; dsimp only; iframe
    imodintro
    iapply Hcont
  case Buffered.cons.nil =>
    iintro Hch
    imod Hmask with -
    icases Hm with ⟨Hd, -⟩
    imod Hclose $$ [Hch Hd] with -
    · inext; iexists .Buffered []; dsimp only; iframe
    imodintro
    iapply Hcont
  case Closed.cons.nil =>
    iintro Hch
    imod Hmask with -
    icases Hm with ⟨Hd, -⟩
    imod Hclose $$ [Hch Hd] with -
    · inext; iexists .Closed []; dsimp only; iframe
    imodintro
    iapply Hcont
  all_goals first | itrivial | (iexfalso; iexact Hm)

end lemmas

end github_com.hashicorp.raft

end Perennial
