/-
`(*Replica).handlePreAccept` against the model's `hPreAccept` (`PAModel`): the proof, stated with
`PAWf`'s fields (`HandlePreAccept.lean` states the spec). The reply goes through
`wp_replyPreAccept_frac` (HUB handlers-6: its `Deps` are the instance's read-only array, its
`CommittedDeps` the live `r.CommittedUpTo`, so `msgObj` takes the slices at their own fractions;
the struct is sent at half, the kept half identifies the returned slices).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandlePrepare
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.StartPhase1
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.PAModel
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.RecInst

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

theorem paEvs_noSends (σ : RState) (m : PreAccept) : NoSends (paEvs σ m) := by
  intro o ho
  unfold paEvs at ho
  split at ho
  · split at ho
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
      subst ho; exact ⟨fun _ _ h => Out.noConfusion h, fun _ h => Out.noConfusion h⟩
    · simp at ho
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
    rcases ho with rfl | rfl <;>
      exact ⟨fun _ _ h => Out.noConfusion h, fun _ h => Out.noConfusion h⟩

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- `replyPreAccept(t, reply)` with the reply's parts at their own fractions. -/
theorem wp_replyPreAccept_frac (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (i : Nat)
    (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (ord : List w32)
    (t : Nat) (q : w32) (hqt : W32 (t : Int) = q) (lr : Loc) (m : PreAcceptReply)
    (ds cds : GoSlice) (dq1 dq2 : DFrac) (h : t < nR ∧ t ≠ i)
    (hwf : (Msg.preAcceptReply m).wf) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ outboxFrag γ i t [Msg.preAcceptReply m] ∗
        lr ↦ epaxos.PreAcceptReply.mk m.replica m.inst m.ballot m.vballot m.seq ds cds m.status ∗
        ds ↦*{dq1} m.deps ∗ cds ↦*{dq2} m.committedDeps }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"replyPreAccept"))
        (Val #q)) (Val #lr))
    {{ RET #(); outboxFrag γ i t [] ∗ ds ↦*{dq1} m.deps ∗ cds ↦*{dq2} m.committedDeps }} := by
  subst hqt
  wp_start as ⟨#Hctx, Ho, Hl, Hds, Hcds⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  ihave ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, %HLn⟩ := fwRO_fields _ _ _ _ _ $$ Hfro
  unfold epROFields
  icases Hro with ⟨-, -, -, #Hparr, -⟩
  wp_auto
  icases (typedPointsto_half_split lr _ 1).1 $$ Hl with ⟨Hl, Hl2⟩
  ihave Hmsg : msgObj (interface.mkOk (go.GoType.PointerType epaxos.PreAcceptReply.ty) #lr)
      (Msg.preAcceptReply m) (DFrac.own (1 : Qp).half) dq1 dq2 $$ [Hl Hds Hcds]
  · unfold msgObj
    iexists MsgKind.preAcceptReply, lr
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    unfold ownMsg ownPreAcceptReply ownDeps
    iexists ds, cds
    iframe
  wp_apply (wp_bcast_send hS γ r rr i L p Rext ord t
    (interface.mkOk (go.GoType.PointerType epaxos.PreAcceptReply.ty) #lr)
    (Msg.preAcceptReply m) (DFrac.own (1 : Qp).half) (W8 12) rfl ⟨by rw [HLn.1]; exact h.1, h.2, rfl, hwf⟩
    dq1 dq2) $$ [Ho Hmsg]
  · isplitl []
    · unfold hdCtx epROFields prefOrder; iexact Hctx0
    iframe
  iintro ⟨Hmsg, Ho⟩
  unfold msgObj
  icases Hmsg with ⟨%k, %l', %Hk, Hm⟩
  obtain ⟨-, he⟩ := Hk
  have hl : l' = lr := by
    rw [interface_mkOk_inj] at he
    exact (go.intoVal_inj he.2).symm
  subst hl
  unfold ownMsg ownPreAcceptReply ownDeps
  icases Hm with ⟨%ds', %cds', Hl, Hds, Hcds⟩
  icombine Hl2 Hl gives %Heq
  simp only [epaxos.PreAcceptReply.mk.injEq] at Heq
  obtain ⟨-, -, -, -, -, rfl, rfl, -⟩ := Heq
  wp_auto
  iapply HΦ
  iframe

/-- Closing the opened slot with an instance record. -/
theorem repInsts_updP (γ : EpNames) (i : Nat) (r : Loc) (inst : InstId → Option InstRec)
    (x : InstId) (o : Option InstRec) :
    repInstsP (GF := GF) r (updP (instAtP γ i inst) x (fun pt => instAt γ i x pt o)) ⊢
      repInsts γ i r (upd inst x o) := by
  have e : updP (instAtP (GF := GF) γ i inst) x (fun pt => instAt γ i x pt o) = instAtP γ i (upd inst x o) := by
    funext y pt
    simp only [updP, instAtP, upd]
    split <;> simp_all
  rw [e]
  exact (repInsts_P γ i r _).2

theorem pa_updP_updP {α : Type} (P : InstId → α) (x : InstId) (a b : α) :
    updP (updP P x a) x b = updP P x b := by
  funext y; simp only [updP]; split <;> rfl

/-- Slot `x` held as the opened instance `y1` (its `Seq` the model's). -/
theorem seqReadable_pt (γ : EpNames) (i : Nat) (inst : InstId → Option InstRec) (x : InstId)
    (w0 : InstRec) (p' : Loc) (y1 : epaxos.Instance) (hs : y1.Seq' = w0.seq) :
    SeqReadable (upd inst x (some w0))
      (updP (instAtP (GF := GF) γ i inst) x (fun pt => iprop(⌜pt = p'⌝ ∗ pt ↦ y1))) := by
  intro z pt w hw
  unfold updP
  by_cases hz : z = x
  · subst hz
    simp only [upd, if_true, Option.some.injEq] at hw
    subst hw
    simp only [if_true]
    iintro ⟨%Hpt, Hy⟩
    iexists y1
    iframe Hy
    isplitr
    · ipureintro; exact hs
    iintro Hy
    iframe Hy
    ipureintro; exact Hpt
  · simp only [hz, if_false]
    simp only [upd, hz, if_false] at hw
    exact instAtP_seq γ i inst z pt w hw

set_option maxHeartbeats 8000000 in
/-- `handlePreAccept(preAccept)`, with `PAWf`'s fields. -/
theorem wp_handlePreAccept_core (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (i : Nat)
    (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (ord : List w32)
    (σ : RState) (l : Loc) (m : PreAccept) (hrep : RepWf i σ ord)
    (hq : 0 ≤ zz m.replica ∧ zz m.replica < nR) (hn : 0 ≤ zz m.inst ∧ toN m.inst + 1 < MAX_INSTANCE)
    (hlead : toN m.leaderId < nR ∧ toN m.leaderId ≠ i ∧ 0 ≤ zz m.leaderId)
    (hdeps : depsOk m.deps) (hcmd : m.command ≠ []) (hconf : ConfWf σ)
    (houts : OutsWf (hPreAccept σ m).2) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ ownPreAccept l m (DFrac.own 1) ∗
        repFrag γ i (hPreAccept σ m).1 ∗ outsOk γ i (hPreAccept σ m).2 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"handlePreAccept"))
        (Val #l))
    {{ RET #(); repDone γ i r }} := by
  wp_start as ⟨#Hctx, Hrep, Hm, Hf, Houts⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  ihave #HDur := isReplicaFw_durable _ _ _ _ _ _ $$ Hfw
  rw [ownRep_unseal]; unfold ownRepDef
  icases Hrep with ⟨%Hib, %Hcb, Hinsts, Hcrt, Hcut, Heut, Hconf, Hmsk, HlS, HlP, HmaxSeq, Hlead, Hmrb,
    Hstore, Hpeer⟩
  ihave Hcls : clsArrs r σ.lastScan σ.lastPut $$ [HlS HlP]
  · unfold clsArrs; iframe
  unfold ownPreAccept
  icases Hm with ⟨%cs, %ds, Hm, Hcs, Hds⟩
  ihave %Hcsnn := ownCmds_nonnil _ _ _ hcmd $$ Hcs
  have hq' : toN m.replica < nR := by
    have := hq.1; have := hq.2; simp only [toN, zz] at *; omega
  have hn' : toN m.inst < MAX_INSTANCE := by have := hn.2; omega
  ihave Hinsts := (repInsts_P γ i r σ.inst).1 $$ Hinsts
  icases repInstsP_acc r _ ⟨toN m.replica, toN m.inst⟩ hq' hn' $$ Hinsts with
    ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  simp only [instAtP]
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
  ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
  wp_auto
  have e1 : sint.Z (W64 (sint.Z m.replica)) = sint.Z m.replica := by word
  have e2 : sint.Z (W64 (sint.Z m.inst)) = sint.Z m.inst := by word
  have hqe : (sint.Z m.replica).toNat = toN m.replica := rfl
  have hne : (sint.Z m.inst).toNat = toN m.inst := rfl
  have h1 : 0 ≤ sint.Z (W64 (sint.Z m.replica)) ∧ sint.Z (W64 (sint.Z m.replica)) < sint.Z iss.len := by
    have := hq.1; have hl := (List.getElem?_eq_some_iff.mp Hrow).1
    unfold toN zz at *; constructor <;> word
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
  · ipureintro; rw [e1, hqe]; exact Hrow
  have h2 : 0 ≤ sint.Z (W64 (sint.Z m.inst)) ∧ sint.Z (W64 (sint.Z m.inst)) < sint.Z row.len := by
    have := hn.1; have := hn.2; have := Hptr.2
    unfold toN zz at *; constructor <;> word
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
  · ipureintro; rw [e2, hne]; exact Hptr.1
  have hplen' : (sint.Z row.len) = ((ptrs.length : Nat) : Int) := by
    have := Hplen.1; have := Hplen.2; word
  ipersist r
  ipersist preAccept
  -- maxSeq
  wp_join iprop(efld r go!"maxSeq" ↦ paMs σ m ∗ l ↦ epaxos.PreAccept.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds) with [HmaxSeq Hm] as ⟨HmaxSeq, Hm⟩
  · unfold paMs; rw [if_pos ((sle_iff _ _).mpr Hif)]; iframe
  · unfold paMs; rw [if_neg (fun h => Hif ((sle_iff _ _).mp h))]; iframe
  -- maxRecvBallot
  wp_join iprop(efld r go!"maxRecvBallot" ↦ (bumpRecvBallot σ m.ballot).maxRecvBallot ∗ l ↦ epaxos.PreAccept.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds)
    with [Hmrb Hm] as ⟨Hmrb, Hm⟩
  · rw [bumpRecvBallot_true _ _ (by simpa using Hif)]
    iframe
  · rw [bumpRecvBallot_false _ _ (by simpa using Hif)]
    iframe
  -- crtInstance
  unfold repRowArr
  icases Hcrt with ⟨%crt, #Hcrtf, Hcrtsl⟩
  ihave %Hclen := ownSlice_len _ _ _ $$ Hcrtsl
  wp_auto
  have hclen : ((List.range nR).map σ.crtInstance).length = nR := by simp
  have h3 : 0 ≤ sint.Z (W64 (sint.Z m.replica)) ∧ sint.Z (W64 (sint.Z m.replica)) < sint.Z crt.len := by
    have := hq.1; have := hq.2; simp only [toN, zz] at *; constructor <;> word
  simp only [h3, _root_.and_self, ↓reduceIte]
  have hcv : ((List.range nR).map σ.crtInstance)[(sint.Z (W64 (sint.Z m.replica))).toNat]? =
      some (σ.crtInstance (toN m.replica)) := by
    rw [e1, hqe]; simp [hq']
  wp_apply wp_load_slice_index crt _ _ _ _ h3.1 $$ [$Hcrtsl] as Hcrtsl
  · ipureintro; exact hcv
  wp_join iprop(crt ↦* ((List.range nR).map (bumpCrt σ (toN m.replica) m.inst).crtInstance) ∗ l ↦ epaxos.PreAccept.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds)
    with [Hcrtsl Hm] as ⟨Hcrtsl, Hm⟩
  · have h3' : 0 ≤ sint.Z (W64 (sint.Z m.replica)) ∧
        sint.Z (W64 (sint.Z m.replica)) < ((List.range nR).map σ.crtInstance).length := by
      rw [hclen]; have := hq.1; have := hq.2; simp only [toN, zz] at *; constructor <;> word
    try simp only [h3, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [$Hcrtsl] as Hcrtsl
    · ipureintro; exact h3'
    wp_join_done
    rw [bumpCrt_crt_true σ _ _ Hif, map_range_upd _ _ _ _ hq', e1, hqe]
    iframe Hm; iexact Hcrtsl
  · rw [bumpCrt_crt_false σ _ _ Hif]; iframe Hm; iexact Hcrtsl
  -- the instance, created if nil
  have hxq : W32 (toN m.replica : Int) = m.replica := by
    have := hq.1; simp only [toN, zz] at *; word
  have hxi : W32 (toN m.inst : Int) = m.inst := by
    have := hn.1; simp only [toN, zz] at *; word
  wp_join iprop(∃ p', inst_ptr ↦ p' ∗ row ↦* ptrs.set (toN m.inst) p' ∗
      ownInst γ i ⟨toN m.replica, toN m.inst⟩ p' (paW0 σ m) ∗ l ↦ epaxos.PreAccept.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds)
    with [inst Hptrs Hx Hm]
  · -- nil: `newInstanceDefault`
    rcases hx : σ.inst ⟨toN m.replica, toN m.inst⟩ with _ | w0
    case some =>
      unfold instAt ownInst
      icases Hx with ⟨%y, Hy, -⟩
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hy
      exact (Hnn rfl).elim
    wp_apply wp_newInstanceDefault as %p' ⟨%Hp'nn, %t, %idp, Hp', Hid⟩
    ipersist Hid
    simp only [h1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
    · ipureintro; rw [e1, hqe]; exact Hrow
    simp only [h2, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [$Hptrs] as Hptrs
    · ipureintro; rw [← hplen'] ; exact h2
    rw [e2, hne]
    wp_join_done
    iexists p'
    iframe inst Hptrs Hm
    have hd : paW0 σ m = newInstanceDefault ⟨toN m.replica, toN m.inst⟩ := by
      simp [paW0, getOrDefault, hx]
    rw [hd]
    iapply ownInst_default
    iframe Hp'
    rw [hxq, hxi]; iexact Hid
  · -- not nil: the instance exists
    rcases hx : σ.inst ⟨toN m.replica, toN m.inst⟩ with _ | w0
    · unfold instAt; icases Hx with %Hnull
      exact (Hif Hnull).elim
    unfold instAt
    iexists ptr
    have hset : ptrs.set (toN m.inst) ptr = ptrs := by
      have := List.getElem?_eq_some_iff.mp Hptr.1
      rw [← this.2]; exact List.set_getElem_self this.1
    rw [hset]
    have hd : paW0 σ m = w0 := by simp [paW0, getOrDefault, hx]
    rw [hd]
    iframe
  iintro ⟨%p', inst, Hptrs, Hx, Hm⟩
  unfold ownInst
  icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
  ihave %Hp'nn := typedPointsto_not_null _ _ _ $$ Hy
  wp_auto
  rw [show decide (p' = null) = false from decide_eq_false Hp'nn]
  simp only [Bool.not_false]
  wp_auto
  have hib' : instBounds (upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (paW0 σ m))) :=
    instBounds_upd _ _ _ Hib hq' hn.2
  wp_if_destruct
  · -- a lower ballot: dropped
    have hlow : m.ballot.slt (paW0 σ m).bal = true :=
      (slt_iff _ _).mpr (by rw [← Hyf.1]; exact Hif)
    rw [hPreAccept_eq, if_pos hlow]
    ihave Hidle := outsOk_idle (GF := GF) γ i [] (fun o ho => by simp at ho) $$ Houts
    ihave Hins := Hclose $$ %p' %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some (paW0 σ m))) Hptrs
      [Hy Hycmds Hydeps Hylb]
    · unfold instAt ownInst; iexists y; iframe Hy Hycmds Hydeps Hylb
      isplitr
      · ipureintro; exact Hyf
      · iexact Hyid
    ihave Hins := repInsts_updP (GF := GF) γ i r σ.inst ⟨toN m.replica, toN m.inst⟩ (some (paW0 σ m)) $$ Hins
    iapply HΦ
    unfold repDone
    iexists paPre σ m
    iframe Hf Hidle
    rw [ownRep_unseal]; unfold ownRepDef
    simp only [paPre]
    unfold clsArrs
    icases Hcls with ⟨HlS, HlP⟩
    iframe HlS HlP
    unfold repRowArr
    iframe Hins Hcut Heut Hconf Hmsk HmaxSeq Hlead Hstore Hpeer Hmrb
    isplitr
    · ipureintro; exact hib'
    isplitr
    · ipureintro; exact Hcb
    iexists crt; iframe Hcrtf Hcrtsl
  have hnl : m.ballot.slt (paW0 σ m).bal = false := by
    rcases h : m.ballot.slt (paW0 σ m).bal
    · rfl
    · exact absurd ((slt_iff _ _).mp h) (by rw [← Hyf.1]; exact Hif)
  have hcf : (paFin σ m).conflicts = paCf σ m := by rw [paFin_eq]
  have hmk : (paFin σ m).maxSeqPerKey = paMk σ m := by rw [paFin_eq]
  have hls : (paFin σ m).lastScan = paLS σ m := by rw [paFin_eq]
  have hlp : (paFin σ m).lastPut = paLP σ m := by rw [paFin_eq]
  icases Hydeps with ⟨%dq, Hydeps⟩
  imod ownSlice_persist $$ Hydeps with #Hydeps
  imod ownCmds_persist _ _ _ $$ Hcs with #Hcs
  wp_join iprop(∃ y' : epaxos.Instance, inst_ptr ↦ p' ∗ p' ↦ y' ∗
      ⌜y'.bal' = (paW2 σ m).bal ∧ y'.vbal' = (paW2 σ m).vbal ∧ y'.Status' = (paW2 σ m).status ∧
        y'.Seq' = (paW2 σ m).seq⌝ ∗ y'.Deps' ↦*□ (paW2 σ m).deps ∗
      (p' ↦ y' -∗ ownInst γ i ⟨toN m.replica, toN m.inst⟩ p' (paW2 σ m)) ∗
      (ownInst γ i ⟨toN m.replica, toN m.inst⟩ p' (paW2 σ m) -∗ repInsts γ i r (upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (paW2 σ m)))) ∗
      repConf r (paFin σ m).conflicts ∗ repMsk r (paFin σ m).maxSeqPerKey ∗
      clsArrs r (paFin σ m).lastScan (paFin σ m).lastPut ∗ l ↦ epaxos.PreAccept.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds)
    with [inst Hy Hycmds Hylb Hclose Hptrs Hconf Hmsk Hcls Hm Hds]
    as ⟨%y', inst, Hy, %Hy'f, #Hy'd, Hown, Hcl, Hconf, Hmsk, Hcls, Hm⟩
  · -- ACCEPTED or later
    have hacc : paAcc σ m = true := (stGe_iff _ _).mpr (by rw [← Hyf.2.2.1]; exact Hif)
    rw [show (paW2 σ m).status = (paW0 σ m).status by
      unfold paW2; simp only [hacc, if_true]
      by_cases h : (paW0 σ m).cmds = none <;> simp [h]]
    rcases hc : (paW0 σ m).cmds with _ | c
    · -- no commands yet: recorded
      have hW : paW2 σ m = { paW0 σ m with bal := m.ballot, cmds := some m.command } := by
        unfold paW2; simp [hacc, hc]
      have hcf1 : paCf σ m = (updateConflicts σ m.command (toN m.replica) m.inst m.seq).conflicts := by
        unfold paCf; simp [hacc, hc]
      have hmk1 : paMk σ m =
          (updateConflicts σ m.command (toN m.replica) m.inst m.seq).maxSeqPerKey := by
        unfold paMk; simp [hacc, hc]
      have hls1 : paLS σ m = (updateConflicts σ m.command (toN m.replica) m.inst m.seq).lastScan := by
        unfold paLS; simp [hacc, hc]
      have hlp1 : paLP σ m = (updateConflicts σ m.command (toN m.replica) m.inst m.seq).lastPut := by
        unfold paLP; simp [hacc, hc]
      unfold clsArrs
      icases Hcls with ⟨HlS, HlP⟩
      unfold cmdsRep
      icases Hycmds with %Hcn
      rw [show decide (y.Cmds' = slice.nil) = true from decide_eq_true Hcn]
      wp_auto
      wp_apply (wp_updateConflicts r σ cs m.command DFrac.discard m.replica m.inst m.seq hq)
        $$ [$Hpe $Hcs $Hconf $Hmsk $HlS $HlP] as ⟨-, Hconf, Hmsk, HlS, HlP⟩
      wp_apply wp_recordCommands $$ [$Hrr $HDur]
      wp_apply wp_sync $$ [$Hrr $HDur]
      wp_join_done
      iexists (epaxos.Instance.mk cs m.ballot y.vbal' y.Status' y.Seq' y.Deps' y.lb' y.Index' y.Lowlink' y.bfilter' y.proposeTime' y.id')
      iframe inst Hm
      isplitl [Hy]
      · iexact Hy
      isplitr
      · ipureintro; rw [hW]; exact ⟨rfl, Hyf.2.1, Hyf.2.2.1, Hyf.2.2.2.1⟩
      isplitr
      · rw [hW]; iexact Hydeps
      isplitl [Hylb]
      · iintro Hy
        unfold ownInst
        iexists (epaxos.Instance.mk cs m.ballot y.vbal' y.Status' y.Seq' y.Deps' y.lb' y.Index' y.Lowlink' y.bfilter' y.proposeTime' y.id')
        rw [hW]
        iframe Hy Hylb
        isplitr
        · ipureintro; exact ⟨rfl, Hyf.2.1, Hyf.2.2.1, Hyf.2.2.2.1, Hyf.2.2.2.2⟩
        isplitr
        · iexact Hyid
        isplitl []
        · simp only [cmdsRep]
          isplitl []
          · ipureintro; exact Hcsnn
          · iexact Hcs
        iexists DFrac.discard; iexact Hydeps
      isplitl [Hclose Hptrs]
      · iintro Hx
        ihave Hins := Hclose $$ %p' %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some (paW2 σ m))) Hptrs [Hx]
        · dsimp only [instAt]; iexact Hx
        iapply repInsts_updP γ i r σ.inst ⟨toN m.replica, toN m.inst⟩ (some (paW2 σ m))
        iexact Hins
      rw [hcf, hmk, hcf1, hmk1, hls, hlp, hls1, hlp1]
      iframe
    · -- commands already: nothing recorded
      have hW : paW2 σ m = { paW0 σ m with bal := m.ballot } := by
        unfold paW2; simp [hacc, hc]
      have hcf1 : paCf σ m = σ.conflicts := by unfold paCf; simp [hacc, hc]
      have hmk1 : paMk σ m = σ.maxSeqPerKey := by unfold paMk; simp [hacc, hc]
      have hls1 : paLS σ m = σ.lastScan := by unfold paLS; simp [hacc, hc]
      have hlp1 : paLP σ m = σ.lastPut := by unfold paLP; simp [hacc, hc]
      ihave Hycmds' := cmdsRep_dup2 _ _ $$ Hycmds
      icases Hycmds' with ⟨Hycmds, Hyc2⟩
      unfold cmdsRep
      icases Hyc2 with ⟨%Hcn, -⟩
      rw [show decide (y.Cmds' = slice.nil) = false from decide_eq_false Hcn]
      wp_auto
      wp_join_done
      iexists (epaxos.Instance.mk y.Cmds' m.ballot y.vbal' y.Status' y.Seq' y.Deps' y.lb' y.Index' y.Lowlink' y.bfilter' y.proposeTime' y.id')
      iframe inst Hm
      isplitl [Hy]
      · iexact Hy
      isplitr
      · ipureintro; rw [hW]; exact ⟨rfl, Hyf.2.1, Hyf.2.2.1, Hyf.2.2.2.1⟩
      isplitr
      · rw [hW]; iexact Hydeps
      isplitl [Hycmds Hylb]
      · iintro Hy
        unfold ownInst
        iexists (epaxos.Instance.mk y.Cmds' m.ballot y.vbal' y.Status' y.Seq' y.Deps' y.lb' y.Index' y.Lowlink' y.bfilter' y.proposeTime' y.id')
        rw [hW]
        iframe Hy Hylb
        isplitr
        · ipureintro; exact ⟨rfl, Hyf.2.1, Hyf.2.2.1, Hyf.2.2.2.1, Hyf.2.2.2.2⟩
        isplitr
        · iexact Hyid
        isplitl [Hycmds]
        · rw [hc]; simp only [cmdsRep]; iexact Hycmds
        iexists DFrac.discard; iexact Hydeps
      isplitl [Hclose Hptrs]
      · iintro Hx
        ihave Hins := Hclose $$ %p' %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some (paW2 σ m))) Hptrs [Hx]
        · dsimp only [instAt]; iexact Hx
        iapply repInsts_updP γ i r σ.inst ⟨toN m.replica, toN m.inst⟩ (some (paW2 σ m))
        iexact Hins
      rw [hcf, hmk, hcf1, hmk1, hls, hlp, hls1, hlp1]
      iframe
  · -- PREACCEPTED: `updateAttributes`, the slot readable (its `Seq` the model's)
    have hacc : paAcc σ m = false := by
      rcases h : paAcc σ m
      · rfl
      · exact absurd ((stGe_iff _ _).mp h) (by rw [← Hyf.2.2.1]; exact Hif)
    ihave Hy : p' ↦ epaxos.Instance.mk y.Cmds' m.ballot y.vbal' y.Status' y.Seq' y.Deps' y.lb' y.Index' y.Lowlink' y.bfilter' y.proposeTime' y.id' $$ [Hy]
    · iexact Hy
    ihave Hins := Hclose $$ %p' %(fun pt => iprop(⌜pt = p'⌝ ∗ pt ↦ epaxos.Instance.mk y.Cmds' m.ballot y.vbal' y.Status' y.Seq' y.Deps' y.lb' y.Index' y.Lowlink' y.bfilter' y.proposeTime' y.id')) Hptrs [Hy]
    · dsimp only
      isplitr
      · ipureintro; rfl
      iexact Hy
    have hSeq := seqReadable_pt (GF := GF) γ i σ.inst ⟨toN m.replica, toN m.inst⟩ (paW0 σ m) p' (epaxos.Instance.mk y.Cmds' m.ballot y.vbal' y.Status' y.Seq' y.Deps' y.lb' y.Index' y.Lowlink' y.bfilter' y.proposeTime' y.id') Hyf.2.2.2.1
    have hconf' : ConfWf (paPre σ m) := confWf_upd σ ⟨toN m.replica, toN m.inst⟩ (paW0 σ m) hconf _ rfl rfl rfl rfl
    unfold ownDeps
    ihave Hconf : repConf r (paPre σ m).conflicts $$ [Hconf]
    · rw [show (paPre σ m).conflicts = σ.conflicts from rfl]; iexact Hconf
    ihave Hmsk : repMsk r (paPre σ m).maxSeqPerKey $$ [Hmsk]
    · rw [show (paPre σ m).maxSeqPerKey = σ.maxSeqPerKey from rfl]; iexact Hmsk
    unfold clsArrs
    icases Hcls with ⟨HlS, HlP⟩
    ihave HlS : repRowArr r go!"lastScan" (paPre σ m).lastScan $$ [HlS]
    · rw [show (paPre σ m).lastScan = σ.lastScan from rfl]; iexact HlS
    ihave HlP : repRowArr r go!"lastPut" (paPre σ m).lastPut $$ [HlP]
    · rw [show (paPre σ m).lastPut = σ.lastPut from rfl]; iexact HlP
    wp_apply (wp_updateAttributes γ i r rr L p (paPre σ m) _ hSeq hconf' hib' cs m.command
      DFrac.discard m.seq ds m.deps hdeps m.replica m.inst)
      $$ [$Hpe $Hrr $Hfro $Hins $Hconf $Hmsk $HlS $HlP $Hcs $Hds]
      as ⟨Hins, Hconf, Hmsk, HlS, HlP, -, Hds⟩
    rw [show updateAttributes (paPre σ m) m.command m.seq m.deps = paAttrs σ m from rfl]
    -- the slot again
    icases repInstsP_acc r _ ⟨toN m.replica, toN m.inst⟩ hq' hn' $$ Hins with
      ⟨%iss2, %rows2, %row2, %ptrs2, %pt2, #Hiss2, #Hrows2, %Hrow2, Hptrs2, %Hptr2, HQ, Hclose2⟩
    simp only [updP, if_true]
    icases HQ with ⟨%Hpt2, Hy⟩
    subst pt2
    icombine Hiss Hiss2 gives %Heqi
    subst Heqi
    ihave %Heqr := ownSlice_agree _ _ _ _ _ $$ Hrows Hrows2
    subst Heqr
    have Heqrow : row2 = row := by rw [Hrow] at Hrow2; exact (Option.some.inj Hrow2).symm
    subst row2
    unfold epaxos.PREACCEPTED_EQ epaxos.PREACCEPTED
    wp_auto
    wp_join iprop(status_ptr ↦ (if (paAttrs σ m).2.2 then stPREACCEPTED else stPREACCEPTED_EQ))
      at next with [status] as status
    · rcases hch : (paAttrs σ m).2.2
      · simp only [Bool.false_eq_true, ite_false]
        wp_auto
        wp_join_done
      · simp only [ite_true]
        wp_auto
        wp_join_done
    ihave Hconf : repConf r σ.conflicts $$ [Hconf]
    · iexact Hconf
    ihave Hmsk : repMsk r σ.maxSeqPerKey $$ [Hmsk]
    · iexact Hmsk
    ihave HlS : repRowArr r go!"lastScan" σ.lastScan $$ [HlS]
    · iexact HlS
    ihave HlP : repRowArr r go!"lastPut" σ.lastPut $$ [HlP]
    · iexact HlP
    wp_apply (wp_updateConflicts r σ cs m.command DFrac.discard m.replica m.inst m.seq hq)
      $$ [$Hpe $Hcs $Hconf $Hmsk $HlS $HlP] as ⟨-, Hconf, Hmsk, HlS, HlP⟩
    simp only [h1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
    · ipureintro; rw [e1, hqe]; exact Hrow
    simp only [h2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index row _ ptrs2 _ p' h2.1 $$ [$Hptrs2] as Hptrs2
    · ipureintro; rw [e2, hne]; exact Hptr2.1
    wp_apply wp_recordInstanceMetadata $$ [$Hrr $HDur]
    wp_apply wp_recordCommands $$ [$Hrr $HDur]
    imod ownSlice_persist $$ Hds with #Hds
    wp_apply wp_sync $$ [$Hrr $HDur]
    wp_join_done
    have hW : paW2 σ m = { paW0 σ m with
        cmds := some m.command
        seq := (paAttrs σ m).1
        deps := (paAttrs σ m).2.1
        bal := m.ballot
        vbal := m.ballot
        status := if (paAttrs σ m).2.2 then stPREACCEPTED else stPREACCEPTED_EQ } := by
      unfold paW2; simp [hacc]
    have hcf1 : paCf σ m = (updateConflicts σ m.command (toN m.replica) m.inst m.seq).conflicts := by
      unfold paCf; simp [hacc]
    have hmk1 : paMk σ m = (updateConflicts σ m.command (toN m.replica) m.inst m.seq).maxSeqPerKey := by
      unfold paMk; simp [hacc]
    have hne0 : (paW0 σ m).status ≠ stEXECUTED := by
      intro h; unfold paAcc at hacc; rw [h] at hacc; revert hacc; decide
    have hd1 : decide ((paW0 σ m).status = stEXECUTED) = false := decide_eq_false hne0
    have hd2 : decide ((paW2 σ m).status = stEXECUTED) = false := by
      rw [hW]; split <;> rfl
    iexists (epaxos.Instance.mk cs m.ballot m.ballot (if (paAttrs σ m).2.2 then stPREACCEPTED else stPREACCEPTED_EQ) (paAttrs σ m).1 ds y.lb' y.Index' y.Lowlink' y.bfilter' y.proposeTime' y.id')
    iframe inst Hm
    isplitl [Hy]
    · iexact Hy
    isplitr
    · ipureintro; rw [hW]; exact ⟨rfl, rfl, rfl, rfl⟩
    isplitr
    · rw [hW]; iexact Hds
    isplitl [Hylb]
    · iintro Hy
      unfold ownInst
      iexists (epaxos.Instance.mk cs m.ballot m.ballot (if (paAttrs σ m).2.2 then stPREACCEPTED else stPREACCEPTED_EQ) (paAttrs σ m).1 ds y.lb' y.Index' y.Lowlink' y.bfilter' y.proposeTime' y.id')
      simp only [hd1, hd2]
      rw [hW]
      iframe Hy
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl, fun _ => Hyf.2.2.2.2 hne0⟩
      isplitr
      · iexact Hyid
      isplitl []
      · simp only [cmdsRep]
        isplitl []
        · ipureintro; exact Hcsnn
        · iexact Hcs
      isplitl []
      · iexists DFrac.discard; iexact Hds
      iexact Hylb
    isplitl [Hclose2 Hptrs2]
    · iintro Hx
      have hset2 : ptrs2.set (toN m.inst) p' = ptrs2 := by
        have := List.getElem?_eq_some_iff.mp Hptr2.1
        rw [← this.2]; exact List.set_getElem_self this.1
      ihave Hins := Hclose2 $$ %p' %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some (paW2 σ m))) [Hptrs2] [Hx]
      · rw [hset2]; iexact Hptrs2
      · dsimp only [instAt]; iexact Hx
      rw [pa_updP_updP]
      iapply repInsts_updP γ i r σ.inst ⟨toN m.replica, toN m.inst⟩ (some (paW2 σ m))
      iexact Hins
    have hls1 : paLS σ m = (updateConflicts σ m.command (toN m.replica) m.inst m.seq).lastScan := by
      unfold paLS; simp [hacc]
    have hlp1 : paLP σ m = (updateConflicts σ m.command (toN m.replica) m.inst m.seq).lastPut := by
      unfold paLP; simp [hacc]
    rw [hcf, hmk, hcf1, hmk1, hls, hlp, hls1, hlp1]
    iframe
  -- the reply
  icases Hcut with ⟨%cutsl, #Hcutf, Hcutsl⟩
  wp_auto
  have hlid : W32 ((toN m.leaderId : Nat) : Int) = m.leaderId := by
    have := hlead.2.2; simp only [toN, zz] at *; word
  have hres := hPreAccept_eq σ m
  rw [hnl] at hres
  simp only [Bool.false_eq_true, ite_false] at hres
  have hwfr : (Msg.preAcceptReply (paReply σ m)).wf := by
    have := houts; rw [hres] at this
    exact this _ (List.mem_append_right _ (List.mem_singleton_self _))
  rw [hres]
  icases outsOk_send γ i (paEvs σ m) _ _ (paEvs_noSends σ m) hlead.1 $$ Houts with ⟨Ho, Hidle⟩
  have hcl : (paFin σ m).committedList = (List.range nR).map σ.committedUpTo := by
    rw [paFin_eq]; rfl
  ihave Hr : «$r0_ptr» ↦ epaxos.PreAcceptReply.mk (paReply σ m).replica (paReply σ m).inst
      (paReply σ m).ballot (paReply σ m).vballot (paReply σ m).seq y'.Deps' cutsl
      (paReply σ m).status $$ [«$r0»]
  · simp only [paReply]
    rw [← Hy'f.1, ← Hy'f.2.1, ← Hy'f.2.2.1, ← Hy'f.2.2.2]
    iexact «$r0»
  ihave Hcutsl : cutsl ↦* (paReply σ m).committedDeps $$ [Hcutsl]
  · simp only [paReply]; rw [hcl]; iexact Hcutsl
  wp_apply (wp_replyPreAccept_frac hS γ i r rr L p Rext ord (toN m.leaderId) m.leaderId hlid
    «$r0_ptr» (paReply σ m) y'.Deps' cutsl DFrac.discard (DFrac.own 1) ⟨hlead.1, hlead.2.1⟩ hwfr)
    $$ [Ho Hr Hcutsl] as ⟨Ho, -, Hcutsl⟩
  · iframe Ho Hr Hcutsl
    isplitl []
    · unfold hdCtx; iexact Hctx0
    simp only [paReply]; iexact Hy'd
  ihave Hidle := Hidle $$ Ho
  ihave Hcutsl : cutsl ↦* List.map σ.committedUpTo (List.range nR) $$ [Hcutsl]
  · rw [← hcl]; iexact Hcutsl
  -- the state
  ihave Hx := Hown $$ Hy
  ihave Hins := Hcl $$ Hx
  iapply HΦ
  unfold repDone
  iexists paFin σ m
  iframe Hf Hidle
  rw [ownRep_unseal]; unfold ownRepDef
  rw [hls, hlp]
  rw [paFin_eq]
  unfold clsArrs
  icases Hcls with ⟨HlS, HlP⟩
  iframe HlS HlP
  unfold repRowArr
  iframe Hins Heut Hconf Hmsk HmaxSeq Hlead Hstore Hpeer Hmrb
  isplitr
  · ipureintro; exact instBounds_upd _ _ _ Hib hq' hn.2
  isplitr
  · ipureintro; exact Hcb
  isplitl [Hcrtsl]
  · iexists crt; iframe Hcrtf Hcrtsl
  iexists cutsl; iframe Hcutf
  iexact Hcutsl

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
