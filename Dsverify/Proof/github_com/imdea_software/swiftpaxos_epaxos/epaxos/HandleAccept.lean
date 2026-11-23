/-
`(*Replica).handleAccept` against the model's `hAccept`: `maxRecvBallot`, `crtInstance`, the
instance (created if nil); a lower ballot is dropped (no reply); otherwise the instance takes the
Accept's value (unless committed) and the reply (`replyAccept` → `SendMsg`) carries its ballot.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandlePrepare
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Record
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.StartPhase1

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

/-! ## `hAccept`, named -/

/-- The instance `handleAccept` finds (created if nil). -/
def accW0 (σ : RState) (m : Accept) : InstRec :=
  (getOrDefault σ ⟨toN m.replica, toN m.inst⟩).2

/-- The state after the first statements (`maxRecvBallot`, `crtInstance`, the instance). -/
def accPre (σ : RState) (m : Accept) : RState :=
  { σ with crtInstance := (bumpCrt σ (toN m.replica) m.inst).crtInstance,
           maxRecvBallot := (bumpRecvBallot σ m.ballot).maxRecvBallot,
           inst := upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (accW0 σ m)) }

/-- The accepted instance. -/
def accInst (σ : RState) (m : Accept) : InstRec :=
  { accW0 σ m with cmds := some m.command, deps := m.deps, seq := m.seq, bal := m.ballot,
                   vbal := m.ballot, status := stACCEPTED }

/-- The reply, for the instance `w` the handler ends with. -/
def accReply (m : Accept) (w : InstRec) : AcceptReply :=
  { replica := m.replica, inst := m.inst, ballot := w.bal }

theorem hAccept_pre (σ : RState) (m : Accept) :
    (getOrDefault (bumpCrt (bumpRecvBallot σ m.ballot) (toN m.replica) m.inst)
      ⟨toN m.replica, toN m.inst⟩).1 = accPre σ m ∧
    (getOrDefault (bumpCrt (bumpRecvBallot σ m.ballot) (toN m.replica) m.inst)
      ⟨toN m.replica, toN m.inst⟩).2 = accW0 σ m := by
  have e : (getOrDefault (bumpCrt (bumpRecvBallot σ m.ballot) (toN m.replica) m.inst)
      ⟨toN m.replica, toN m.inst⟩).2 = (getOrDefault σ ⟨toN m.replica, toN m.inst⟩).2 := by
    apply getOrDefault_snd_inst
    unfold bumpRecvBallot bumpCrt; split <;> split <;> rfl
  refine ⟨?_, e⟩
  rw [getOrDefault_fst, e]
  unfold accPre accW0 bumpRecvBallot bumpCrt
  split <;> split <;> simp_all

theorem accPre_self (σ : RState) (m : Accept) :
    (accPre σ m).setInst ⟨toN m.replica, toN m.inst⟩ (accW0 σ m) = accPre σ m := by
  simp only [accPre, RState.setInst, upd_upd]

theorem hAccept_eq (σ : RState) (m : Accept) :
    hAccept σ m =
      if m.ballot.slt (accW0 σ m).bal then (accPre σ m, [])
      else if stGe (accW0 σ m).status stCOMMITTED then
        ((accPre σ m).setInst ⟨toN m.replica, toN m.inst⟩ (accW0 σ m),
          [] ++ [Out.send (toN m.leaderId) (.acceptReply (accReply m (accW0 σ m)))])
      else
        ((accPre σ m).setInst ⟨toN m.replica, toN m.inst⟩ (accInst σ m),
          [Out.ev (.vote ⟨toN m.replica, toN m.inst⟩ m.ballot stACCEPTED
            ⟨m.command, m.seq, m.deps⟩)] ++
          [Out.send (toN m.leaderId) (.acceptReply (accReply m (accInst σ m)))]) := by
  obtain ⟨e1, e2⟩ := hAccept_pre σ m
  unfold hAccept
  simp only
  rcases hg : getOrDefault (bumpCrt (bumpRecvBallot σ m.ballot) (toN m.replica) m.inst)
    ⟨toN m.replica, toN m.inst⟩ with ⟨σ3, w⟩
  rw [hg] at e1 e2
  simp only at e1 e2 ⊢
  subst e1 e2
  rw [accPre_self]
  split
  · rfl
  · split
    · rfl
    · rfl

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- The handler's message: an `*Accept` (owned), its command slice not `nil` (decoded: Go's
`make` never returns `nil`; as `ownPrepareReplyNN`). -/
def ownAcceptNN (l : Loc) (m : Accept) : IProp GF :=
  iprop(∃ cs ds : GoSlice, l ↦ epaxos.Accept.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds ∗
      ownCmds cs m.command (DFrac.own 1) ∗ ownDeps ds m.deps (DFrac.own 1) ∗ ⌜cs ≠ slice.nil⌝)

/-- What `handleAccept` needs of the state and the message (message ids in range,
`Inv.msgWf`; the sender a peer). -/
structure AccWf (i : Nat) (σ : RState) (ord : List w32) (m : Accept) : Prop where
  hrep : RepWf i σ ord
  hq : 0 ≤ zz m.replica ∧ zz m.replica < nR
  hn : 0 ≤ zz m.inst ∧ toN m.inst + 1 < MAX_INSTANCE
  hl : 0 ≤ zz m.leaderId ∧ toN m.leaderId < nR ∧ toN m.leaderId ≠ i

set_option maxHeartbeats 4000000 in
/-- **`handleAccept(accept)`**: from the instance lock's contents, the message, and the ghost
step's outputs, the handler ends in the lock's invariant shape. -/
theorem wp_handleAccept (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (i : Nat) (r rr : Loc)
    (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (ord : List w32) (σ : RState)
    (l : Loc) (m : Accept) (hw : AccWf i σ ord m) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ ownAcceptNN l m ∗
        repFrag γ i (hAccept σ m).1 ∗ outsOk γ i (hAccept σ m).2 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"handleAccept")) (Val #l))
    {{ RET #(); repDone γ i r }} := by
  wp_start as ⟨#Hctx, Hrep, Hm, Hf, Houts⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  rw [ownRep_unseal]; unfold ownRepDef
  icases Hrep with ⟨%Hib, %Hcb, Hinsts, Hcrt, Hcut, Heut, Hconf, Hmsk, HlS, HlP, HmaxSeq, Hlead, Hmrb,
    Hstore, Hpeer⟩
  unfold ownAcceptNN
  icases Hm with ⟨%cs, %ds, Hm, Hcs, Hds, %Hcsnn⟩
  have hq : toN m.replica < nR := by
    have := hw.hq.1; have := hw.hq.2; simp only [toN, zz] at *; omega
  have hn : toN m.inst < MAX_INSTANCE := by have := hw.hn.2; omega
  icases repInsts_acc γ i r σ.inst ⟨toN m.replica, toN m.inst⟩ hq hn $$ Hinsts with
    ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
  ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
  wp_auto
  have e1 : sint.Z (W64 (sint.Z m.replica)) = sint.Z m.replica := by word
  have e2 : sint.Z (W64 (sint.Z m.inst)) = sint.Z m.inst := by word
  have hq' : (sint.Z m.replica).toNat = toN m.replica := rfl
  have hn' : (sint.Z m.inst).toNat = toN m.inst := rfl
  have h1 : 0 ≤ sint.Z (W64 (sint.Z m.replica)) ∧ sint.Z (W64 (sint.Z m.replica)) < sint.Z iss.len := by
    have := hw.hq.1; have hl := (List.getElem?_eq_some_iff.mp Hrow).1
    unfold toN zz at *; constructor <;> word
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
  · ipureintro; rw [e1, hq']; exact Hrow
  have h2 : 0 ≤ sint.Z (W64 (sint.Z m.inst)) ∧ sint.Z (W64 (sint.Z m.inst)) < sint.Z row.len := by
    have := hw.hn.1; have := hw.hn.2; have := Hptr.2
    unfold toN zz at *; constructor <;> word
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
  · ipureintro; rw [e2, hn']; exact Hptr.1
  have hplen' : (sint.Z row.len) = ((ptrs.length : Nat) : Int) := by
    have := Hplen.1; have := Hplen.2; word
  ipersist r
  ipersist accept
  -- maxRecvBallot
  wp_join iprop(efld r go!"maxRecvBallot" ↦ (bumpRecvBallot σ m.ballot).maxRecvBallot ∗ l ↦ epaxos.Accept.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds)
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
    have := hw.hq.1; have := hw.hq.2; simp only [toN, zz] at *; constructor <;> word
  simp only [h3, _root_.and_self, ↓reduceIte]
  have hcv : ((List.range nR).map σ.crtInstance)[(sint.Z (W64 (sint.Z m.replica))).toNat]? =
      some (σ.crtInstance (toN m.replica)) := by
    rw [e1, hq']; simp [hq]
  wp_apply wp_load_slice_index crt _ _ _ _ h3.1 $$ [$Hcrtsl] as Hcrtsl
  · ipureintro; exact hcv
  wp_join iprop(crt ↦* ((List.range nR).map (bumpCrt σ (toN m.replica) m.inst).crtInstance) ∗ l ↦ epaxos.Accept.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds)
    with [Hcrtsl Hm] as ⟨Hcrtsl, Hm⟩
  · have h3' : 0 ≤ sint.Z (W64 (sint.Z m.replica)) ∧
        sint.Z (W64 (sint.Z m.replica)) < ((List.range nR).map σ.crtInstance).length := by
      rw [hclen]; have := hw.hq.1; have := hw.hq.2; simp only [toN, zz] at *; constructor <;> word
    try simp only [h3, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [$Hcrtsl] as Hcrtsl
    · ipureintro; exact h3'
    wp_join_done
    rw [bumpCrt_crt_true σ _ _ Hif, map_range_upd _ _ _ _ hq, e1, hq']
    iframe Hm; iexact Hcrtsl
  · rw [bumpCrt_crt_false σ _ _ Hif]; iframe Hm; iexact Hcrtsl
  -- the instance, created if nil
  have hxq : W32 (toN m.replica : Int) = m.replica := by
    have := hw.hq.1; simp only [toN, zz] at *; word
  have hxi : W32 (toN m.inst : Int) = m.inst := by
    have := hw.hn.1; simp only [toN, zz] at *; word
  wp_join iprop(∃ p', inst_ptr ↦ p' ∗ row ↦* ptrs.set (toN m.inst) p' ∗
      ownInst γ i ⟨toN m.replica, toN m.inst⟩ p' (accW0 σ m) ∗ l ↦ epaxos.Accept.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds)
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
    · ipureintro; rw [e1, hq']; exact Hrow
    simp only [h2, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [$Hptrs] as Hptrs
    · ipureintro; rw [← hplen'] ; exact h2
    rw [e2, hn']
    wp_join_done
    iexists p'
    iframe inst Hptrs Hm
    have hd : accW0 σ m = newInstanceDefault ⟨toN m.replica, toN m.inst⟩ := by
      simp [accW0, getOrDefault, hx]
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
    have hd : accW0 σ m = w0 := by simp [accW0, getOrDefault, hx]
    rw [hd]
    iframe
  iintro ⟨%p', inst, Hptrs, Hx, Hm⟩
  unfold ownInst
  icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
  have hib' : instBounds (upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (accW0 σ m))) :=
    instBounds_upd _ _ _ Hib hq hw.hn.2
  wp_auto
  wp_if_destruct
  · -- a lower ballot: dropped, no reply
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply (wp_ep_Printf dlog_Printf_ok γ r rr i L p) $$ [$Hrr $Hfro]
    have hlow : m.ballot.slt (accW0 σ m).bal = true :=
      (slt_iff _ _).mpr (by rw [← Hyf.1]; exact Hif)
    rw [hAccept_eq, if_pos hlow]
    ihave Hidle := outsOk_idle (GF := GF) γ i [] (fun o ho => by simp at ho) $$ Houts
    ihave Hins := Hclose $$ %p' %(some (accW0 σ m)) Hptrs [Hy Hycmds Hydeps Hylb]
    · unfold instAt ownInst; iexists y; iframe Hy Hycmds Hydeps Hylb
      isplitr
      · ipureintro; exact Hyf
      · iexact Hyid
    iapply HΦ
    unfold repDone
    iexists accPre σ m
    iframe Hf Hidle
    rw [ownRep_unseal]; unfold ownRepDef
    simp only [accPre]
    unfold repRowArr
    iframe Hins Hcut Heut Hconf Hmsk HmaxSeq Hlead Hstore Hpeer Hmrb
    isplitr
    · ipureintro; exact hib'
    isplitr
    · ipureintro; exact Hcb
    isplitl [Hcrtsl]
    · iexists crt; iframe Hcrtf Hcrtsl
    isplitl [HlS]
    · iexact HlS
    iexact HlP
  have hnl : m.ballot.slt (accW0 σ m).bal = false := by
    rcases h : m.ballot.slt (accW0 σ m).bal
    · rfl
    · exact absurd ((slt_iff _ _).mp h) (by rw [← Hyf.1]; exact Hif)
  -- the instance's update (unless committed), joined before the reply
  wp_join iprop(∃ (w' : InstRec) (evs : List Out),
      ⌜hAccept σ m = ((accPre σ m).setInst ⟨toN m.replica, toN m.inst⟩ w',
        evs ++ [Out.send (toN m.leaderId) (.acceptReply (accReply m w'))]) ∧ NoSends evs⌝ ∗
      inst_ptr ↦ p' ∗ ownInst γ i ⟨toN m.replica, toN m.inst⟩ p' w' ∗ l ↦ epaxos.Accept.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds ∗ row ↦* ptrs.set (toN m.inst) p')
    with [inst Hy Hycmds Hydeps Hylb Hm Hcs Hds Hptrs] as ⟨%w', %evs, %Heq, inst, Hx, Hm, Hptrs⟩
  · -- committed already
    wp_apply (wp_ep_Printf dlog_Printf_ok γ r rr i L p) $$ [$Hrr $Hfro]
    wp_join_done
    have hc : stGe (accW0 σ m).status stCOMMITTED = true :=
      (stGe_iff _ _).mpr (by rw [← Hyf.2.2.1]; exact Hif)
    iexists accW0 σ m, []
    iframe inst Hm Hptrs
    isplitr
    · ipureintro
      refine ⟨?_, fun o ho => by simp at ho⟩
      rw [hAccept_eq, if_neg (by rw [hnl]; decide), if_pos hc]
    unfold ownInst; iexists y; iframe Hy Hycmds Hydeps Hylb
    isplitr
    · ipureintro; exact Hyf
    · iexact Hyid
  · -- accepted
    unfold epaxos.ACCEPTED
    wp_auto
    simp only [h1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
    · ipureintro; rw [e1, hq']; exact Hrow
    simp only [h2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index row _ _ _ p' h2.1 $$ [$Hptrs] as Hptrs
    · ipureintro; rw [e2, hn']
      simp [show toN m.inst < ptrs.length by have := Hptr.2; omega]
    ihave #HDur := isReplicaFw_durable _ _ _ _ _ _ $$ Hfw
    wp_apply wp_recordInstanceMetadata $$ [$Hrr $HDur]
    wp_apply wp_recordCommands $$ [$Hrr $HDur]
    imod ownCmds_persist _ _ _ $$ Hcs with #Hcs
    wp_apply wp_sync $$ [$Hrr $HDur]
    wp_join_done
    have hc : stGe (accW0 σ m).status stCOMMITTED = false := by
      rcases h : stGe (accW0 σ m).status stCOMMITTED
      · rfl
      · exact absurd ((stGe_iff _ _).mp h) (by rw [← Hyf.2.2.1]; exact Hif)
    have hne : (accW0 σ m).status ≠ stEXECUTED := by
      intro h; rw [h] at hc; revert hc; decide
    iexists accInst σ m, [Out.ev (.vote ⟨toN m.replica, toN m.inst⟩ m.ballot stACCEPTED
      ⟨m.command, m.seq, m.deps⟩)]
    iframe inst Hm Hptrs
    isplitr
    · ipureintro
      refine ⟨?_, ?_⟩
      · rw [hAccept_eq, if_neg (by rw [hnl]; decide), if_neg (by rw [hc]; decide)]
      · intro o ho
        simp only [List.mem_cons, List.mem_nil_iff, _root_.or_false] at ho
        subst ho
        exact ⟨fun _ _ h => Out.noConfusion h, fun _ h => Out.noConfusion h⟩
    unfold ownInst
    iexists _
    iframe Hy
    isplitr
    · ipureintro
      exact ⟨rfl, rfl, rfl, rfl, fun _ => Hyf.2.2.2.2 hne⟩
    iframe Hyid
    isplitr
    · simp only [accInst, cmdsRep]
      iframe Hcs
      ipureintro; exact Hcsnn
    isplitl [Hds]
    · iexists DFrac.own 1
      simp only [accInst, ownDeps]
      iexact Hds
    have hd1 : decide ((accW0 σ m).status = stEXECUTED) = false := decide_eq_false hne
    have hd2 : decide ((accInst σ m).status = stEXECUTED) = false := by
      show decide (stACCEPTED = stEXECUTED) = false
      decide
    simp only [hd1, hd2]
    simp only [accInst]
    iexact Hylb
  -- the reply
  unfold ownInst
  icases Hx with ⟨%y2, Hy2, %Hyf2, #Hyid2, Hycmds2, Hydeps2, Hylb2⟩
  wp_auto
  obtain ⟨Heq, Hns⟩ := Heq
  have hlt : toN m.leaderId < nR ∧ toN m.leaderId ≠ i := ⟨hw.hl.2.1, hw.hl.2.2⟩
  have hlid : W32 ((toN m.leaderId : Nat) : Int) = m.leaderId := by
    have := hw.hl.1; simp only [toN, zz] at *; word
  rw [Heq]
  icases outsOk_send γ i evs _ _ Hns hlt.1 $$ Houts with ⟨Ho, Hidle⟩
  ihave Hmsg : ownAcceptReply «$r0_ptr» (accReply m w') (DFrac.own 1) $$ [«$r0»]
  · unfold ownAcceptReply accReply
    rw [← Hyf2.1]
    iexact «$r0»
  wp_apply (wp_replyAccept hS γ i r rr L p Rext ord (toN m.leaderId) m.leaderId hlid «$r0_ptr»
    (accReply m w') (DFrac.own 1) hlt) $$ [Ho Hmsg] as Ho
  · iframe
    unfold hdCtx; iexact Hctx0
  ihave Hidle := Hidle $$ Ho
  -- the state
  ihave Hins := Hclose $$ %p' %(some w') [Hptrs] [Hy2 Hycmds2 Hydeps2 Hylb2]
  · iexact Hptrs
  · unfold instAt ownInst; iexists y2; iframe Hy2 Hycmds2 Hydeps2 Hylb2
    isplitr
    · ipureintro; exact Hyf2
    · iexact Hyid2
  iapply HΦ
  unfold repDone
  iexists (accPre σ m).setInst ⟨toN m.replica, toN m.inst⟩ w'
  iframe Hf Hidle
  rw [ownRep_unseal]; unfold ownRepDef
  simp only [accPre, RState.setInst, upd_upd]
  unfold repRowArr
  iframe Hins Hcut Heut Hconf Hmsk HmaxSeq Hlead Hstore Hpeer Hmrb
  isplitr
  · ipureintro; exact instBounds_upd _ _ _ Hib hq hw.hn.2
  isplitr
  · ipureintro; exact Hcb
  isplitl [Hcrtsl]
  · iexists crt; iframe Hcrtf Hcrtsl
  isplitl [HlS]
  · iexact HlS
  iexact HlP

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
