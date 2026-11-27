/- Relate the immutable term runs to the Raft state's entries above the delivered cursor. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode
public import Proof.go_etcd_io.raft.v3.DurableLogView

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

variable [GooseExts]

/-- In the replay window the last entry in the durable backend prefix is at the
consistent index. Agreement with the Raft state's log identifies the entry term. -/
theorem replayImage_plogTerm (A : List EntryModel) (S : RaftState) (ci : w64)
    (hpos : 0 < A.length) (hci : uint.Z ci = A.length) (hb : uint.nat S.base.index' ≤ A.length)
    (ha : DurAgrees S (A.map EntryModel.toLE)) :
    plogTermAt S.base S.ents ci = some ((A.getLast?.map EntryModel.term).getD (W64 0)) := by
  let k := A.length - 1
  have hk : k < A.length := by dsimp [k]; omega
  have he := List.getElem?_eq_getElem hk
  have hm : (A.map EntryModel.toLE)[k]? = some (A[k].toLE) := by simp [List.getElem?_map, he]
  have hn : k + 1 = A.length := by dsimp [k]; omega
  have hterm := ha k _ (by omega) hm
  have hw : W64 ((k : Int) + 1) = ci := by word
  rw [hw] at hterm
  rw [List.getLast?_eq_getElem?, he]
  exact hterm

variable [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- (2026-11-24, the lifetime law: `notes/etcd-dist-d6.md`, T4 round 5) **A `MsgSnap` of this run is
past the restart's term**: a `MsgSnap` a `Ready` of this run handed out (`rnMessageSource`), at a
restart (`a0 ≠ []`: `rnRestartOk`'s second disjunct, with the node's `nodeStartTerm γ.nl γ.t0`), has
a term past `t0` (raft's `readySnapSources_startTerm`). -/
theorem rnReplayJob_lifetime (γ : RNNames GF) (sm : MsgSt) (ml : Loc) :
    rnRestartOk γ ∗ rnMessageSource γ ⟨ml, sm⟩ ⊢
      ⌜sm.msg.Type' = MsgSnap → γ.a0 ≠ [] → uint.Z γ.t0 < uint.Z sm.msg.Term'⌝ := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨#Hrok, #Hsrc⟩
  iunfold rnRestartOk at Hrok
  icases Hrok with (%h0 | ⟨-, -, #Hst, -⟩)
  · ipureintro; intro _ hne; exact absurd h0.1 hne
  iunfold rnMessageSource at Hsrc
  icases Hsrc with ⟨%term, %ms, %bound, %inst, %hq, #Hss⟩
  ihave %Hall := readySnapSources_startTerm γ.node.cl γ.nl γ.id term ms bound inst γ.t0 $$ [Hss Hst]
  · iframe Hss Hst
  ipureintro
  intro ht _
  exact Hall ⟨ml, sm⟩ hq ht

/-- The apply channel gets the concrete run for the backend index when the
elected log agrees with the committed backend prefix. (2026-11-24, the lifetime law) The agreement is
needed only for a `MsgSnap` of this run (`rnReplayJob`), so only at a term past the restart's
(`rnReplayJob_lifetime`): `uint.Z γ.t0 < uint.Z rt`, which raft's `raftState_cmtBefore_agree` takes. -/
theorem rnReplayJob_of_history (γ : RNNames GF) (view : GoSlice) (runs : List replayTermRun)
    (rt : w64) (n : Nat) (S : RaftState) (hb : uint.nat S.base.index' ≤ n)
    (hr : replayRunsDescribe runs S n) :
    letI := srvStor (GF := GF) γ.node
    (view ↦*□ runs : IProp GF) ⊢ rnRestartOk γ -∗
      (□ ∀ sm : MsgSt, ⌜sm.msg.Type' = MsgSnap ∧ sm.msg.Term' = rt ∧ n < γ.a0.length ∧
          uint.Z γ.t0 < uint.Z rt⌝ -∗
        sentMsg γ.node.cl srvClusterN γ.id sm ={⊤}=∗ ⌜DurAgrees S (γ.a0.map EntryModel.toLE)⌝) -∗
      rnReplayJob γ view rt n := by
  iintro #Hr #Hrok #Hagree
  iunfold rnReplayJob
  iintro !> %sm %ci %h #Hsent %ml #Hsrc
  obtain ⟨ht, hrt, hn, hci⟩ := h
  ihave %hlt := rnReplayJob_lifetime γ sm ml $$ [Hrok Hsrc]
  · iframe Hrok Hsrc
  have ht0 : uint.Z γ.t0 < uint.Z rt := by
    rw [← hrt]; exact hlt ht (fun h => by rw [h] at hn; exact Nat.not_lt_zero _ hn)
  ihave Hag := Hagree $$ %sm %(⟨ht, hrt, hn, ht0⟩) Hsent
  imod Hag with %ha
  have hd := replayImage_plogTerm γ.a0 S ci (by omega) hci (by omega) ha
  obtain ⟨hc, r, hfound, hterm⟩ := hr ci _ (by have := uint_nat_eq ci; omega) hd
  imodintro
  iexists runs, r
  iframe Hr
  ipureintro; exact ⟨hc, hfound, hterm⟩

/-- (2026-11-24, option (a): the campaign map's closure) **L2 at the durable state, as the replay job's
premise**: raft's `raftState_leadAgree` at a durable state `S` of term `rt` (made at the `Ready`'s
*enter*) gives `rnReplayJob_of_history`'s premise: a `MsgSnap` this node sent at `rt` shows it leads
`rt` (`sentMsg_localSnapshotLeader`). -/
theorem rnReplayJob_premise_of_lead (γ : RNNames GF) (S : RaftState) (rt : w64) (n : Nat)
    (hrt : S.term = rt) :
    letI := srvStor (GF := GF) γ.node
    (□ (snapshotLeader γ.node.cl γ.id S.term ={⊤}=∗
        ⌜durLogAgrees S (γ.a0.map EntryModel.toLE)⌝) : IProp GF) ⊢
      □ ∀ sm : MsgSt, ⌜sm.msg.Type' = MsgSnap ∧ sm.msg.Term' = rt ∧ n < γ.a0.length ∧
          uint.Z γ.t0 < uint.Z rt⌝ -∗
        sentMsg γ.node.cl srvClusterN γ.id sm ={⊤}=∗ ⌜DurAgrees S (γ.a0.map EntryModel.toLE)⌝ := by
  letI := srvStor (GF := GF) γ.node
  iintro #Hlaw !> %sm %h #Hsent
  obtain ⟨ht, htm, -, -⟩ := h
  ihave #Hsl := sentMsg_localSnapshotLeader γ.node.cl srvClusterN γ.id sm ht $$ Hsent
  rw [htm, ← hrt]
  ihave Hl := Hlaw $$ Hsl
  imod Hl with %ha
  imodintro; ipureintro; exact ha

/-- (2026-11-24, the lifetime law) **The server's membership is fixed** (raft's L2 premise `confFixed`):
after every committed log the configuration is the boot one (`srv_confAt_simple`). -/
theorem srv_confFixed [go_etcd_io.raft.v3.Assumptions] (γ : ServerRaftNames) (E : CoPset)
    (hC : ↑srvConfN ⊆ E) (hL : ↑srvLogN ⊆ E) :
    srvRaftLogInv (GF := GF) γ ⊢
      (letI := srvStor (GF := GF) γ.raft; confFixed γ.raft.cl E (Membership.simple γ.raft.cfg)) := by
  letI := srvStor (GF := GF) γ.raft
  iintro #Hinv
  unfold confFixed
  iintro !> %l #Hl
  iapply srv_confAt_simple γ l l.length (Nat.le_refl _) E hC hL
  iframe Hinv Hl

/-- (T10 step 3 (B), B1; option (a) item 2) **L2's law at a durable state, for the replay job**: when the
restart's backend log `a0` is non-empty and `S`'s term is past the restart's `t0`, a leadership of
`S.term` shows `S`'s log agrees with `a0` (`raftState_leadAgree`'s wand). Made at each *enter*
(`rnLeadLaw_enter`); `rnReplayJob_premise_of_lead` turns it into the replay job's premise. -/
def rnLeadLaw (γ : RNNames GF) (S : RaftState) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(□ (⌜γ.a0 ≠ [] ∧ uint.Z γ.t0 < uint.Z S.term⌝ -∗
    □ (snapshotLeader γ.node.cl γ.id S.term ={⊤}=∗ ⌜durLogAgrees S (γ.a0.map EntryModel.toLE)⌝)))

instance rnLeadLaw_persistent (γ : RNNames GF) (S : RaftState) :
    Persistent (rnLeadLaw (GF := GF) γ S) := by
  unfold rnLeadLaw; infer_instance

/-- (T10 step 3 (B), B1) **The law at an *enter***: with the restart data (`rnRestart_cmtBefore`), the
cluster, the server's log invariant (`srv_confFixed`) and the node's durable state `S`, raft's
`raftState_leadAgree` gives `rnLeadLaw γ S` (trivially when `a0 = []` or `S.term ≤ t0`). -/
theorem rnLeadLaw_enter [go_etcd_io.raft.v3.Assumptions] (γ : RNNames GF) (γr : ServerRaftNames)
    (S : RaftState) (hγ : γr.raft = γ.node) :
    letI := srvStor (GF := GF) γ.node
    rnRestartOk γ ∗ isCluster γ.node.cl srvClusterN ∗ srvRaftLogInv γr ∗ raftState γ.node.cl γ.id S ⊢
      |={⊤}=> raftState γ.node.cl γ.id S ∗ rnLeadLaw γ S := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨#Hrok, #Hcl, #Hinv, Hst⟩
  by_cases hc : γ.a0 ≠ [] ∧ uint.Z γ.t0 < uint.Z S.term
  · have hfix := srv_confFixed (GF := GF) γr ⊤ (by simp) (by simp)
    rw [hγ] at hfix
    ihave #Hfix := hfix $$ Hinv
    ihave #Hcb := rnRestart_cmtBefore γ $$ Hrok %hc.1
    imod raftState_leadAgree γ.node.cl srvClusterN ⊤ (by simp) _ γ.id γ.t0 S _ hc.2 $$
      [Hcl Hfix Hcb Hst] with ⟨Hst, #Hlaw⟩
    · iframe Hcl Hfix Hcb Hst
    imodintro
    iframe Hst
    iunfold rnLeadLaw
    iintro !> %_
    iexact Hlaw
  · imodintro
    iframe Hst
    iunfold rnLeadLaw
    iintro !> %h
    exact absurd h hc

/-- (T10s3b B3) `rnLeadLaw_enter` at a mask `E` holding the cluster's, the log's and the
configuration's invariants (the law's wand stays at `⊤`): for the loop's *enter*, where the node's
durable state is inside the WAL's crash-aware invariant (`rnDurK_leadLaw`). -/
theorem rnLeadLaw_enterE [go_etcd_io.raft.v3.Assumptions] (γ : RNNames GF) (γr : ServerRaftNames)
    (S : RaftState) (hγ : γr.raft = γ.node) (E : CoPset) (hN : ↑srvClusterN ⊆ E)
    (hC : ↑srvConfN ⊆ E) (hL : ↑srvLogN ⊆ E) :
    letI := srvStor (GF := GF) γ.node
    rnRestartOk γ ∗ isCluster γ.node.cl srvClusterN ∗ srvRaftLogInv γr ∗ raftState γ.node.cl γ.id S ⊢
      |={E}=> raftState γ.node.cl γ.id S ∗ rnLeadLaw γ S := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨#Hrok, #Hcl, #Hinv, Hst⟩
  by_cases hc : γ.a0 ≠ [] ∧ uint.Z γ.t0 < uint.Z S.term
  · have hfix := srv_confFixed (GF := GF) γr E hC hL
    rw [hγ] at hfix
    ihave #Hfix := hfix $$ Hinv
    ihave #Hcb := rnRestart_cmtBefore γ $$ Hrok %hc.1
    imod raftState_leadAgree γ.node.cl srvClusterN E hN _ γ.id γ.t0 S _ hc.2 $$
      [Hcl Hfix Hcb Hst] with ⟨Hst, #Hlaw⟩
    · iframe Hcl Hfix Hcb Hst
    imodintro
    iframe Hst
    iunfold rnLeadLaw
    iintro !> %_ !> #Hsl
    ihave Hl := Hlaw $$ Hsl
    iapply (fupd_mask_mono (E1 := E) (E2 := ⊤) (by simp)) $$ Hl
  · imodintro
    iframe Hst
    iunfold rnLeadLaw
    iintro !> %h
    exact absurd h hc

/-- (T10s3b B3) **The replay job from the history and the law** (`rnReplayJob_of_history` and
`rnReplayJob_premise_of_lead`): the runs describe the durable state `S` the batch entered, whose term
is the batch's raft term `rt` (or `rt = 0`, when the job's premise is void). -/
theorem rnReplayJob_of_lead (γ : RNNames GF) (view : GoSlice) (S : RaftState) (rt : w64) (n : Nat)
    (hb : uint.nat S.base.index' ≤ n) (hrt : S.term = rt ∨ uint.Z rt = 0) :
    rnReplayHist γ view S n ⊢ rnRestartOk γ -∗ rnLeadLaw γ S -∗ rnReplayJob γ view rt n := by
  letI := srvStor (GF := GF) γ.node
  iintro #Hh #Hrok #Hlaw
  icases rnReplayHist.describe γ view S n $$ Hh with ⟨%runs, #Hr, %hd⟩
  iapply rnReplayJob_of_history γ view runs rt n S hb hd $$ Hr Hrok
  rcases hrt with hrt | h0
  · iunfold rnLeadLaw at Hlaw
    iintro !> %sm %h #Hsent
    obtain ⟨h1, h2, hn, ht0⟩ := h
    have hne : γ.a0 ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hc : γ.a0 ≠ [] ∧ uint.Z γ.t0 < uint.Z S.term := ⟨hne, by rw [hrt]; exact ht0⟩
    ihave #Hl := Hlaw $$ %hc
    ihave #Hp := rnReplayJob_premise_of_lead γ S rt n hrt $$ Hl
    iapply Hp $$ %sm %(⟨h1, h2, hn, ht0⟩) Hsent
  · iintro !> %sm %h
    exfalso
    have := h.2.2.2
    have := (uint.Z γ.t0).le_refl
    have h0' : (0 : Int) ≤ uint.Z γ.t0 := by word
    omega

/-- (T10s3b B3) **The law at the loop's *enter***: the node's durable state is the one in the WAL's
crash-aware invariant, at the loop's view `vk` (its `durOf`); `rnLeadLaw_enterE` inside it. (Session 6)
Also that state's log well formed (`raftState_logViewE`), for the replay view's batch premises. -/
theorem rnDurK_leadLaw [go_etcd_io.raft.v3.Assumptions] (γ : RNNames GF) (γr : ServerRaftNames)
    (hγ : γr.raft = γ.node) (νk : WalNamesK GF) (h : WalH GF) (vk : WalViewK) :
    letI := srvStor (GF := GF) γ.node
    rnDurInvK γ.node γ.id νk h ∗ notCrashed ∗ £ 1 ∗ rnWalViewK νk vk ∗
      rnRestartOk γ ∗ isCluster γ.node.cl srvClusterN ∗ srvRaftLogInv γr ⊢
      |={⊤}=> notCrashed ∗ rnWalViewK νk vk ∗ rnLeadLaw γ (durOf vk) ∗
        ⌜PlogWf (durOf vk).base (durOf vk).ents⌝ := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨#Hinv, Hnc, Hlc, Hvw, #Hrok, #Hcl, #Hlog⟩
  iunfold rnWalViewK at Hvw
  icases Hvw with ⟨Hv, Hok⟩
  iunfold rnDurInvK at Hinv
  icases Hinv with ⟨-, #Hinv⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  icases Hi with (Hb | ⟨Hs', Ha', Hok', Htn'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Hok Hok'
  iunfold rnDurBodyK at Hb
  icases Hb with ⟨%vk0, %σ, %Hs, %n, Hv0, Hcm, Htn, Hr, #Hsc, #Hsy, #Hhc, #Hlb, %Hp, Hraft⟩
  icombine Hv Hv0 gives %Hag
  have Hvv : vk = vk0 := Hag.2
  subst Hvv
  icases Hraft with (⟨HrS, Hpend⟩ | ⟨Hcr, Htk⟩)
  rotate_left
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hcr
  have hN : (↑srvClusterN : CoPset) ⊆ ⊤ \ ↑rnDurKN :=
    fun x hx => mask_ndot_ne' nroot "raft_commit" "rnDurK" (by decide) x (srvClusterN_sub x hx)
  have hC : (↑srvConfN : CoPset) ⊆ ⊤ \ ↑rnDurKN :=
    fun x hx => mask_ndot_ne' nroot "server_conf" "rnDurK" (by decide) x hx
  have hL : (↑srvLogN : CoPset) ⊆ ⊤ \ ↑rnDurKN :=
    fun x hx => mask_ndot_ne' nroot "raft_commit" "rnDurK" (by decide) x (srvLogN_sub x hx)
  imod rnLeadLaw_enterE γ γr (durOf vk) hγ _ hN hC hL $$ [HrS] with ⟨HrS, #Hlaw⟩
  · iframe Hrok Hcl Hlog
    rw [← hγ] at *
    iexact HrS
  -- (session 6) the entered log well formed (raft's), for the replay view's batch premises
  imod raftState_logViewE γ.node.cl γ.id (durOf vk) srvClusterN _ hN $$ [$Hcl $HrS]
    with ⟨HrS, %fp, %Hfp, -, -⟩
  imod Hclose $$ [Hv0 Hcm Htn Hr HrS Hpend] with -
  · inext
    ileft
    iunfold rnDurBodyK
    iexists vk, σ, Hs, n
    iframe Hv0 Hcm Htn Hr Hsc Hsy Hhc Hlb
    isplitr
    · ipureintro; exact Hp
    ileft
    iframe HrS Hpend
  imodintro
  iframe Hnc Hlaw
  isplitl [Hv Hok]
  · iunfold rnWalViewK
    iframe Hv Hok
  ipureintro; exact Hfp.2.1

end EtcdGrove
end Perennial
