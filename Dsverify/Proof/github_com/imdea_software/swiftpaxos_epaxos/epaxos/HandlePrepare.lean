/-
`(*Replica).handlePrepare` against the model's `hPrepare`: the instance (created if nil), the
ballot joined, the reply (`replyPrepare` → `SendMsg`, the outbox `[reply]` emptied). Also the
replies' shared lemmas (`outsOk_send`, `wp_replyPrepare`, `wp_replyAccept`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Bcast
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.NewInstance
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Log

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

theorem sendsTo_send (evs : List Out) (h : NoSends evs) (t : Nat) (m : Msg) (to : Nat) :
    sendsTo (evs ++ [.send t m]) to = if to = t then [m] else [] := by
  have := sendsTo_noSends _ h to
  unfold sendsTo at this ⊢
  rw [List.filterMap_append, this]
  by_cases e : to = t
  · subst e; simp
  · simp [e, Ne.symm e]

theorem pendOf_send (evs : List Out) (h : NoSends evs) (t : Nat) (m : Msg) :
    pendOf (evs ++ [.send t m]) = none := by
  have := pendOf_noSends _ h
  unfold pendOf at this ⊢
  rw [List.foldl_append, this]
  rfl

/-! ## `hPrepare`, named -/

/-- The instance `handlePrepare` finds (created if nil). -/
def prepW0 (σ : RState) (m : Prepare) : InstRec :=
  (getOrDefault σ ⟨toN m.replica, toN m.inst⟩).2

/-- The instance after joining the ballot. -/
def prepW1 (σ : RState) (m : Prepare) : InstRec :=
  if (prepW0 σ m).bal.slt m.ballot then { prepW0 σ m with bal := m.ballot } else prepW0 σ m

/-- The reply. -/
def prepReply (σ : RState) (m : Prepare) : PrepareReply :=
  { acceptorId := W32 σ.id, replica := m.replica, inst := m.inst, ballot := (prepW1 σ m).bal,
    vballot := (prepW1 σ m).vbal, status := (prepW1 σ m).status,
    command := (prepW1 σ m).cmds.getD [], seq := (prepW1 σ m).seq, deps := (prepW1 σ m).deps }

theorem prepW1_bal (σ : RState) (m : Prepare) : (prepW1 σ m).bal =
    if (prepW0 σ m).bal.slt m.ballot then m.ballot else (prepW0 σ m).bal := by
  unfold prepW1; split <;> rfl

@[simp] theorem prepW1_vbal (σ : RState) (m : Prepare) : (prepW1 σ m).vbal = (prepW0 σ m).vbal := by
  unfold prepW1; split <;> rfl
@[simp] theorem prepW1_status (σ : RState) (m : Prepare) :
    (prepW1 σ m).status = (prepW0 σ m).status := by unfold prepW1; split <;> rfl
@[simp] theorem prepW1_cmds (σ : RState) (m : Prepare) : (prepW1 σ m).cmds = (prepW0 σ m).cmds := by
  unfold prepW1; split <;> rfl
@[simp] theorem prepW1_seq (σ : RState) (m : Prepare) : (prepW1 σ m).seq = (prepW0 σ m).seq := by
  unfold prepW1; split <;> rfl
@[simp] theorem prepW1_deps (σ : RState) (m : Prepare) : (prepW1 σ m).deps = (prepW0 σ m).deps := by
  unfold prepW1; split <;> rfl
@[simp] theorem prepW1_lb (σ : RState) (m : Prepare) : (prepW1 σ m).lb = (prepW0 σ m).lb := by
  unfold prepW1; split <;> rfl

theorem prepW1_eq (σ : RState) (m : Prepare) :
    prepW1 σ m = { prepW0 σ m with bal := (prepW1 σ m).bal } := by
  unfold prepW1; split <;> rfl

theorem setInst_setInst (σ : RState) (x : InstId) (a b : InstRec) :
    (σ.setInst x a).setInst x b = σ.setInst x b := by
  simp only [RState.setInst]
  congr 1
  funext y
  simp only [upd]
  split <;> rfl

theorem hPrepare_eq (σ : RState) (m : Prepare) :
    hPrepare σ m = ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩ (prepW1 σ m),
      [Out.send (toN m.leaderId) (.prepareReply (prepReply σ m))]) := by
  unfold hPrepare prepReply prepW1 prepW0 getOrDefault
  simp only [bumpRecvBallot_inst]
  rcases h : σ.inst ⟨toN m.replica, toN m.inst⟩ with _ | w
  · simp only [setInst_setInst]
    simp [RState.setInst]
  · simp [RState.setInst]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- A handler's outputs whose only send is its last one, a reply `m` to `t`: the outbox of `t`
is `[m]`; once emptied, the replica is idle. -/
theorem outsOk_send (γ : EpNames) (i : Nat) (evs : List Out) (t : Nat) (m : Msg)
    (h : NoSends evs) (ht : t < nR) :
    outsOk (GF := GF) γ i (evs ++ [.send t m]) ⊢ outboxFrag γ i t [m] ∗ (outboxFrag γ i t [] -∗ repIdle γ i) := by
  unfold outsOk repIdle
  iintro ⟨Hob, Hp, Hc, -⟩
  rw [pendOf_send _ h]
  have e : ([∗list] to ∈ List.range nR, outboxFrag (GF := GF) γ i to (sendsTo (evs ++ [.send t m]) to)) =
      [∗list] k ↦ to ∈ List.range nR, outboxFrag γ i to (if k = t then [m] else []) := by
    refine Iris.Algebra.BigOpL.bigOpL_eq fun {k to} hk => ?_
    have : to = k := by
      have hk' := (List.getElem?_eq_some_iff.mp hk)
      obtain ⟨hl, he⟩ := hk'
      rw [← he, List.getElem_range]
    subst this
    rw [sendsTo_send _ h]
  rw [e]
  have hget : (List.range nR)[t]? = some t := by simp [ht]
  icases bigSepL_set_acc' hget $$ Hob with ⟨Ho, Hclose⟩
  simp only [↓reduceIte]
  iframe Ho
  iintro Ho
  ihave Hall := Hclose $$ %(fun _ to => outboxFrag γ i to []) %t [] Ho
  · ipureintro
    intro k hk
    funext to
    simp [hk]
  have hset : (List.range nR).set t t = List.range nR := by
    have := List.getElem?_eq_some_iff.mp hget
    conv => rhs; rw [← List.set_getElem_self this.1]
    rw [this.2]
  rw [hset]
  iframe

/-- `replyPrepare(t, reply)`: `SendMsg(t, prepareReplyRPC, reply)` (the outbox `[reply]`
emptied). -/
theorem wp_replyPrepare (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (i : Nat) (r rr : Loc)
    (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (ord : List w32) (t : Nat)
    (q : w32) (hqt : W32 (t : Int) = q)
    (lr : Loc) (m : PrepareReply) (dq : DFrac) (h : t < nR ∧ t ≠ i)
    (hwf : (Msg.prepareReply m).wf) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ outboxFrag γ i t [Msg.prepareReply m] ∗
        ownPrepareReply lr m dq }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"replyPrepare"))
        (Val #q)) (Val #lr))
    {{ RET #(); outboxFrag γ i t [] }} := by
  subst hqt
  wp_start as ⟨#Hctx, Ho, Hm⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  ihave ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, %HLn⟩ := fwRO_fields _ _ _ _ _ $$ Hfro
  unfold epROFields
  icases Hro with ⟨-, #Hprr, -⟩
  wp_auto
  ihave Hmsg : msgObj (interface.mkOk (go.GoType.PointerType epaxos.PrepareReply.ty) #lr)
      (Msg.prepareReply m) dq $$ [Hm]
  · unfold msgObj
    iexists MsgKind.prepareReply, lr
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    unfold ownMsg; iexact Hm
  wp_apply (wp_bcast_send hS γ r rr i L p Rext ord t
    (interface.mkOk (go.GoType.PointerType epaxos.PrepareReply.ty) #lr)
    (Msg.prepareReply m) dq (W8 10) rfl ⟨by rw [HLn.1]; exact h.1, h.2, rfl, hwf⟩) $$ [Ho Hmsg]
  · isplitl []
    · unfold hdCtx epROFields prefOrder; iexact Hctx0
    iframe
  iintro ⟨-, Ho⟩
  wp_auto
  iapply HΦ
  iexact Ho

/-- `replyAccept(t, reply)`: `SendMsg(t, acceptReplyRPC, reply)`. -/
theorem wp_replyAccept (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (i : Nat) (r rr : Loc)
    (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (ord : List w32) (t : Nat)
    (q : w32) (hqt : W32 (t : Int) = q)
    (lr : Loc) (m : AcceptReply) (dq : DFrac) (h : t < nR ∧ t ≠ i) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ outboxFrag γ i t [Msg.acceptReply m] ∗
        ownAcceptReply lr m dq }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"replyAccept"))
        (Val #q)) (Val #lr))
    {{ RET #(); outboxFrag γ i t [] }} := by
  subst hqt
  wp_start as ⟨#Hctx, Ho, Hm⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  ihave ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, %HLn⟩ := fwRO_fields _ _ _ _ _ $$ Hfro
  unfold epROFields
  icases Hro with ⟨-, -, -, -, -, #Harr, -⟩
  wp_auto
  ihave Hmsg : msgObj (interface.mkOk (go.GoType.PointerType epaxos.AcceptReply.ty) #lr)
      (Msg.acceptReply m) dq $$ [Hm]
  · unfold msgObj
    iexists MsgKind.acceptReply, lr
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    unfold ownMsg; iexact Hm
  wp_apply (wp_bcast_send hS γ r rr i L p Rext ord t
    (interface.mkOk (go.GoType.PointerType epaxos.AcceptReply.ty) #lr)
    (Msg.acceptReply m) dq (W8 14) rfl ⟨by rw [HLn.1]; exact h.1, h.2, rfl, trivial⟩) $$ [Ho Hmsg]
  · isplitl []
    · unfold hdCtx epROFields prefOrder; iexact Hctx0
    iframe
  iintro ⟨-, Ho⟩
  wp_auto
  iapply HΦ
  iexact Ho

/-- What `handlePrepare` needs of the state and the message (message ids in range,
`Inv.msgWf`; the sender a peer). -/
structure PrepWf (i : Nat) (σ : RState) (ord : List w32) (m : Prepare) : Prop where
  hrep : RepWf i σ ord
  hq : 0 ≤ zz m.replica ∧ zz m.replica < nR
  hn : 0 ≤ zz m.inst ∧ toN m.inst + 1 < MAX_INSTANCE
  hl : 0 ≤ zz m.leaderId ∧ toN m.leaderId < nR ∧ toN m.leaderId ≠ i
  houts : OutsWf (hPrepare σ m).2

set_option maxHeartbeats 4000000 in
/-- **`handlePrepare(prepare)`**: from the instance lock's contents, the message, and the ghost
step's outputs (the fragment at the model's result, the reply in its outbox), the handler ends
in the lock's invariant shape. -/
theorem wp_handlePrepare (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (i : Nat) (r rr : Loc)
    (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (ord : List w32) (σ : RState)
    (l : Loc) (m : Prepare) (hw : PrepWf i σ ord m) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ ownPrepare l m (DFrac.own 1) ∗
        repFrag γ i (hPrepare σ m).1 ∗ outsOk γ i (hPrepare σ m).2 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"handlePrepare")) (Val #l))
    {{ RET #(); repDone γ i r }} := by
  wp_start as ⟨#Hctx, Hrep, Hm, Hf, Houts⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  rw [ownRep_unseal]; unfold ownRepDef
  icases Hrep with ⟨%Hib, %Hcb, Hinsts, Hcrt, Hcut, Heut, Hconf, Hmsk, HlS, HlP, HmaxSeq, Hlead, Hmrb,
    Hstore, Hpeer⟩
  unfold ownPrepare
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
  ipersist prepare
  -- maxRecvBallot
  wp_join iprop(efld r go!"maxRecvBallot" ↦ (bumpRecvBallot σ m.ballot).maxRecvBallot ∗ l ↦ epaxos.Prepare.mk m.leaderId m.replica m.inst m.ballot)
    with [Hmrb Hm] as ⟨Hmrb, Hm⟩
  · rw [bumpRecvBallot_true _ _ (by simpa using Hif)]
    iframe
  · rw [bumpRecvBallot_false _ _ (by simpa using Hif)]
    iframe
  -- the instance, created if nil
  have hxq : W32 (toN m.replica : Int) = m.replica := by
    have := hw.hq.1; simp only [toN, zz] at *; word
  have hxi : W32 (toN m.inst : Int) = m.inst := by
    have := hw.hn.1; simp only [toN, zz] at *; word
  wp_join iprop(∃ p', inst_ptr ↦ p' ∗ row ↦* ptrs.set (toN m.inst) p' ∗
      ownInst γ i ⟨toN m.replica, toN m.inst⟩ p' (prepW0 σ m) ∗ l ↦ epaxos.Prepare.mk m.leaderId m.replica m.inst m.ballot)
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
    simp only [h1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
    · ipureintro; rw [e1, hq']; exact Hrow
    simp only [h2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index row _ _ _ p' h2.1 $$ [$Hptrs] as Hptrs
    · ipureintro; rw [e2, hn']
      simp [List.getElem?_set, show toN m.inst < ptrs.length by have := Hptr.2; omega]
    rw [e2, hn']
    wp_join_done
    iexists p'
    iframe inst Hptrs Hm
    have hd : prepW0 σ m = newInstanceDefault ⟨toN m.replica, toN m.inst⟩ := by
      simp [prepW0, getOrDefault, hx]
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
    have hd : prepW0 σ m = w0 := by simp [prepW0, getOrDefault, hx]
    rw [hd]
    iframe
  iintro ⟨%p', inst, Hptrs, Hx, Hm⟩
  unfold ownInst
  icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
  -- the ballot joined
  wp_auto
  wp_join iprop(p' ↦ { y with bal' := (prepW1 σ m).bal } ∗ l ↦ epaxos.Prepare.mk m.leaderId m.replica m.inst m.ballot ∗ inst_ptr ↦ p')
    with [Hy Hm inst] as ⟨Hy, Hm, inst⟩
  · -- a higher ballot already
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply (wp_ep_Printf dlog_Printf_ok γ r rr i L p) $$ [$Hrr $Hfro]
    wp_join_done
    have hb : (prepW1 σ m).bal = y.bal' := by
      rw [prepW1_bal, Hyf.1, if_neg]
      intro h; have := (slt_iff _ _).mp h; rw [← Hyf.1] at this
      have : sint.Z m.ballot < sint.Z y.bal' := Hif
      simp only [sint.Z] at *; omega
    rw [hb]
    iframe
  · wp_if_destruct
    · -- joining
      try wp_auto
      wp_apply wp_slice_literal (V := GoInterface) _
      isplitr
      · ipureintro; rfl
      iintro %_ ⟨-, -⟩
      wp_auto
      wp_apply (wp_ep_Printf dlog_Printf_ok γ r rr i L p) $$ [$Hrr $Hfro]
      try wp_auto
      wp_join_done
      have hb : (prepW1 σ m).bal = m.ballot := by
        rw [prepW1_bal, if_pos ((slt_iff _ _).mpr (by rw [← Hyf.1]; exact Hif))]
      rw [hb]
      iframe
    · wp_join_done
      have hb : (prepW1 σ m).bal = y.bal' := by
        rw [prepW1_bal, Hyf.1, if_neg]
        intro h; have := (slt_iff _ _).mp h; rw [← Hyf.1] at this
        have : ¬ sint.Z y.bal' < sint.Z m.ballot := Hif
        simp only [sint.Z] at *; omega
      rw [hb]
      iframe
  -- the reply
  ihave ⟨-, -, #HId, -, -, -, -, -, -, -, -, -, -, %HLn⟩ := fwRO_fields _ _ _ _ _ $$ Hfro
  wp_auto
  icases Hydeps with ⟨%dq, Hydeps⟩
  imod ownSlice_persist $$ Hydeps with #Hydeps
  icases cmdsRep_dup _ _ $$ Hycmds with ⟨Hycmds, #Hcmd⟩
  ipersist «$r0»
  ihave Hmsg : ownPrepareReply «$r0_ptr» (prepReply σ m) DFrac.discard $$ []
  · unfold ownPrepareReply ownDeps prepReply
    iexists y.Cmds', y.Deps'
    simp only [prepW1_vbal, prepW1_status, prepW1_cmds, prepW1_seq, prepW1_deps, hw.hrep.id]
    rw [← Hyf.2.1, ← Hyf.2.2.1, ← Hyf.2.2.2.1]
    iframe Hcmd Hydeps
    iexact «$r0»
  have hlt : toN m.leaderId < nR ∧ toN m.leaderId ≠ i := ⟨hw.hl.2.1, hw.hl.2.2⟩
  have hlid : W32 ((toN m.leaderId : Nat) : Int) = m.leaderId := by
    have := hw.hl.1; simp only [toN, zz] at *; word
  have hwfr : (Msg.prepareReply (prepReply σ m)).wf := by
    have := hw.houts; rw [hPrepare_eq] at this
    exact this _ (List.mem_singleton_self _)
  have houts : (hPrepare σ m).2 = [] ++ [Out.send (toN m.leaderId) (.prepareReply (prepReply σ m))] := by
    rw [hPrepare_eq]; rfl
  rw [houts]
  icases outsOk_send γ i [] _ _ (fun o ho => by simp at ho) hlt.1 $$ Houts with ⟨Ho, Hidle⟩
  wp_apply (wp_replyPrepare hS γ i r rr L p Rext ord (toN m.leaderId) m.leaderId hlid «$r0_ptr»
    (prepReply σ m) DFrac.discard hlt hwfr) $$ [Ho Hmsg] as Ho
  · iframe
    unfold hdCtx; iexact Hctx0
  ihave Hidle := Hidle $$ Ho
  -- the state
  have hib' : instBounds (upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (prepW1 σ m))) :=
    instBounds_upd _ _ _ Hib hq hw.hn.2
  ihave Hins := Hclose $$ %p' %(some (prepW1 σ m)) [Hptrs] [Hy Hycmds Hylb]
  · iexact Hptrs
  · unfold instAt ownInst
    iexists { y with bal' := (prepW1 σ m).bal }
    simp only [prepW1_vbal, prepW1_status, prepW1_cmds, prepW1_seq, prepW1_deps, prepW1_lb]
    iframe Hy Hyid Hycmds Hylb
    isplitr
    · ipureintro; exact ⟨trivial, Hyf.2.1, Hyf.2.2.1, Hyf.2.2.2.1, Hyf.2.2.2.2⟩
    iexists DFrac.discard; iexact Hydeps
  iapply HΦ
  unfold repDone
  iexists (bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩ (prepW1 σ m)
  rw [hPrepare_eq]
  iframe Hf Hidle
  iapply ownRep_of
  rw [ownRepRest_setInst]
  unfold ownRepRest
  simp only [RState.setInst, bumpRecvBallot_inst, bumpRecvBallot_crt, bumpRecvBallot_cut,
    bumpRecvBallot_eut, bumpRecvBallot_conf, bumpRecvBallot_msk, bumpRecvBallot_maxSeq,
    bumpRecvBallot_leader, bumpRecvBallot_store, bumpRecvBallot_po, bumpRecvBallot_lastScan,
    bumpRecvBallot_lastPut]
  iframe
  ipureintro; exact ⟨hib', Hcb⟩

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
