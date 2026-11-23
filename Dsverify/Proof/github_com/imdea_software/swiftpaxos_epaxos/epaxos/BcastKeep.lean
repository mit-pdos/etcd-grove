/-
`bcastCommit` with the broadcasting instance's slot pointer kept known across the call (its
caller reads `inst.proposeTime` afterwards through its local `inst` pointer).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.BcastOthers
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Slot

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

/-- Slot `x` known to hold `ptr` with image `w`. -/
def ptrQ (γ : EpNames) (i : Nat) (x : InstId) (ptr : Loc) (w : InstRec) :
    Loc → IProp GF :=
  fun pt => iprop(⌜pt = ptr⌝ ∗ instAt γ i x pt (some w))

set_option maxHeartbeats 4000000 in
/-- `wp_bcastCommit` with slot `x`'s pointer kept (`repInstsP` with `ptrQ` at `x`). -/
theorem wp_bcastCommitKeep (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (i : Nat)
    (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (ord : List w32)
    (σ : RState) (replica n : w32) (w : InstRec) (lb : LbRec) (ptr : Loc) (hwf : RepWf i σ ord)
    (hq : 0 ≤ zz replica ∧ zz replica < nR) (hn : 0 ≤ zz n ∧ toN n + 1 < MAX_INSTANCE)
    (hw : σ.inst ⟨toN replica, toN n⟩ = some w) (hlb : w.lb = some lb)
    (hdo : lbDepsOwned lb = false) (hm : (Msg.commit (commitOf σ replica n lb)).wf)
    (hord : ∀ o ∈ ord, 0 ≤ sint.Z o) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ⌜instBounds σ.inst⌝ ∗ ⌜cutBounds σ.committedUpTo⌝ ∗
        repInstsP r (updP (instAtP γ i σ.inst) ⟨toN replica, toN n⟩
          (ptrQ γ i ⟨toN replica, toN n⟩ ptr w)) ∗ ownRepRest i r σ ∗ repFrag γ i σ ∗
        pendFrag γ i (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)).norm ∗
        outboxesNil γ i }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"bcastCommit"))
        (Val #replica)) (Val #n))
    {{ RET #(); repInstsP r (updP (instAtP γ i σ.inst) ⟨toN replica, toN n⟩
          (ptrQ γ i ⟨toN replica, toN n⟩ ptr w)) ∗ ownRepRest i r σ ∗ repFrag γ i σ ∗
        pendFrag γ i none ∗ outboxesNil γ i }} := by
  wp_start as ⟨#Hctx, %Hib, %Hcb, Hinsts, Hrest, Hf, Hp, Hob⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  have hq' : toN replica < nR := by
    have := hq.1; have := hq.2; simp only [toN, zz] at *; omega
  have hn' : toN n < MAX_INSTANCE := by have := hn.2; omega
  icases repInstsP_acc r _ ⟨toN replica, toN n⟩ hq' hn' $$ Hinsts with
    ⟨%iss, %rows, %row, %ptrs, %pt0, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  ihave Hx := updP_apply_self _ _ _ _ $$ Hx
  unfold ptrQ
  icases Hx with ⟨%Hpe0, Hx⟩
  subst pt0
  ihave Hx := (instAt_some γ i _ ptr _ rfl).1 $$ Hx
  unfold ownInst
  icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
  rw [hlb]
  icases Hylb with ⟨%Hlbnn, Hlb⟩
  unfold ownLb
  icases Hlb with ⟨%yl, %gs, %prs, Hyl, %Hylf, Hcp, Hlcmds, Hldeps, Hlprs, %Hlprsl, Hlpr⟩
  wp_apply wp_with_defer_recover as %defer %pnc Hdefer Hpnc
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
  ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
  have e1 : sint.Z (W64 (sint.Z replica)) = sint.Z replica := by word
  have e2 : sint.Z (W64 (sint.Z n)) = sint.Z n := by word
  have hqe : (sint.Z replica).toNat = toN replica := rfl
  have hne : (sint.Z n).toNat = toN n := rfl
  have h1 : 0 ≤ sint.Z (W64 (sint.Z replica)) ∧ sint.Z (W64 (sint.Z replica)) < sint.Z iss.len := by
    have := hq.1; have hl := (List.getElem?_eq_some_iff.mp Hrow).1
    unfold toN zz at *; constructor <;> word
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
  · ipureintro; rw [e1, hqe]; exact Hrow
  have h2 : 0 ≤ sint.Z (W64 (sint.Z n)) ∧ sint.Z (W64 (sint.Z n)) < sint.Z row.len := by
    have := hn.1; have := hn.2; have := Hptr.2
    unfold toN zz at *; constructor <;> word
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
  · ipureintro; rw [e2, hne]; exact Hptr.1
  ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  ihave ⟨#HN, #HF, #HId, #HSt, #HRPC, #HPC, #HThr, #HEx, #HDr, #HSh, #HStats, #HStm, #HAl, %HLn⟩ :=
    fwRO_fields _ _ _ _ _ $$ Hfro
  unfold epROFields
  icases Hro with ⟨-, -, -, -, -, -, #Hcom, -⟩
  unfold prefOrder
  icases Hpo with ⟨%po, #Hpof, #Hpos, %Hpop⟩
  wp_auto
  ipersist «$r0»
  ihave #Hec : «$r0_ptr» ↦□ epaxos.Commit.mk (W32 i) replica n yl.ballot' yl.cmds'
      yl.seq' yl.deps' $$ [«$r0»]
  · iexact «$r0»
  iclear «$r0»
  -- the message object
  rw [hdo]
  simp only [Bool.false_eq_true, if_false]
  icases Hldeps with ⟨%dq0, Hldeps⟩
  ipersist Hldeps
  icases cmdsRep_dup _ _ $$ Hlcmds with ⟨Hlcmds, #Hcmd⟩
  -- the state, closed again (the loop reads only persistent data)
  have hset : ptrs.set (toN n) ptr = ptrs := by
    have := List.getElem?_eq_some_iff.mp Hptr.1
    rw [← this.2]; exact List.set_getElem_self this.1
  ihave Hx : instAt γ i ⟨toN replica, toN n⟩ ptr (some w) $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hlprs Hlpr]
  · iapply (instAt_some γ i _ ptr _ rfl).2
    unfold ownInst
    iexists y
    iframe Hy Hyid Hycmds Hydeps
    isplitr
    · ipureintro; exact Hyf
    rw [hlb]
    isplitr
    · ipureintro; exact Hlbnn
    unfold ownLb
    iexists yl, gs, prs
    iframe Hyl Hcp Hlcmds Hlprs Hlpr
    rw [hdo]
    isplitr
    · ipureintro; exact Hylf
    isplitl []
    · simp only [Bool.false_eq_true, ite_false]; iexists DFrac.discard; iexact Hldeps
    ipureintro; exact Hlprsl
  ihave Hins := Hclose $$ %ptr %(ptrQ γ i ⟨toN replica, toN n⟩ ptr w) [Hptrs] [Hx]
  · simp only [hset]; iexact Hptrs
  · unfold ptrQ; isplitr
    · ipureintro; rfl
    iexact Hx
  rw [updP_updP]
  -- the loop (the model's `sent` is ghost: the code does not count)
  have hL5 : L.length = nR := HLn.1
  have hi : i < nR := hwf.hi
  obtain ⟨hperm, hlast, -⟩ := Hpop
  rw [hL5] at hperm hlast
  have hpeers : (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)).peers = (ord.map (fun x => sint.nat x)).take (nR - 1) := by
    simp only [bcastCommitOf, hwf.po]
  have hordlen : ord.length = nR := by have := hperm.length_eq; simpa using this
  ihave HI : (∃ k s : Nat, "Hq" ∷ q_ptr ↦ W64 k ∗
      "%Hks" ∷ ⌜k ≤ nR - 1 ∧ s ≤ k⌝ ∗ "Hf" ∷ repFrag γ i σ ∗
      "Hp" ∷ pendFrag γ i ({ (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)) with peers := (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)).peers.drop k, sent := s }).norm ∗
      "Hob" ∷ outboxesNil γ i : IProp GF) $$ [q Hf Hp Hob]
  · iexists 0, 0
    iframe q Hf Hob
    isplitr
    · ipureintro; unfold nR; omega
    have e0 : ({ (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)) with peers := (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)).peers.drop 0, sent := 0 } : Bcast) = (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)) := rfl
    rw [e0]
    iexact Hp
  wp_for HI
  ihave %Hpolen := ownSlice_len _ _ _ $$ Hpos
  wp_if_destruct
  · -- an iteration: peer `ord[k]`
    have hk : k < nR - 1 := by
      have h := Hif; rw [hL5] at h; unfold nR at *; have := Hks.1
      simp only [show (5 : Nat) - 1 = 4 from rfl] at *
      have : sint.Z (W64 ((k : Nat) : Int)) = (k : Int) := by word
      word
    obtain ⟨t, hot, htn, hti, htt⟩ := prefPeers_ok i ord hperm hlast hi hord k hk
    have hb : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z po.len := by
      have := Hpolen.1; have := Hpolen.2; rw [hordlen] at *; unfold nR at *
      constructor <;> word
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index po _ ord _ (W32 t) hb.1 $$ [$Hpos] as -
    · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact hot
    wp_apply (lc := 1) (wp_alive γ i r rr L p Rext (W32 t) ⟨by word, by rw [hL5]; unfold nR at *; word⟩)
      $$ [$Hrr $Hfw] as %a -
    -- the broadcast's ghost step for this read
    have hdrop' : (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)).peers.drop k = t :: (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)).peers.drop (k + 1) := by
      have hk' : k < ((ord.map (fun x => sint.nat x)).take (nR - 1)).length := by
        simp [hordlen]; omega
      rw [hpeers, List.drop_eq_getElem_cons hk']
      congr 1
      simp only [List.getElem_take, List.getElem_map]
      rw [List.getElem?_eq_getElem (by omega)] at hot
      rw [Option.some.inj hot, htt]
    have hnorm : ({ (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)) with peers := (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)).peers.drop k, sent := s } : Bcast).norm =
        some { (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)) with peers := (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)).peers.drop k, sent := s } := by
      unfold Bcast.norm
      rw [if_neg]
      rw [hdrop']
      simp only [bcastCommitOf, reduceCtorEq, false_or]
      have := Hks.2; unfold nR at *; omega
    rw [hnorm]
    iapply fupd_wp
    imod bcast_step γ i σ _ t _ a hdrop' htn hi $$ Hinv Hf Hp Hob Hlc1 with
      ⟨Hf, Hp, Ho, Hobc⟩
    imodintro
    rw [bcastRep_noTrack _ _ _ rfl]
    have hk1 : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by
      have : k < 4 := hk; word
    have hnext : ∀ a : Bool, ({ (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)) with peers := (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)).peers.drop k, sent := s } : Bcast).next a =
        ({ (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)) with peers := (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)).peers.drop (k + 1), sent := if a then s + 1 else s } : Bcast).norm := by
      intro a
      unfold Bcast.next
      simp only [hdrop']
      cases a <;> rfl
    rw [hnext]
    rcases a with _ | _
    · -- not alive: the next peer
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_for_post
      iframe
      iexists k + 1, s
      rw [← hk1]
      iframe Hq Hf Hp
      isplitr
      · ipureintro; exact ⟨by omega, by omega⟩
      iapply Hobc $$ Ho
    · -- alive: the send
      wp_auto
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index po _ ord _ (W32 t) hb.1 $$ [$Hpos] as -
      · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact hot
      ihave Hmsg : msgObj (interface.mkOk (go.GoType.PointerType epaxos.Commit.ty) #«$r0_ptr»)
          (Msg.commit (commitOf σ replica n lb)) DFrac.discard $$ []
      · unfold msgObj
        iexists MsgKind.commit, «$r0_ptr»
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        unfold ownMsg ownCommit commitOf ownDeps
        iexists yl.cmds', yl.deps'
        rw [hwf.id, ← Hylf.1, ← Hylf.2.2.2.2.2.2.2.2.2.1]
        iframe Hec Hcmd Hldeps
      wp_apply (wp_bcast_send hS γ r rr i L p Rext ord t
        (interface.mkOk (go.GoType.PointerType epaxos.Commit.ty) #«$r0_ptr»)
        (Msg.commit (commitOf σ replica n lb)) DFrac.discard (W8 15) rfl
        ⟨by rw [hL5]; exact htn, hti, rfl, hm⟩) $$ [Ho Hmsg]
      · isplitl []
        · unfold hdCtx epROFields prefOrder; iexact Hctx0
        iframe Hmsg
        rw [show (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)).m = Msg.commit (commitOf σ replica n lb) from rfl]
        iexact Ho
      iintro ⟨-, Ho⟩
      ihave Hob := Hobc $$ Ho
      wp_auto
      wp_for_post
      iframe
      iexists k + 1, s + 1
      rw [← hk1]
      iframe Hq Hf Hp Hob
      ipureintro; exact ⟨by omega, by omega⟩
  · -- every peer read: the loop ends
    have hk4 : k = nR - 1 := by
      have h := Hif; rw [hL5] at h; have := Hks.1; unfold nR at *
      simp only [show (5 : Nat) - 1 = 4 from rfl] at *
      word
    have hnone : ({ (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)) with peers := (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)).peers.drop k, sent := s } : Bcast).norm = none := by
      unfold Bcast.norm
      rw [if_pos]
      left
      rw [hpeers, hk4]
      simp
    rw [hnone]
    wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
    iapply HΦ
    unfold ptrQ
    iframe Hins Hrest Hf Hp Hob

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
