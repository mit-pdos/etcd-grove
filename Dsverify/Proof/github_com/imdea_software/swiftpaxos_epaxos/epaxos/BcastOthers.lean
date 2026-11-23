/-
`bcastPreAccept`, `bcastCommit`, `bcastPrepare` (the pattern of `wp_bcastAccept`, `Bcast.lean`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Bcast

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

/-! ## `bcastPrepare`'s cyclic peers -/

/-- `q = (q + 1) % N` on `q = (r.Id + j) % N`. -/
theorem cyc_step (i j : Nat) (hi : i < nR) (hj : j < nR) :
    BitVec.srem (W32 (((i + j) % nR : Nat) : Int) + W32 1) (W32 5) =
      W32 (((i + (j + 1)) % nR : Nat) : Int) := by
  unfold nR at *
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- `q == r.Id` exactly after `N` steps. -/
theorem cyc_eq (i j : Nat) (hi : i < nR) (hj : j < nR) :
    W32 (((i + (j + 1)) % nR : Nat) : Int) = W32 (i : Int) ↔ j + 1 = nR := by
  unfold nR at *
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem cyc_peer (i j : Nat) (hi : i < nR) :
    (i + (j + 1)) % nR < nR ∧ sint.Z (W32 (((i + (j + 1)) % nR : Nat) : Int)) =
      (((i + (j + 1)) % nR : Nat) : Int) := by
  have h : (i + (j + 1)) % nR < nR := Nat.mod_lt _ (by unfold nR; omega)
  refine ⟨h, ?_⟩
  unfold nR at *
  word

theorem cyclePeers_drop (σ : RState) (j : Nat) (hj : j < nR - 1) :
    (cyclePeers σ).drop j = (σ.id + (j + 1)) % nR :: (cyclePeers σ).drop (j + 1) := by
  have hl : j < (cyclePeers σ).length := by simp [cyclePeers]; exact hj
  rw [List.drop_eq_getElem_cons hl]
  congr 1
  simp only [cyclePeers, List.getElem_map, List.getElem_range]
  congr 1; omega

theorem W32_toN (x : w32) (h : 0 ≤ sint.Z x) : W32 ((toN x : Nat) : Int) = x := by
  unfold toN
  rw [Int.toNat_of_nonneg h]
  word

theorem cyclePeers_drop_all (σ : RState) : (cyclePeers σ).drop (nR - 1) = [] := by
  simp [cyclePeers]

/-! ## `bcastPreAccept`'s `lb.preAcceptsSent` -/

/-- The bookkeeping after `s` sends of `bcastPreAccept` (`lb.preAcceptsSent = s`, unchanged
before the first). -/
def paLb (lb : LbRec) (s : Nat) : LbRec :=
  if s = 0 then lb else { lb with preAcceptsSent := W64 s }

/-- The replica's state after `s` sends of `bcastPreAccept` for `x` (`w` its instance). -/
def paSt (σ : RState) (x : InstId) (w : InstRec) (lb : LbRec) (s : Nat) : RState :=
  σ.setInst x { w with lb := some (paLb lb s) }

theorem paLb_clientProposals (lb : LbRec) (s : Nat) :
    (paLb lb s).clientProposals = lb.clientProposals := by unfold paLb; split <;> rfl
theorem paLb_cmds (lb : LbRec) (s : Nat) : (paLb lb s).cmds = lb.cmds := by
  unfold paLb; split <;> rfl
theorem paLb_deps (lb : LbRec) (s : Nat) : (paLb lb s).deps = lb.deps := by
  unfold paLb; split <;> rfl
theorem paLb_prepareReplies (lb : LbRec) (s : Nat) :
    (paLb lb s).prepareReplies = lb.prepareReplies := by unfold paLb; split <;> rfl
theorem paLb_depsOwned (lb : LbRec) (s : Nat) : lbDepsOwned (paLb lb s) = lbDepsOwned lb := by
  unfold paLb; split <;> rfl

theorem paSt_zero (σ : RState) (x : InstId) (w : InstRec) (lb : LbRec)
    (hw : σ.inst x = some w) (hlb : w.lb = some lb) : paSt σ x w lb 0 = σ := by
  have hw' : ({ w with lb := some lb } : InstRec) = w := by cases w; simp_all
  simp only [paSt, paLb, ↓reduceIte, RState.setInst, hw']
  rw [upd_self _ _ _ hw]

theorem paSt_inst (σ : RState) (x : InstId) (w : InstRec) (lb : LbRec) (s : Nat) :
    (paSt σ x w lb s).inst x = some { w with lb := some (paLb lb s) } := by
  simp [paSt, RState.setInst, upd]

theorem paLb_succ (lb : LbRec) (s : Nat) :
    ({ paLb lb s with preAcceptsSent := W64 ((s + 1 : Nat) : Int) } : LbRec) = paLb lb (s + 1) := by
  unfold paLb; split <;> simp

/-- A `bcastPreAccept` step on the state after `s` sends. -/
theorem bcastRep_pa (σ : RState) (x : InstId) (w : InstRec) (lb : LbRec) (s : Nat) (b : Bcast)
    (hx : b.x = x) (ht : b.trackPA = true) (hp : b.peers ≠ []) (hs : b.sent = s) (a : Bool) :
    bcastRep (paSt σ x w lb s) b a = paSt σ x w lb (if a then s + 1 else s) := by
  cases a
  · simp [bcastRep]
  · simp only [bcastRep, ht, hp, hs, ne_eq, not_false_eq_true, _root_.and_self, ↓reduceIte]
    unfold setPreAcceptsSent
    rw [hx, paSt_inst]
    simp only
    rw [paLb_succ]
    unfold paSt RState.setInst
    congr 1
    funext y
    simp only [upd]
    split <;> rfl

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- `fastQuorumReplies()` = `2F - 1` = 3. -/
theorem wp_fastQuorumReplies (r rr : Loc) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fld rr go!"F" ↦□ W64 2 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"fastQuorumReplies"))
        (Val #()))
    {{ RET #(W64 3); True }} := by
  wp_start as ⟨#Hrr, #HF⟩
  wp_auto
  rw [show W64 2 * W64 2 - W64 1 = W64 3 from rfl]
  iapply HΦ
  iempintro

set_option maxHeartbeats 4000000 in
/-- `bcastPreAccept(replica, instance)`: the PreAccept built from `lb`, sent to the first
`2F - 1` alive peers of `PreferredPeerOrder[0..N-2]`, `lb.preAcceptsSent = sent` after each send
(`bcastRep`'s `setPreAcceptsSent`). -/
theorem wp_bcastPreAccept (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (i : Nat) (r rr : Loc)
    (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (ord : List w32) (σ : RState)
    (replica n : w32) (w : InstRec) (lb : LbRec) (hwf : RepWf i σ ord)
    (hq : 0 ≤ zz replica ∧ zz replica < nR) (hn : 0 ≤ zz n ∧ toN n + 1 < MAX_INSTANCE)
    (hw : σ.inst ⟨toN replica, toN n⟩ = some w) (hlb : w.lb = some lb)
    (hdo : lbDepsOwned lb = false) (hm : (Msg.preAccept (preAcceptOf σ replica n lb)).wf)
    (hord : ∀ o ∈ ord, 0 ≤ sint.Z o) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ repFrag γ i σ ∗
        pendFrag γ i (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)).norm ∗
        outboxesNil γ i }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"bcastPreAccept"))
        (Val #replica)) (Val #n))
    {{ RET #(); ∃ σ' : RState, ownRep γ i r σ' ∗ repFrag γ i σ' ∗ pendFrag γ i none ∗
        outboxesNil γ i }} := by
  wp_start as ⟨#Hctx, Hrep, Hf, Hp, Hob⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  rw [ownRep_unseal]; unfold ownRepDef
  icases Hrep with ⟨%Hib, %Hcb, Hinsts, Hcrt, Hcut, Heut, Hconf, Hmsk, HmaxSeq, Hlead, Hmrb,
    Hstore, Hpeer⟩
  have hq' : toN replica < nR := by
    have := hq.1; have := hq.2; simp only [toN, zz] at *; omega
  have hn' : toN n < MAX_INSTANCE := by have := hn.2; omega
  icases repInsts_acc γ i r σ.inst ⟨toN replica, toN n⟩ hq' hn' $$ Hinsts with
    ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  rw [hw]
  unfold instAt ownInst
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
  icases Hro with ⟨-, -, #Hpa, -⟩
  unfold prefOrder
  icases Hpo with ⟨%po, #Hpof, #Hpos, %Hpop⟩
  wp_auto
  ipersist «$r0»
  ihave #Hepa : «$r0_ptr» ↦□ epaxos.PreAccept.mk (W32 i) replica n yl.lastTriedBallot' yl.cmds'
      yl.seq' yl.deps' $$ [«$r0»]
  · iexact «$r0»
  iclear «$r0»
  -- the message object
  rw [hdo]
  simp only [Bool.false_eq_true, if_false]
  icases Hldeps with ⟨%dq0, Hldeps⟩
  ipersist Hldeps
  icases cmdsRep_dup _ _ $$ Hlcmds with ⟨Hlcmds, #Hcmd⟩
  wp_apply (wp_fastQuorumReplies r rr) $$ [$Hpe $Hrr $HF]
  -- the state, closable at any number `s` of sends (`lb.preAcceptsSent = s`)
  have hset : ptrs.set (toN n) ptr = ptrs := by
    have := List.getElem?_eq_some_iff.mp Hptr.1
    rw [← this.2]; exact List.set_getElem_self this.1
  ihave Hcl : (∀ s : Nat, y.lb' ↦ { yl with preAcceptsSent' := (paLb lb s).preAcceptsSent } -∗
      ownRep γ i r (paSt σ ⟨toN replica, toN n⟩ w lb s)) $$ [Hclose Hptrs Hy Hycmds Hydeps Hcp Hlcmds Hlprs Hlpr
        Hcrt Hcut Heut Hconf Hmsk HmaxSeq Hlead Hmrb Hstore Hpeer]
  · iintro %s Hyl
    ihave Hins := Hclose $$ %ptr %(some { w with lb := some (paLb lb s) }) [Hptrs]
      [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hlprs Hlpr]
    · simp only [hset]; iexact Hptrs
    · iexists y
      iframe Hy Hyid Hycmds Hydeps
      isplitr
      · ipureintro; exact Hyf
      isplitr
      · ipureintro; exact Hlbnn
      iexists { yl with preAcceptsSent' := (paLb lb s).preAcceptsSent }, gs, prs
      rw [paLb_clientProposals, paLb_cmds, paLb_deps, paLb_prepareReplies, paLb_depsOwned, hdo]
      iframe Hyl Hcp Hlcmds Hlprs Hlpr
      isplitr
      · ipureintro
        unfold paLb; split <;> exact ⟨Hylf.1, Hylf.2.1, Hylf.2.2.1, Hylf.2.2.2.1, Hylf.2.2.2.2.1,
          Hylf.2.2.2.2.2.1, Hylf.2.2.2.2.2.2.1, Hylf.2.2.2.2.2.2.2.1, Hylf.2.2.2.2.2.2.2.2.1,
          Hylf.2.2.2.2.2.2.2.2.2.1, Hylf.2.2.2.2.2.2.2.2.2.2.1, rfl⟩
      isplitl []
      · simp only [Bool.false_eq_true, ite_false]; iexists DFrac.discard; iexact Hldeps
      ipureintro; exact Hlprsl
    rw [ownRep_unseal]; unfold ownRepDef paSt RState.setInst
    iframe
    ipureintro; exact ⟨instBounds_upd _ _ _ Hib hq' hn.2, Hcb⟩
  have hyl0 : ({ yl with preAcceptsSent' := (paLb lb 0).preAcceptsSent } :
      epaxos.LeaderBookkeeping) = yl := by
    rw [show paLb lb 0 = lb from rfl, ← Hylf.2.2.2.2.2.2.2.2.2.2.2]
  ihave Hyl : y.lb' ↦ { yl with preAcceptsSent' := (paLb lb 0).preAcceptsSent } $$ [Hyl]
  · rw [hyl0]; iexact Hyl
  ihave Hf : repFrag γ i (paSt σ ⟨toN replica, toN n⟩ w lb 0) $$ [Hf]
  · rw [paSt_zero σ _ w lb hw hlb]; iexact Hf
  -- the loop
  have hL5 : L.length = nR := HLn.1
  have hi : i < nR := hwf.hi
  obtain ⟨hperm, hlast, -⟩ := Hpop
  rw [hL5] at hperm hlast
  have hpeers : (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)).peers = (ord.map (fun x => sint.nat x)).take (nR - 1) := by
    simp only [bcastPreAcceptOf, hwf.po]
  have hordlen : ord.length = nR := by have := hperm.length_eq; simpa using this
  ihave HI : (∃ k s : Nat, "Hq" ∷ q_ptr ↦ W64 k ∗ "Hs" ∷ sent_ptr ↦ W64 s ∗
      "%Hks" ∷ ⌜k ≤ nR - 1 ∧ s < 2 * fR - 1⌝ ∗ "Hf" ∷ repFrag γ i (paSt σ ⟨toN replica, toN n⟩ w lb s) ∗
      "Hp" ∷ pendFrag γ i ({ (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)) with peers := (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)).peers.drop k, sent := s }).norm ∗
      "Hob" ∷ outboxesNil γ i ∗
      "Hyl" ∷ y.lb' ↦ { yl with preAcceptsSent' := (paLb lb s).preAcceptsSent } :
      IProp GF) $$ [q sent Hf Hp Hob Hyl]
  · iexists 0, 0
    iframe q sent Hf Hob Hyl
    isplitr
    · ipureintro; unfold nR fR; omega
    have e0 : ({ (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)) with peers := (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)).peers.drop 0, sent := 0 } : Bcast) = (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)) := rfl
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
    have hdrop' : (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)).peers.drop k = t :: (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)).peers.drop (k + 1) := by
      have hk' : k < ((ord.map (fun x => sint.nat x)).take (nR - 1)).length := by
        simp [hordlen]; omega
      rw [hpeers, List.drop_eq_getElem_cons hk']
      congr 1
      simp only [List.getElem_take, List.getElem_map]
      rw [List.getElem?_eq_getElem (by omega)] at hot
      rw [Option.some.inj hot, htt]
    have hnorm : ({ (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)) with peers := (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)).peers.drop k, sent := s } : Bcast).norm =
        some { (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)) with peers := (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)).peers.drop k, sent := s } := by
      unfold Bcast.norm
      rw [if_neg]
      rw [hdrop']
      simp only [bcastPreAcceptOf, reduceCtorEq, false_or]
      have := Hks.2; unfold nR fR at *; omega
    rw [hnorm]
    iapply fupd_wp
    imod bcast_step γ i _ _ t _ a hdrop' htn hi $$ Hinv Hf Hp Hob Hlc1 with
      ⟨Hf, Hp, Ho, Hobc⟩
    imodintro
    rw [bcastRep_pa σ ⟨toN replica, toN n⟩ w lb s _ rfl rfl (by rw [hdrop']; exact List.cons_ne_nil _ _) rfl a]
    have hk1 : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by
      have : k < 4 := hk; word
    have hnext : ∀ a : Bool, ({ (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)) with peers := (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)).peers.drop k, sent := s } : Bcast).next a =
        ({ (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)) with peers := (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)).peers.drop (k + 1), sent := if a then s + 1 else s } : Bcast).norm := by
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
      iframe Hq Hs Hf Hp Hyl
      isplitr
      · ipureintro; exact ⟨by omega, Hks.2⟩
      iapply Hobc $$ Ho
    · -- alive: the send
      simp only [↓reduceIte]
      wp_auto
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index po _ ord _ (W32 t) hb.1 $$ [$Hpos] as -
      · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact hot
      ihave Hmsg : msgObj (interface.mkOk (go.GoType.PointerType epaxos.PreAccept.ty) #«$r0_ptr»)
          (Msg.preAccept (preAcceptOf σ replica n lb)) DFrac.discard $$ []
      · unfold msgObj
        iexists MsgKind.preAccept, «$r0_ptr»
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        unfold ownMsg ownPreAccept preAcceptOf ownDeps
        iexists yl.cmds', yl.deps'
        rw [hwf.id, ← Hylf.2.2.2.2.2.2.2.1, ← Hylf.2.2.2.2.2.2.2.2.2.1]
        iframe Hepa Hcmd Hldeps
      wp_apply (wp_bcast_send hS γ r rr i L p Rext ord t
        (interface.mkOk (go.GoType.PointerType epaxos.PreAccept.ty) #«$r0_ptr»)
        (Msg.preAccept (preAcceptOf σ replica n lb)) DFrac.discard (W8 11) rfl
        ⟨by rw [hL5]; exact htn, hti, rfl, hm⟩) $$ [Ho Hmsg]
      · isplitl []
        · unfold hdCtx epROFields prefOrder; iexact Hctx0
        iframe Hmsg
        rw [show (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)).m = Msg.preAccept (preAcceptOf σ replica n lb) from rfl]
        iexact Ho
      iintro ⟨-, Ho⟩
      ihave Hob := Hobc $$ Ho
      wp_auto
      have hs1 : W64 (s : Int) + W64 1 = W64 ((s + 1 : Nat) : Int) := by
        have := Hks.2; unfold nR fR at *; word
      rw [hs1]
      have hpa : (paLb lb (s + 1)).preAcceptsSent = W64 ((s + 1 : Nat) : Int) := by simp [paLb]
      ihave Hyl : y.lb' ↦ { yl with preAcceptsSent' := (paLb lb (s + 1)).preAcceptsSent } $$ [Hyl]
      · rw [hpa]; iexact Hyl
      by_cases hs3 : 2 * fR - 1 ≤ s + 1
      · -- enough sends: the loop ends
        have hd : decide (sint.Z (W64 3) ≤ sint.Z (W64 ((s + 1 : Nat) : Int))) = true := by
          have := Hks.2; unfold nR fR at *
          simp only [decide_eq_true_eq]; word
        rw [hd]
        wp_auto
        wp_for_post
        have hnone : ({ (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)) with peers := (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)).peers.drop (k + 1), sent := s + 1 } : Bcast).norm =
            none := by
          unfold Bcast.norm
          rw [if_pos]
          right
          simp only [bcastPreAcceptOf]
          exact hs3
        rw [hnone]
        wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
        iapply HΦ
        ihave Hrep := Hcl $$ %(s + 1) Hyl
        iexists paSt σ ⟨toN replica, toN n⟩ w lb (s + 1)
        rw [ownRep_unseal]; unfold ownRepDef
        iframe Hrep Hf Hp Hob
      · -- the next peer
        have hd : decide (sint.Z (W64 3) ≤ sint.Z (W64 ((s + 1 : Nat) : Int))) = false := by
          have := Hks.2; unfold nR fR at *
          simp only [decide_eq_false_iff_not]; word
        rw [hd]
        wp_auto
        wp_for_post
        iframe
        iexists k + 1, s + 1
        rw [← hk1]
        iframe Hq Hs Hf Hp Hob Hyl
        ipureintro; constructor
        · omega
        · omega
  · -- every peer read: the loop ends
    have hk4 : k = nR - 1 := by
      have h := Hif; rw [hL5] at h; have := Hks.1; unfold nR at *
      simp only [show (5 : Nat) - 1 = 4 from rfl] at *
      word
    have hnone : ({ (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)) with peers := (bcastPreAcceptOf σ ⟨toN replica, toN n⟩ (preAcceptOf σ replica n lb)).peers.drop k, sent := s } : Bcast).norm = none := by
      unfold Bcast.norm
      rw [if_pos]
      left
      rw [hpeers, hk4]
      simp
    rw [hnone]
    wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
    iapply HΦ
    ihave Hrep := Hcl $$ %s Hyl
    iexists paSt σ ⟨toN replica, toN n⟩ w lb s
    rw [ownRep_unseal]; unfold ownRepDef
    iframe Hrep Hf Hp Hob

set_option maxHeartbeats 4000000 in
/-- `bcastCommit(replica, instance)`: the Commit built from `lb` (ballot `lb.ballot`), sent to
every alive peer of `PreferredPeerOrder[0..N-2]`. -/
theorem wp_bcastCommit (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (i : Nat) (r rr : Loc)
    (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (ord : List w32) (σ : RState)
    (replica n : w32) (w : InstRec) (lb : LbRec) (hwf : RepWf i σ ord)
    (hq : 0 ≤ zz replica ∧ zz replica < nR) (hn : 0 ≤ zz n ∧ toN n + 1 < MAX_INSTANCE)
    (hw : σ.inst ⟨toN replica, toN n⟩ = some w) (hlb : w.lb = some lb)
    (hdo : lbDepsOwned lb = false) (hm : (Msg.commit (commitOf σ replica n lb)).wf)
    (hord : ∀ o ∈ ord, 0 ≤ sint.Z o) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ repFrag γ i σ ∗
        pendFrag γ i (bcastCommitOf σ ⟨toN replica, toN n⟩ (commitOf σ replica n lb)).norm ∗
        outboxesNil γ i }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"bcastCommit"))
        (Val #replica)) (Val #n))
    {{ RET #(); ownRep γ i r σ ∗ repFrag γ i σ ∗ pendFrag γ i none ∗ outboxesNil γ i }} := by
  wp_start as ⟨#Hctx, Hrep, Hf, Hp, Hob⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  rw [ownRep_unseal]; unfold ownRepDef
  icases Hrep with ⟨%Hib, %Hcb, Hinsts, Hcrt, Hcut, Heut, Hconf, Hmsk, HmaxSeq, Hlead, Hmrb,
    Hstore, Hpeer⟩
  have hq' : toN replica < nR := by
    have := hq.1; have := hq.2; simp only [toN, zz] at *; omega
  have hn' : toN n < MAX_INSTANCE := by have := hn.2; omega
  icases repInsts_acc γ i r σ.inst ⟨toN replica, toN n⟩ hq' hn' $$ Hinsts with
    ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  rw [hw]
  unfold instAt ownInst
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
  ihave Hins := Hclose $$ %ptr %(some w) [Hptrs] [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hlprs Hlpr]
  · simp only [hset]; iexact Hptrs
  · iexists y
    iframe Hy Hyid Hycmds Hydeps
    isplitr
    · ipureintro; exact Hyf
    rw [hlb]
    isplitr
    · ipureintro; exact Hlbnn
    iexists yl, gs, prs
    iframe Hyl Hcp Hlcmds Hlprs Hlpr
    rw [hdo]
    isplitr
    · ipureintro; exact Hylf
    isplitl []
    · simp only [Bool.false_eq_true, ite_false]; iexists DFrac.discard; iexact Hldeps
    ipureintro; exact Hlprsl
  rw [upd_self _ _ _ hw]
  ihave Hrep : ownRep γ i r σ $$ [Hins Hcrt Hcut Heut Hconf Hmsk HmaxSeq Hlead Hmrb Hstore Hpeer]
  · rw [ownRep_unseal]; unfold ownRepDef
    iframe
    ipureintro; exact ⟨Hib, Hcb⟩
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
    rw [ownRep_unseal]; unfold ownRepDef
    iframe Hrep Hf Hp Hob

set_option maxHeartbeats 4000000 in
/-- `bcastPrepare(replica, instance)`: the Prepare at `lb.lastTriedBallot`, to every alive peer
`r.Id + 1, ..., r.Id + N - 1` (mod `N`). -/
theorem wp_bcastPrepare (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (i : Nat) (r rr : Loc)
    (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (ord : List w32) (σ : RState)
    (replica n : w32) (w : InstRec) (lb : LbRec) (hwf : RepWf i σ ord)
    (hq : 0 ≤ zz replica ∧ zz replica < nR) (hn : 0 ≤ zz n ∧ toN n + 1 < MAX_INSTANCE)
    (hw : σ.inst ⟨toN replica, toN n⟩ = some w) (hlb : w.lb = some lb) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ repFrag γ i σ ∗
        pendFrag γ i (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot).norm ∗
        outboxesNil γ i }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"bcastPrepare"))
        (Val #replica)) (Val #n))
    {{ RET #(); ownRep γ i r σ ∗ repFrag γ i σ ∗ pendFrag γ i none ∗ outboxesNil γ i }} := by
  wp_start as ⟨#Hctx, Hrep, Hf, Hp, Hob⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, -⟩
  rw [ownRep_unseal]; unfold ownRepDef
  icases Hrep with ⟨%Hib, %Hcb, Hinsts, Hcrt, Hcut, Heut, Hconf, Hmsk, HmaxSeq, Hlead, Hmrb,
    Hstore, Hpeer⟩
  have hq' : toN replica < nR := by
    have := hq.1; have := hq.2; simp only [toN, zz] at *; omega
  have hn' : toN n < MAX_INSTANCE := by have := hn.2; omega
  icases repInsts_acc γ i r σ.inst ⟨toN replica, toN n⟩ hq' hn' $$ Hinsts with
    ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  rw [hw]
  unfold instAt ownInst
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
  icases Hro with ⟨#Hprep, -⟩
  wp_auto
  ipersist «$r0»
  -- the state, closed again (the loop reads only persistent data)
  have hset : ptrs.set (toN n) ptr = ptrs := by
    have := List.getElem?_eq_some_iff.mp Hptr.1
    rw [← this.2]; exact List.set_getElem_self this.1
  ihave Hins := Hclose $$ %ptr %(some w) [Hptrs] [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlpr]
  · simp only [hset]; iexact Hptrs
  · iexists y
    iframe Hy Hyid Hycmds Hydeps
    isplitr
    · ipureintro; exact Hyf
    rw [hlb]
    isplitr
    · ipureintro; exact Hlbnn
    iexists yl, gs, prs
    iframe Hyl Hcp Hlcmds Hldeps Hlprs Hlpr
    ipureintro; exact ⟨Hylf, Hlprsl⟩
  rw [upd_self _ _ _ hw]
  ihave Hrep : ownRep γ i r σ $$ [Hins Hcrt Hcut Heut Hconf Hmsk HmaxSeq Hlead Hmrb Hstore Hpeer]
  · rw [ownRep_unseal]; unfold ownRepDef
    iframe
    ipureintro; exact ⟨Hib, Hcb⟩
  -- the loop: `q = r.Id + j` (mod `N`) after `j` steps
  have hL5 : L.length = nR := HLn.1
  have hi : i < nR := hwf.hi
  have hq0 : W32 (i : Int) = W32 (((i + 0) % nR : Nat) : Int) := by
    rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
  rw [hq0]
  ihave HI : (∃ j s : Nat, "Hq" ∷ q_ptr ↦ W32 (((i + j) % nR : Nat) : Int) ∗
      "Hs" ∷ sent_ptr ↦ W64 s ∗ "Hn" ∷ n_ptr ↦ (W64 (L.length : Int) - W64 1) ∗
      "%Hjs" ∷ ⌜j ≤ nR - 1 ∧ s ≤ j⌝ ∗ "Hf" ∷ repFrag γ i σ ∗
      "Hp" ∷ pendFrag γ i ({ (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot) with peers := (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot).peers.drop j, sent := s }).norm ∗
      "Hob" ∷ outboxesNil γ i : IProp GF) $$ [q sent n Hf Hp Hob]
  · iexists 0, 0
    iframe q sent n Hf Hob
    isplitr
    · ipureintro; unfold nR; omega
    have e0 : ({ (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot) with peers := (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot).peers.drop 0, sent := 0 } : Bcast) = (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot) := rfl
    rw [e0]
    iexact Hp
  wp_for HI
  wp_if_destruct
  · -- an iteration: `q = r.Id + j + 1`
    have hs4 : s < nR - 1 := by
      have h := Hif; rw [hL5] at h; unfold nR at *
      have := Hjs.1; have := Hjs.2
      simp only [show (5 : Nat) - 1 = 4 from rfl] at *
      word
    have hj5 : j < nR := by have := Hjs.1; unfold nR at *; omega
    have hW5 : W32 (sint.Z (W64 (L.length : Int))) = W32 5 := by rw [hL5]; rfl
    rw [hW5, cyc_step i j hi hj5]
    simp only [show sint.Z (W32 5) ≠ 0 by decide, ↓reduceIte]
    wp_auto
    rw [← hq0]
    by_cases hj4 : j + 1 = nR
    · -- back at `r.Id`: every peer read
      have hd : decide (W32 (((i + (j + 1)) % nR : Nat) : Int) = W32 (i : Int)) = true := by
        simp only [decide_eq_true_eq]; exact (cyc_eq i j hi hj5).mpr hj4
      rw [hd]
      wp_auto
      wp_for_post
      have hnone : ({ (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot) with peers := (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot).peers.drop j, sent := s } : Bcast).norm = none := by
        unfold Bcast.norm
        rw [if_pos]
        left
        rw [show j = nR - 1 by omega]
        exact cyclePeers_drop_all σ
      rw [hnone]
      wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
      iapply HΦ
      rw [ownRep_unseal]; unfold ownRepDef
      iframe Hrep Hf Hp Hob
    · have hd : decide (W32 (((i + (j + 1)) % nR : Nat) : Int) = W32 (i : Int)) = false := by
        simp only [decide_eq_false_iff_not]; exact fun h => hj4 ((cyc_eq i j hi hj5).mp h)
      rw [hd]
      wp_auto
      have hj3 : j < nR - 1 := by unfold nR at *; omega
      obtain ⟨htn, htz⟩ := cyc_peer i j hi
      have hti : (i + (j + 1)) % nR ≠ i := by
        intro h; apply hj4; apply (cyc_eq i j hi hj5).mp; rw [h]
      wp_apply (lc := 1) (wp_alive γ i r rr L p Rext (W32 (((i + (j + 1)) % nR : Nat) : Int))
        ⟨by rw [htz]; omega, by rw [htz, hL5]; exact_mod_cast htn⟩) $$ [$Hrr $Hfw] as %a -
      -- the broadcast's ghost step for this read
      have hdrop' : (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot).peers.drop j = (i + (j + 1)) % nR :: (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot).peers.drop (j + 1) := by
        have := cyclePeers_drop σ j hj3
        rw [hwf.id] at this
        exact this
      have hnorm : ({ (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot) with peers := (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot).peers.drop j, sent := s } : Bcast).norm =
          some { (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot) with peers := (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot).peers.drop j, sent := s } := by
        unfold Bcast.norm
        rw [if_neg]
        rw [hdrop']
        simp only [bcastPrepareOf, reduceCtorEq, false_or]
        omega
      rw [hnorm]
      iapply fupd_wp
      imod bcast_step γ i σ _ _ _ a hdrop' htn hi $$ Hinv Hf Hp Hob Hlc1 with
        ⟨Hf, Hp, Ho, Hobc⟩
      imodintro
      rw [bcastRep_noTrack _ _ _ rfl]
      have hnext : ∀ a : Bool, ({ (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot) with peers := (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot).peers.drop j, sent := s } : Bcast).next a =
          ({ (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot) with peers := (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot).peers.drop (j + 1), sent := if a then s + 1 else s } : Bcast).norm := by
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
        iexists j + 1, s
        iframe Hq Hs Hn Hf Hp
        isplitr
        · ipureintro; exact ⟨by omega, by omega⟩
        iapply Hobc $$ Ho
      · -- alive: the send
        simp only [↓reduceIte]
        wp_auto
        have hbm : (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot).m = Msg.prepare ⟨W32 (i : Int), replica, n, lb.lastTriedBallot⟩ := by
          simp only [bcastPrepareOf, hwf.id, W32_toN replica hq.1, W32_toN n hn.1]
        ihave Hmsg : msgObj (interface.mkOk (go.GoType.PointerType epaxos.Prepare.ty) #«$r0_ptr»)
            (Msg.prepare ⟨W32 (i : Int), replica, n, lb.lastTriedBallot⟩) DFrac.discard $$ []
        · unfold msgObj
          iexists MsgKind.prepare, «$r0_ptr»
          isplitr
          · ipureintro; exact ⟨rfl, rfl⟩
          unfold ownMsg ownPrepare
          rw [← Hylf.2.2.2.2.2.2.2.1]
          iexact «$r0»
        wp_apply (wp_bcast_send hS γ r rr i L p Rext ord ((i + (j + 1)) % nR)
          (interface.mkOk (go.GoType.PointerType epaxos.Prepare.ty) #«$r0_ptr»)
          (Msg.prepare ⟨W32 (i : Int), replica, n, lb.lastTriedBallot⟩) DFrac.discard (W8 9) rfl
          ⟨by rw [hL5]; exact htn, hti, rfl, trivial⟩) $$ [Ho Hmsg]
        · isplitl []
          · unfold hdCtx epROFields prefOrder; iexact Hctx0
          iframe Hmsg
          rw [← hbm]
          iexact Ho
        iintro ⟨-, Ho⟩
        ihave Hob := Hobc $$ Ho
        wp_auto
        have hs1 : W64 (s : Int) + W64 1 = W64 ((s + 1 : Nat) : Int) := by
          unfold nR at *; word
        rw [hs1]
        wp_for_post
        iframe
        iexists j + 1, s + 1
        iframe Hq Hs Hn Hf Hp Hob
        ipureintro; exact ⟨by omega, by omega⟩
  · -- `sent = n`: the loop ends
    have hs4 : s = nR - 1 := by
      have h := Hif; rw [hL5] at h; unfold nR at *
      have := Hjs.1; have := Hjs.2
      simp only [show (5 : Nat) - 1 = 4 from rfl] at *
      word
    have hnone : ({ (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot) with peers := (bcastPrepareOf σ ⟨toN replica, toN n⟩ lb.lastTriedBallot).peers.drop j, sent := s } : Bcast).norm = none := by
      unfold Bcast.norm
      rw [if_pos]
      right
      simp only [bcastPrepareOf]
      omega
    rw [hnone, ← hq0]
    wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
    iapply HΦ
    rw [ownRep_unseal]; unfold ownRepDef
    iframe Hrep Hf Hp Hob

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
