/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/NewLeaderProof.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**Phase 4 (round N1, sv-swc): `handleNewLeader`'s proof** (recovery.go:15-65) over its callees'
specs (NewLeaderSpecs.lean), and the run loop's `newLeader` arm (its instance in normal
operation). Top-down (D52): every Go statement is stepped; the callees are hypotheses and the
ghost steps not proved yet are named sorries `N1: <item>`.

The proof is by Löb induction (the recovery loop's `newLeaderChan` case calls `handleNewLeader`
again, from the recovering state). Steps:
1. `if r.ballot >= msg.Ballot { return }` (the state opened: `swift.runInvR_open`);
2. `log.Println`;
3. `if r.status == NORMAL { r.repchan.stop(); r.stopDescs() }`: both ways the epoch is stopped
   (`epStoppedX`): in normal operation `replyChan.stop` (`epR_stop_ofD`) and `stopDescs`
   (`stopDescs.wp_specI`);
4. `r.status = RECOVERING`, `r.ballot = msg.Ballot` under `ballotL`: the halves and quarters of
   the two fields (`runSt`, `epStopped`, `ballotLInv`); the node state's new ballot
   (`swift.newBallot_stepD`, with the epoch token's agreement `swift.nl_epoch_agree`);
5. `r.recStart = time.Now()`;
6. the ack `&MNewLeaderAckN{r.Id, r.ballot, r.cballot}` and `fillNewLeaderAckN` (in recovery,
   `recInvB`);
7. `SendTo(msg.Replica, …)` or `handleNewLeaderAckN`;
8. the loop `for r.status == RECOVERING { select { … } }` over `∃ s, runInvR s`
   (`swift.runInvR_status`): the three arms `swift.recArm_newLeader` (the induction
   hypothesis), `swift.recArm_ackN`, `swift.recArm_sync`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.pkg.TimeInit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewLeaderReqs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncTail
-- round N3: gob's encoder proofs, for `MSync.marshal_proofG` at the link (the set's handler)
public import Dsverify.Proof.encoding.gob.NewEncoder
public import Dsverify.Proof.encoding.gob.Encoder__EncodeW
-- round N3: the ack's `Marshal`
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MarshalAckN
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.PutVarint
-- round N3: item 4's report order (pure)
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FillOrder
-- round N4: `fillNewLeaderAckN`'s walk
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FillAckN
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GhostSteps2

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- The induction hypothesis, hidden from the WP tactics (as Perennial's `sortHide`). -/
def swift.nlHide (P : IProp netDistGF) : IProp netDistGF := P

theorem swift.nlHide_intro {P Q : IProp netDistGF} : (□ swift.nlHide P -∗ Q) ⊢ (□ P -∗ Q) := .rfl

theorem swift.nlHide_elim {P Q : IProp netDistGF} : (□ P -∗ Q) ⊢ (□ swift.nlHide P -∗ Q) := .rfl

/-- **The run loop's state, opened** (normal, `s = true`, or recovering): `runInv`/`recInv`
without `runSt`, with the epoch running (`descDS`) or stopped (`epStoppedX`). -/
def swift.runOpen (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (s : Bool)
    (v : swift.RunV) (w : swift.LView) (sq : sp.Seq) : IProp netDistGF :=
  iprop(swift.descCtxE γ γc γm x.γl x.γw x.γv x.γe x.γo x.γx x.γxe x.γxm x.γxp x.γxu x.γrp x.γcg x.γout x.γcl x.γdc x.γdl
      x.str rp x.rr x.N x.r x.k ∗
    swift.syncCtx γ x.N x.r x.syncN rp ∗
    swift.runLoopCtx rp γ γc γm x ∗
    swift.seqOwn γ rp x.k ∗
    swift.runReader rp x.γdl ∗
    swift.runFields γ rp x.rr x.N x.r ∗ swift.propDepsOwn rp sq ∗
    (if s then swift.descDS γ γc γm x rp else swift.epStoppedXc γ x rp (sint.Z v.cballot).toNat) ∗
    ⌜w.2.2.1 = s ∧ (s = false → w.2.1 < w.1 ∧ v.status = swift.stRECOVERING)⌝)

end defs

/-! ## Plumbing: the state's fields the loop and the first `if` read -/

section plumbing
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

theorem swift.stNORMAL_ne_REC : swift.stNORMAL ≠ swift.stRECOVERING := by decide

/-- The run loop's half of `status`, out of either state: `NORMAL` iff normal. -/
theorem swift.runInvR_status (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (s : Bool) :
    swift.runInvR rp γ γc γm x s ⊢ ∃ st : w64,
      typedPointsto (swift.fld rp go!"status") st (DFrac.own (1 : Iris.Qp).half) ∗
      ⌜(s = true → st = swift.stNORMAL) ∧ (s = false → st = swift.stRECOVERING)⌝ ∗
      (typedPointsto (swift.fld rp go!"status") st (DFrac.own (1 : Iris.Qp).half) -∗
        swift.runInvR rp γ γc γm x s) := by
  cases s
  · simp only [swift.runInvR, Bool.false_eq_true, ↓reduceIte]
    iintro H
    iunfold swift.recInv at H
    icases H with ⟨%bl, %cb, H⟩
    iunfold swift.recInvB at H
    icases H with ⟨#Hd, #Hsc, Hrl, ⟨%ld, %v, %M0, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hep⟩
    iunfold swift.runSt at Hrun
    icases Hrun with ⟨Hbal, Hcb, Hstat, Hhd, Hhdl, Hhdc, Hpr, Hprs, Hk, Hks, Hhl, Hhls, Hpe,
      Hpes, Hls0, Hlso, Hw, #Hlb, %Hok2⟩
    iexists v.status
    iframe Hstat
    isplitr
    · ipureintro; simp only [Bool.false_eq_true, false_implies, true_and, forall_const]
      exact Hn.2.2.2.2
    iintro Hstat
    iunfold swift.recInv
    iexists bl, cb
    iunfold swift.recInvB
    iframe Hd Hsc Hrl Hseq Hdr Hrf Hep
    iexists ld, v, M0, bs, hd, w
    isplitr [Hpd]
    · iunfold swift.runSt; iframe; iframe Hlb; ipureintro; exact Hok2
    iframe Hpd
    ipureintro; exact Hn
  · simp only [swift.runInvR, ↓reduceIte]
    iintro H
    iunfold swift.runInv at H
    icases H with ⟨#Hd, #Hsc, Hrl, ⟨%ld, %v, %M0, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hds⟩
    iunfold swift.runSt at Hrun
    icases Hrun with ⟨Hbal, Hcb, Hstat, Hhd, Hhdl, Hhdc, Hpr, Hprs, Hk, Hks, Hhl, Hhls, Hpe,
      Hpes, Hls0, Hlso, Hw, #Hlb, %Hok2⟩
    iexists v.status
    iframe Hstat
    isplitr
    · ipureintro; exact ⟨fun _ => (Hok2.1.2.2.2.2.1).1 Hn, fun h => by cases h⟩
    iintro Hstat
    iunfold swift.runInv
    iframe Hd Hsc Hrl Hseq Hdr Hrf Hds
    iexists ld, v, M0, bs, hd, w
    isplitr [Hpd]
    · iunfold swift.runSt; iframe; iframe Hlb; ipureintro; exact Hok2
    iframe Hpd
    ipureintro; exact Hn

/-- Either state, opened (`swift.runOpen`). -/
theorem swift.runInvR_open (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (s : Bool) :
    swift.runInvR rp γ γc γm x s ⊣⊢ ∃ (ld : Bool) (v : swift.RunV) (M : Option sp.SyncMsg)
      (bs hd : sp.Seq) (w : swift.LView),
      swift.runSt γ x.γv rp x.N x.r ld v M bs hd w ∗ swift.runOpen rp γ γc γm x s v w (bs ++ hd) := by
  constructor
  · cases s
    · simp only [swift.runInvR, Bool.false_eq_true, ↓reduceIte]
      iintro H
      iunfold swift.recInv at H
      icases H with ⟨%bl, %cb, H⟩
      iunfold swift.recInvB at H
      icases H with ⟨#Hd, #Hsc, Hrl, ⟨%ld, %v, %M0, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hep⟩
      have hcb := Hn.2.2.2.1
      subst hcb
      iexists ld, v, M0, bs, hd, w
      iframe Hrun
      iunfold swift.runOpen
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
      iframe #
      ipureintro; exact ⟨Hn.1, fun _ => ⟨Hn.2.1, Hn.2.2.2.2⟩⟩
    · simp only [swift.runInvR, ↓reduceIte]
      iintro H
      iunfold swift.runInv at H
      icases H with ⟨#Hd, #Hsc, Hrl, ⟨%ld, %v, %M0, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hds⟩
      iexists ld, v, M0, bs, hd, w
      iframe Hrun
      iunfold swift.runOpen
      simp only [↓reduceIte]
      iframe
      iframe #
      ipureintro; exact ⟨Hn, fun h => by cases h⟩
  · cases s
    · simp only [swift.runInvR, Bool.false_eq_true, ↓reduceIte]
      iintro ⟨%ld, %v, %M0, %bs, %hd, %w, Hrun, Hop⟩
      iunfold swift.runOpen at Hop
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hop with ⟨#Hd, #Hsc, Hrl, Hseq, Hdr, Hrf, Hpd, Hep, %Hn⟩
      iunfold swift.recInv
      iexists v.ballot, v.cballot
      iunfold swift.recInvB
      iframe Hd Hsc Hrl Hseq Hdr Hrf Hep
      iexists ld, v, M0, bs, hd, w
      iframe Hrun Hpd
      ipureintro; exact ⟨Hn.1, (Hn.2 trivial).1, rfl, rfl, (Hn.2 trivial).2⟩
    · simp only [swift.runInvR, ↓reduceIte]
      iintro ⟨%ld, %v, %M0, %bs, %hd, %w, Hrun, Hop⟩
      iunfold swift.runOpen at Hop
      simp only [↓reduceIte]
      icases Hop with ⟨#Hd, #Hsc, Hrl, Hseq, Hdr, Hrf, Hpd, Hds, %Hn⟩
      iunfold swift.runInv
      iframe Hd Hsc Hrl Hseq Hdr Hrf Hds
      iexists ld, v, M0, bs, hd, w
      iframe Hrun Hpd
      ipureintro; exact Hn.1

end plumbing

/-! ## Ghost steps -/

section ghost
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- The stopped epoch's token is at the run loop's view's `(ballot, cballot)` (both agree with
the node state in `nodeInvD`). -/
theorem swift.nl_epoch_agree (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat)
    (w : swift.LView) (bc : Nat × Nat) :
    inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗ ghostVar γv (1 : Iris.Qp).half w ∗
      swift.epochTok γe (1 : Iris.Qp).half bc ⊢
    |={⊤}=> ghostVar γv (1 : Iris.Qp).half w ∗ swift.epochTok γe (1 : Iris.Qp).half bc ∗
      ⌜bc = (w.1, w.2.1)⌝ := by
  iintro ⟨#Hninv, Hw, Hep⟩
  iinv Hninv with Hi Hclose
  iunfold swift.nodeInvD at Hi
  imod Hi
  icases Hi with ⟨%st, %O, Hst, Hw2, He, HO, HS, HX, %Hok⟩
  ihave %Heq := ghostVar_agree γv w (1 : Iris.Qp).half (swift.viewOf st) (1 : Iris.Qp).half $$ Hw Hw2
  iunfold swift.epochTok at Hep
  ihave %Heq2 := ghostVar_agree γe bc (1 : Iris.Qp).half (swift.epochOf st) (1 : Iris.Qp).half $$ Hep He
  imod Hclose $$ [Hst Hw2 He HO HS HX] with -
  · inext
    iunfold swift.nodeInvD
    iexists st, O
    iframe
    ipureintro; exact Hok
  imodintro
  iunfold swift.epochTok
  iframe
  ipureintro
  subst Heq Heq2
  rfl

/-- The hash logs with a weaker leader flag (`hlogOk`'s leader clause is an implication). Round
N1 used it at the new ballot; since D56 N1-a (`localOk`'s `ld` is about `cballot`),
`handleNewLeader` keeps `ld` and does not need it. -/
theorem swift.hlogOwn_weaken (hm : Loc) (hM : GMap w64 Loc) (ld ld' : Bool) (hd : sp.Seq)
    (K : sp.CmdId → Prop) (Λ : w64 → w64 → List sp.CmdId → Prop) (h : ld' = true → ld = true) :
    swift.hlogOwn hm hM ld hd K Λ ⊢ swift.hlogOwn hm hM ld' hd K Λ := by
  unfold swift.hlogOwn
  iintro ⟨Hm, Hents, %Hc⟩
  iframe Hm
  isplitl [Hents]
  · iapply (BigSepM.bigSepM_mono_of_forall (Φ := fun k l => swift.hlogEnt ld hd K Λ k l)
      (Ψ := fun k l => swift.hlogEnt ld' hd K Λ k l) (fun {k l} => ?_)) $$ Hents
    unfold swift.hlogEnt
    iintro ⟨%σ, Ho, %Hok⟩
    iexists σ; iframe Ho; ipureintro
    obtain ⟨h1, h2, h3, h4, h5⟩ := Hok
    exact ⟨h1, h2, h3, fun hl => h4 (h hl), h5⟩
  · ipureintro; exact Hc

end ghost

/-! ## The recovery loop's arms (in recovery) -/

section arms
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [examples.swiftnet.Assumptions]

set_option goose.wp.extras true

/-- An ack from the codec (`msgRepM`, owned), persisted: its report object `ackObj` and ballot. -/
theorem swift.ackObj_of_rep (l : Loc) (rep bl cb : w32) (es : List sp.RepEntry)
    (hr : 0 ≤ sint.Z rep) (hc : 0 ≤ sint.Z cb) :
    swift.msgRepM (interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #l)
        (.newLeaderAckN rep bl cb es) ⊢
      |={⊤}=> swift.ackObj l (sp.rid rep, ⟨sp.bal cb, es⟩) ∗ swift.ackBal l bl := by
  iintro H
  iunfold swift.msgRepM at H
  icases H with ⟨%l0, %ids, %ph, %cm, %dp, %cmL, %dpL, %Hv, Hl, Hids, Hph, Hcm, Hdp, %Hlen, Hes⟩
  have hl : l0 = l := go.IntoValInj.intoVal_inj (V := Loc)
    (by simpa [interface_mkOk_inj] using Hv.symm)
  subst hl
  ipersist Hl
  ipersist Hids
  ipersist Hph
  ipersist Hcm
  ipersist Hdp
  imod swift.bigSepL_bupd es
    (fun i e => iprop(∃ (cc : state.Command) (sd : swift.SDep),
      ⌜cmL[i]? = some cc ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryOwn cc sd e))
    (fun i e => iprop(∃ (cc : state.Command) (sd : swift.SDep),
      ⌜cmL[i]? = some cc ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryObj cc sd e))
    (fun i e => by
      iintro ⟨%cc, %sd, %h, He⟩
      unfold swift.repEntryOwn swift.repEntryObj
      icases He with ⟨%vs, %hvs, Hv, Hd⟩
      ipersist Hv
      ipersist Hd
      imodintro
      iexists cc, sd
      isplitr
      · ipureintro; exact h
      iexists vs
      isplitr
      · ipureintro; exact hvs
      iframe #) $$ Hes with #Hes
  imodintro
  isplitl
  · iunfold swift.ackObj
    iexists rep, bl, cb, ids, ph, cm, dp, cmL, dpL
    iframe #
    ipureintro
    refine ⟨(Int.toNat_of_nonneg hr).symm, (Int.toNat_of_nonneg hc).symm, Hlen.1, Hlen.2⟩
  iunfold swift.ackBal
  iexists rep, cb, ids, ph, cm, dp
  iexact Hl

/-- The configuration at the run loop's `N` (persistent, from `descCtxE`). -/
theorem swift.recInv_cfg (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) :
    swift.recInv rp γ γc γm x ⊢ ∃ (fr : Bool) (l : List GoString), sp.cfg γc γm x.N fr l := by
  iintro HI
  iunfold swift.recInv at HI
  icases HI with ⟨%bl, %cb, HI⟩
  iunfold swift.recInvB at HI
  icases HI with ⟨#Hd, -⟩
  iunfold swift.descCtxE at Hd
  icases Hd with ⟨%me, %fr, %l, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #HR, #HisR, %Hids,
    -, -, -, #Hinv, #Hcfg, -⟩
  iexists fr, l
  iexact Hcfg

/-- **The recovery loop's `newLeaderAckNChan` arm**: an ack from the codec (`msgRepM`, with its
witness `msgOk`: `reported`) to `handleNewLeaderAckN.specN` (its struct persisted: `ackObj`). -/
theorem swift.recArm_ackN (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_ackN : swift.Replica.handleNewLeaderAckN.specN (hG := hG) rp γ γc γm x)
    (l : Loc) (rep bl cb : w32) (es : List sp.RepEntry) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.recInv rp γ γc γm x ∗
        swift.msgRepM (interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #l)
          (.newLeaderAckN rep bl cb es) ∗
        sp.msgOk γ γc γm (.newLeaderAckN rep bl cb es) }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleNewLeaderAckN")) (Val #l))
    {{ RET #(); swift.runInvP rp γ γc γm x false }} := by
  iintro %Φ ⟨#Hpkg, HI, Hrep, #Hok⟩ HΦ
  iunfold sp.msgOk at Hok
  icases Hok with ⟨%Hw, #Hrp, %N', %fr', %l', #Hcfg', %HrN⟩
  obtain ⟨⟨hr0, hb0⟩, hc0⟩ := Hw
  -- D56 N1-b: the sender is `< N` (`msgOk`'s configuration is the run loop's)
  ihave ⟨⟨%fr, %l0, #Hcfg⟩, HI⟩ :=
    BI.persistent_entails_right (swift.recInv_cfg rp γ γc γm x) $$ HI
  ihave %Hag := sp.cfg_agree x.N N' fr fr' l0 l' $$ [Hcfg Hcfg']
  · iframe #
  obtain ⟨rfl, -, -⟩ := Hag
  iapply fupd_wp
  imod swift.ackObj_of_rep l rep bl cb es hr0 hc0 $$ Hrep with ⟨#Hack, #HackB⟩
  imodintro
  rw [show sp.bal bl = (sint.Z bl).toNat from rfl]
  wp_apply (wp_ackN l (sp.rid rep, ⟨sp.bal cb, es⟩) bl) $$ [HI] as HP
  · iframe #
    iframe HI
    ipureintro
    exact ⟨HrN, hb0⟩
  iapply HΦ
  iexact HP

set_option maxRecDepth 4096 in
/-- **The recovery loop's `syncChan` arm**: as `swift.runArm_sync` (RunArmSync.lean), from the
recovering state: a ballot past `cballot` by `handleSync.specIR`'s recovering case (its row
disjunct `locAt b' = []`), an older one by `handleSync`'s first `return`. -/
theorem swift.recArm_sync (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_hs : swift.Replica.handleSync.specIR (hG := hG) (fun _ => swift.descDS γ γc γm x rp)
      (swift.descEpS γ γc γm x rp) (fun b => swift.descDF (x.DR γ b)) (swift.stopPS x) γ γc γm x.γl x.γw x.γv x.γd x.γe x.γo
      x.syncN rp x.rr (swift.descPC γ γc γm x rp))
    (l : Loc) (m : sp.SyncWire) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.recInv rp γ γc γm x ∗
        swift.msgRepM (interface.mkOk (go.GoType.PointerType swift.MSync.ty) #l) (.sync m) ∗
        sp.msgOk γ γc γm (.sync m) }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleSync")) (Val #l))
    {{ RET #(); swift.runInvP rp γ γc γm x false }} := by
  iintro %Φ ⟨#Hpkg, Hinv, Hrep, #Hok⟩ HΦ
  iunfold swift.recInv at Hinv
  icases Hinv with ⟨%bl, %cb, Hinv⟩
  iunfold swift.recInvB at Hinv
  icases Hinv with ⟨#Hd, #Hsc, Hrl, ⟨%ld, %v, %M0, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hep⟩
  ihave #Hctx : swift.runCtxD γ γc γm x.γl x.γw x.γv x.γe x.γo x.sn x.γdl rp x.N x.r x.k $$ [Hrl]
  · ihave #Hd3 := Hd
    iunfold swift.descCtxE at Hd3
    icases Hd3 with ⟨%me, %fr, %l, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #HR, #HisR, %Hids,
      -, -, -, #Hinv, #Hcfg, #HnI, #Hdel, #HdV, #HdI, -, -, -, -, -, -, -, -, #Hng⟩
    iunfold swift.runLoopCtx at Hrl
    icases Hrl with ⟨%s, %b, %γs, %sq, %hsl, %fr', %pl, %sam, %csv, %n, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, #HcntL, -, -, -⟩
    iunfold swift.runCtxD
    iexists x.rr, me, fr, l, dm
    iframe HR HisR Hinv Hcfg HnI Hdel HdV
    isplitr
    · ipureintro; exact Hids
    isplitr
    · iexists x.γx, x.γxp, x.γxm, γa, x.γxe, γrm, x.str; iexact HdI
    iframe Hng
    iexists x.dm, x.γn, x.d
    iexact HcntL
  ihave #Hd2 := Hd
  iunfold swift.descCtxE at Hd2
  icases Hd2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc0, %γrc, #HR, #HisR,
    %Hids, -, -, -, #Hspi, #Hcfgx, #HnI, -, -, -, -, -, -, -, -, -, -, -⟩
  -- the message and its witness
  iunfold sp.msgOk at Hok
  icases Hok with ⟨%M, %N', %fr', %l', #HsI, ⟨#Hcfg', #HlbL0⟩, %Hw⟩
  obtain ⟨-, hwok, hlead⟩ := Hw
  -- round 54 (D74 (2), 53-4): the sender is the ballot's leader (`msgOk (.sync)`), with its `locLb`
  ihave %Hag := sp.cfg_agree (γc := γc) (γm := γm) x.N N' fr fr' lg l' $$ [Hcfgx Hcfg']
  · isplitl []
    · iexact Hcfgx
    · iexact Hcfg'
  obtain ⟨hNN, -, -⟩ := Hag
  subst hNN
  ihave #HlbL : sp.locLb γ (sp.leaderOf x.N (sp.bal m.bal)) (sp.bal m.bal) (sp.syncSeq M) $$ []
  · rw [← hlead]; iexact HlbL0
  iapply fupd_wp
  imod sp.syncIs_facts ⊤ (fun _ _ => CoPset.mem_full) (sp.bal m.bal) M $$ [Hspi HsI] with %HMf
  · iframe Hspi HsI
  obtain ⟨hb0, hnd⟩ := HMf
  imod sp.syncIs_len ⊤ (fun _ _ => CoPset.mem_full) (sp.bal m.bal) M hnd $$ [Hspi HsI] with %Hlen
  · iframe Hspi HsI
  have hwf : sp.KitVal.wf (.msync m) := by
    obtain ⟨⟨ps, hp, hpp⟩, ⟨cs, hc, hcp⟩, ⟨ds, hd', hdp⟩⟩ := hwok
    simp only [sp.KitVal.wf, hp, hc, hd', Option.map_some, Option.getD_some]
    refine ⟨?_, ?_, ?_⟩
    · have h := hpp.map Prod.fst
      rw [List.map_map] at h
      exact h.nodup_iff.2 (by simpa [Function.comp_def] using hnd)
    · have h := hcp.map Prod.fst
      rw [List.map_map] at h
      exact h.nodup_iff.2 (by simpa [Function.comp_def] using hnd)
    · have h := hdp.map Prod.fst
      rw [List.map_map] at h
      exact h.nodup_iff.2 (by simpa [Function.comp_def] using hnd)
  iunfold swift.msgRepM at Hrep
  icases Hrep with ⟨%l1, %xv, %Hx, Hso⟩
  obtain ⟨hl1, hxv⟩ := Hx
  have hl : l1 = l := go.IntoValInj.intoVal_inj (V := Loc)
    (by simpa [interface_mkOk_inj] using hl1.symm)
  subst hl
  rw [hxv hwf]
  imod swift.syncMaps_of_wire l1 m M hwok hnd $$ Hso with #HMaps
  imodintro
  ihave ⟨%Hlok, Hrun⟩ := BI.persistent_entails_right
    (swift.runSt_localOk γ x.γv rp x.N x.r ld v M0 bs hd w) $$ Hrun
  by_cases hb : sp.bal m.bal < w.1
  · -- an older ballot: `handleSync`'s first `return`
    ihave #HM2 := HMaps
    iunfold swift.syncMaps at HM2
    icases HM2 with ⟨%rep, %bl', %ph, %cm, %dp, %phM, %cmM, %dpM, #Hls, -, -, -, %HMf2, -⟩
    iunfold swift.runSt at Hrun
    icases Hrun with ⟨Hbal, Hcb, Hstat, Hhd, Hhdl, Hhdc, Hpr, Hprs, Hk, Hks, Hhl, Hhls, Hpe,
      Hpes, Hls0, Hlso, Hw, #Hlb, %Hok2⟩
    ihave #Hls2 := Hls
    iStructNamedPrefix Hls2 "MS"
    obtain ⟨hvb0, hvc0, hw1, hw2, hst, hnc, -⟩ := Hlok
    have hbl := HMf2.1
    wp_method_call
    wp_auto
    try ipersist r
    try ipersist msg
    wp_if_destruct
    · try wp_auto
      iapply HΦ
      iunfold swift.runInvP
      iexists false
      isplitl
      · simp only [swift.runInvR, Bool.false_eq_true, ↓reduceIte]
        iunfold swift.recInv
        iexists bl, cb
        iunfold swift.recInvB
        iframe Hd Hsc Hrl Hseq Hdr Hrf Hep
        iexists ld, v, M0, bs, hd, w
        isplitr [Hpd]
        · iunfold swift.runSt
          iframe
          iframe Hlb
          ipureintro; exact Hok2
        iframe Hpd
        ipureintro; exact Hn
      ipureintro; intro h; cases h
    · exfalso
      have h1 : ¬ bl'.toInt < v.ballot.toInt := ‹¬ sint.Z bl' < sint.Z v.ballot›
      have h4 : sp.bal bl' < sp.bal v.ballot := by rw [hbl, ← hw1]; exact hb
      have h5 : (0 : Int) ≤ v.ballot.toInt := hvb0
      unfold sp.bal at h4
      omega
  · -- the ballot or a later one: `specIR`, recovering
    have hle : w.1 ≤ sp.bal m.bal := by omega
    have hw21 : w.2.1 < sp.bal m.bal := by have := Hn.2.1; omega
    have hloc : w.locAt (sp.bal m.bal) = [] :=
      swift.LView.locAt_nil_of_rows (fun o => Hlok.2.2.2.2.2.2.2.2.2.1 _ o hw21)
    iunfold swift.runFields at Hrf
    icases Hrf with ⟨%t, %fq, %rc, %nl, %bsN, %ppsl, %pp, Ft, FFQ, Frc, Fnl, Fbs, Hnl, FPP, Hpp,
      %Hpp, %Hnlr⟩
    iunfold swift.propDepsOwn at Hpd
    icases Hpd with ⟨%pdm, %PD, Fpd, Hpdm, -⟩
    ihave Hst := swift.runSt_runStS γ x.γv rp x.N x.r ld v M0 bs hd w (sp.bal m.bal) $$ Hrun
    ihave ⟨⟨%s, %γs, %csv, #Fsnd, #Hsbag, #Fcs, %Hcs⟩, Hrl⟩ :=
      BI.persistent_entails_right (swift.runLoopCtx_send rp γ γc γm x) $$ Hrl
    -- round 47 (sv-swb, 45-b, D61 (1)): `handleSync.specIR`'s `PC`, the descriptors' contexts
    ihave ⟨#HPCw, Hrl⟩ := BI.persistent_entails_right (swift.descPC_of rp γ γc γm x x.N x.r) $$ Hrl
    ihave #HPC := HPCw $$ Hsc [Hd]
    · unfold swift.DC.ctx; iexact Hd
    ihave #Hsc2 := Hsc
    iunfold swift.syncCtx at Hsc2
    icases Hsc2 with ⟨%dm2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      ⟨%sqS, %szS, %memS, #FSQ, #HSQq⟩, -⟩
    ihave #Hssc : swift.syncSendCtx γ γc γm rp x.N $$ []
    · iunfold swift.syncSendCtx
      iexists me
      isplitr
      · iunfold swift.sendCtxN
        iexists x.rr, s, x.γw, γs, csv
        iframe #
        ipureintro; exact Hcs
      iexists sqS, szS, memS
      iframe #
    have e : x.syncN.γdl = x.γdl := rfl
    have esn : x.syncN.sn x.N x.r = x.sn := rfl
    ihave Hep := swift.epStoppedXc_forget γ x rp _ $$ Hep
    wp_apply (wp_hs l1 x.N x.r x.k ld v M0 bs hd w (sp.bal m.bal) M)
      $$ [Hdr Hst Hep Ft Frc FFQ Fpd Hpdm]
    · simp only [Hn.1, Bool.false_eq_true, ↓reduceIte, e, esn]
      iframe #
      iframe Hdr Hst Hep
      isplitl [Ft Frc FFQ Fpd Hpdm]
      · iunfold swift.syncFieldsOwn
        iexists t, rc, fq, pdm, PD
        iframe
      isplitr
      · ileft; ipureintro; exact hloc
      ipureintro
      exact ⟨by omega, by omega, by omega, fun _ => Hn.2.1⟩
    rw [e]
    iintro ⟨Hdr, Hpost⟩
    icases Hpost with (⟨%Hc, -, -, -⟩ | ⟨%v', %w', Hrun', Hds', Hsf, %Hw'⟩)
    · exfalso; rcases Hc with h | ⟨h1, h2⟩
      · omega
      · rw [Hn.1] at h2; cases h2
    iapply HΦ
    iunfold swift.syncFieldsOwnE at Hsf
    icases Hsf with ⟨%t', %rc', %fq', %pd', Ft, Fpd, Hpdm, Frc, FFQ⟩
    iunfold swift.descEpS at Hds'
    icases Hds' with ⟨Hds', -⟩
    iunfold swift.runInvP
    iexists true
    isplitl
    · simp only [swift.runInvR, ↓reduceIte]
      iunfold swift.runInv
      iframe Hd Hsc Hrl Hseq Hdr Hds'
      isplitl [Hrun' Fpd Hpdm]
      · iexists _, v', (some M), (sp.syncSeq M), [], w'
        iframe Hrun'
        isplitl [Fpd Hpdm]
        · iapply swift.propDepsOwn_empty rp pd'; iframe
        ipureintro; exact Hw'.2.2
      iunfold swift.runFields
      iexists t', fq', rc', nl, bsN, ppsl, pp
      iframe
      isplitr
      · ipureintro; exact Hpp
      ipureintro; exact Hnlr
    ipureintro; intro _; rfl

end arms

/-! ## `handleNewLeader` -/

section main
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [examples.swiftnet.Assumptions]

set_option goose.wp.extras true

/-- The channels' bags and the RPC codes (persistent), out of `runLoopCtx`. -/
theorem swift.runLoopCtx_codec (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) :
    swift.runLoopCtx rp γ γc γm x ⊢ encoding.gob.codecSet (GF := netDistGF) := by
  iintro H
  iunfold swift.runLoopCtx at H
  icases H with ⟨%s, %b, %γs, %sq, %hsl, %fr2, %pl, %sam, %csv, %n, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hc, -⟩
  iexact Hc

theorem swift.runLoopCtx_bags (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) :
    swift.runLoopCtx rp γ γc γm x ⊢ ∃ (csv : swift.CommunicationSupply) (n : swift.CsNames),
      swift.fld rp go!"cs" ↦□ csv ∗ ⌜swift.csCodes csv⌝ ∗ swift.csBags γ γc γm csv n := by
  iintro H
  iunfold swift.runLoopCtx at H
  icases H with ⟨%s, %b, %γs, %sq, %hsl, %fr2, %pl, %sam, %csv, %n, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, #Fcs, %Hcs, #Hbags, -⟩
  iexists csv, n
  iframe #
  ipureintro; exact Hcs

/-- **`handleNewLeader`** (see the file header). -/
theorem swift.Replica.handleNewLeader.wp_proofN (rp : Loc) (γ : sp.Names) (γc γm : GName)
    (x : swift.RunX)
    (wp_Now : time.Now.spec (GF := netDistGF) (hG := hG))
    (wp_fill : swift.Replica.fillNewLeaderAckN.specN (hG := hG) rp γ γc γm x)
    (wp_ackN : swift.Replica.handleNewLeaderAckN.specN (hG := hG) rp γ γc γm x)
    (wp_hs : swift.Replica.handleSync.specIR (hG := hG) (fun _ => swift.descDS γ γc γm x rp)
      (swift.descEpS γ γc γm x rp) (fun b => swift.descDF (x.DR γ b)) (swift.stopPS x) γ γc γm x.γl x.γw x.γv x.γd x.γe x.γo
      x.syncN rp x.rr (swift.descPC γ γc γm x rp))
    (wp_SendTo : replica.Sender.SendTo.spec (hG := hG))
    (hmarsh : swift.MNewLeaderAckN.marshalH (hG := hG)) :
    swift.Replica.handleNewLeader.specN (hG := hG) rp γ γc γm x := by
  intro l r b s
  iloeb as IH generalizing %l %r %b %s
  irevert IH
  iapply swift.nlHide_intro
  iintro #IH
  wp_start as ⟨HI, #Hl, #Hmok⟩
  ihave #Hl2 := Hl
  iStructNamedPrefix Hl2 "ML"
  ihave ⟨%ld, %v, %M0, %bs, %hd, %w, Hrun, Hop⟩ := (swift.runInvR_open rp γ γc γm x s).1 $$ HI
  iunfold swift.runOpen at Hop
  icases Hop with ⟨#Hd, #Hsc, Hrl, Hseq, Hdr, Hrf, Hpd, Hep, %Hn⟩
  iunfold swift.runSt at Hrun
  icases Hrun with ⟨Hbal, Hcb, Hstat, Hhd, Hhdl, Hhdc, Hpr, Hprs, Hk, Hks, Hhl, Hhls, Hpe,
    Hpes, Hls0, Hlso, Hw, #Hlb, %Hok2⟩
  obtain ⟨hvb0, hvc0, hw1, hw2, hst, hnc, -, -, -, -, -, -⟩ := Hok2.1
  -- the persistent context the later steps read
  ihave #Hd2 := Hd
  iunfold swift.descCtxE at Hd2
  icases Hd2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc0, %γrc, #HR, #HisR,
    %Hids, -, -, -, #Hspi, #Hcfg, #HnI, -, -, -, -, -, -, -, -, -, -, -, #Hng⟩
  obtain ⟨hme, hme0, hrN, hN1, hN7, hk⟩ := Hids
  -- D56 N1-b: the message's sender is a replica (`msgOk (.newLeader)`)
  ihave %Hsnd : ⌜0 ≤ r.toInt ∧ sp.rid r < x.N⌝ $$ []
  · iunfold sp.msgOk at Hmok
    icases Hmok with ⟨%N', %fr2, %l2, #Hcfg2, %Hr⟩
    ihave %Hag := sp.cfg_agree x.N N' fr fr2 lg l2 $$ [Hcfg Hcfg2]
    · iframe #
    obtain ⟨rfl, -, -⟩ := Hag
    ipureintro; exact Hr
  ihave #HisR2 := HisR
  iunfold replica.isReplica at HisR2
  icases HisR2 with ⟨%lg', %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, -, -, #HN, #Hid, -⟩
  ihave ⟨⟨%sS, %γs, %csv, #Fsnd, #Hsbag, #Fcs, %Hcs⟩, Hrl⟩ :=
    BI.persistent_entails_right (swift.runLoopCtx_send rp γ γc γm x) $$ Hrl
  ihave ⟨⟨%csv2, %n2, #Fcs2, %Hcs2, #Hbags⟩, Hrl⟩ :=
    BI.persistent_entails_right (swift.runLoopCtx_bags rp γ γc γm x) $$ Hrl
  ihave #Hsc2 := Hsc
  iunfold swift.syncCtx at Hsc2
  icases Hsc2 with ⟨%dmS, -, -, -, -, -, #HbaL, -⟩
  ihave #Fcs4 := Fcs
  iStructNamedPrefix Fcs4 "CSa"
  -- 1. `if r.ballot >= msg.Ballot { return }`
  wp_auto
  try ipersist r
  try ipersist msg
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    iunfold swift.runInvP
    iexists s
    isplitl
    · iapply (swift.runInvR_open rp γ γc γm x s).2
      iexists ld, v, M0, bs, hd, w
      isplitl [Hbal Hcb Hstat Hhd Hhdl Hhdc Hpr Hprs Hk Hks Hhl Hhls Hpe Hpes Hls0 Hlso Hw]
      · iunfold swift.runSt; iframe; iframe Hlb; ipureintro; exact Hok2
      iunfold swift.runOpen; iframe; iframe #; ipureintro; exact Hn
    ipureintro; exact id
  rename_i Hge
  -- 2. `log.Println("Recovering... with the ballot", msg.Ballot)`
  have tStr : ∀ x : GoString, swift.printable (interface.mkOk go.string #x) :=
    fun x => swift.printable_of_argsWf _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)
  have tI32 : ∀ x : w32, swift.printable (interface.mkOk go.int32 #x) :=
    fun x => swift.printable_of_argsWf _
      (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int32 x) fmt.ArgsWf.nil)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.InterfaceType [])))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType []) [_, _]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lsl1 ⟨Hlsl1, -⟩
  wp_auto
  wp_apply (swift.wp_PrintlnT _ _ _ (by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | ⟨⟩
    · exact tStr _
    · exact tI32 _)) $$ [$Hlsl1] as -
  try wp_auto
  -- 3. `if r.status == NORMAL { r.repchan.stop(); r.stopDescs() }`: the epoch stopped
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun vv => iprop(⌜vv = executeVal⌝ ∗ swift.epStoppedX γ x rp ∗
      swift.runFields γ rp x.rr x.N x.r ∗
      typedPointsto (swift.fld rp go!"status") v.status (DFrac.own (1 : Iris.Qp).half))))
    $$ [Hep Hrf Hstat]
  · try wp_auto
    wp_if_destruct
    · -- normal operation: stop the reply goroutine and the descriptors
      have hs : s = true := by
        cases hs' : s
        · exfalso; rw [(Hn.2 hs').2] at Hif; exact swift.stNORMAL_ne_REC Hif.symm
        · rfl
      subst hs
      simp only [↓reduceIte]
      iunfold swift.runFields at Hrf
      icases Hrf with ⟨%t, %fq, %rc, %nl, %bsN, %ppsl, %pp, Ft, FFQ, Frc, Fnl, Fbs, Hnl, FPP, Hpp,
        %Hpp, %Hnlr⟩
      try wp_auto
      wp_apply (swift.epR_stop_ofD swift.replyChan.stop.wp_proof γ γc γm x rp rc v.propsM)
        $$ [$Hep $Frc] as ⟨HepH, Frc⟩
      try wp_auto
      wp_apply (swift.Replica.stopDescs.wp_specI γ x rp v.propsM) $$ [$HepH] as Hstp
      try wp_auto
      iframe Hstp Hstat
      isplitr
      · ipureintro; rfl
      iunfold swift.runFields
      iexists t, fq, rc, nl, bsN, ppsl, pp
      iframe
      isplitr
      · ipureintro; exact Hpp
      ipureintro; exact Hnlr
    · -- in recovery: the epoch is stopped already
      have hs : s = false := by
        cases hs' : s
        · rfl
        · exfalso; exact Hif ((hst.1 (by rw [Hn.1, hs'])))
      subst hs
      simp only [Bool.false_eq_true, ↓reduceIte]
      ihave Hep := swift.epStoppedXc_forget γ x rp _ $$ Hep
      iframe
      try (ipureintro; rfl)
  iintro %vv ⟨%Hvv, Hep, Hrf, Hstat⟩
  subst Hvv
  wp_auto
  -- 4. `r.status = RECOVERING`; `r.ballot = msg.Ballot` under `ballotL`
  try iunfold swift.epStoppedX at Hep
  iunfold swift.epStopped at Hep
  icases Hep with ⟨%bw2, %st2, %stp, %stpX, %bc, Hb2, Hst2, HS, Hrc2, He, Hxp, Hxe, Hrm, Hdstp,
    Hout, Hhs, Hfz, Hfq⟩
  ihave ⟨%Hsteq, Hstat⟩ := typedPointsto_half_combine _ _ _ (1 : Iris.Qp) $$ [Hstat Hst2]
  · iframe
  wp_auto
  icases (typedPointsto_half_split _ _ (1 : Iris.Qp)).1 $$ Hstat with ⟨Hstat, Hst2⟩
  wp_apply sync.Mutex.wp_Lock $$ [$HbaL] as ⟨Hblk, HB⟩
  iunfold swift.ballotLInv at HB
  icases HB with ⟨%bq, HBq, -⟩
  ihave ⟨%Hbq, Hbal⟩ := typedPointsto_half_combine _ _ _ (1 : Iris.Qp).half $$ [HBq Hbal]
  · iframe
  ihave ⟨%Hbq2, Hbal⟩ := typedPointsto_half_combine _ _ _ (1 : Iris.Qp) $$ [Hbal Hb2]
  · iframe
  try wp_auto
  icases (typedPointsto_half_split _ _ (1 : Iris.Qp)).1 $$ Hbal with ⟨Hbal, Hb2⟩
  icases (typedPointsto_half_split _ _ (1 : Iris.Qp).half).1 $$ Hbal with ⟨Hbal, HBq⟩
  have hb0 : 0 ≤ sint.Z b := by omega
  wp_apply sync.Mutex.wp_Unlock $$ [$HbaL $Hblk HBq]
  · inext; iunfold swift.ballotLInv; iexists b; iframe; ipureintro; exact hb0
  try wp_auto
  -- the node state's new ballot (`newBallot_stepD`), the epoch token at the view's epoch
  have hwb : w.1 < sp.bal b := by
    rw [hw1]; unfold sp.bal; show (sint.Z v.ballot).toNat < (sint.Z b).toNat; omega
  iapply fupd_wp
  imod swift.nl_epoch_agree γ x.γv x.γe x.γo x.sn x.k w bc $$ [HnI Hw He] with ⟨Hw, He, %Hbc⟩
  · iframe Hw He; iexact HnI
  imodintro
  -- L2: at its resolution (`ghostNewBallot(msg.Ballot)`, `newBallot_stepD` in its update)
  ihave #Hcpk : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client
    $$ []
  · iPkgInit
  wp_bind (App (Val (@! swift.ghostNewBallot)) (Val _))
  iapply (swift.wp_ghostNewBallot γ x.k b
    iprop(ghostVar x.γv (1 : Iris.Qp).half (w.newBal (sp.bal b)) ∗
      swift.epochTok x.γe (1 : Iris.Qp).half (sp.bal b, w.2.1) ∗ swift.repTok x.sn.γrp (sp.bal b)))
    $$ [Hw He]
  · iframe Hpkg Hcpk Hng
    isplitr
    · ipureintro; exact hb0
    iunfold swift.ghostUpd
    iintro %W' Hpre
    imod swift.newBallot_stepD γ γc γm x.γl x.γv x.γe x.γo x.N x.r x.k fr lg w bc (sp.bal b)
      hrN hk hwb W' $$ [Hspi Hcfg HnI Hw He Hpre] with ⟨Hw, Hpost, He, Htk⟩
    · iframe #; iframe
    imodintro
    iframe Hpost Hw He Htk
  inext
  iintro ⟨Hw, He, Htk⟩
  try wp_auto
  subst Hbc
  -- 5. `r.recStart = time.Now()`
  iunfold swift.runFields at Hrf
  icases Hrf with ⟨%t, %fq, %rc, %nl, %bsN, %ppsl, %pp, Ft, FFQ, Frc, Fnl, Fbs, Hnl, FPP, Hpp,
    %Hpp, %Hnlr⟩
  ihave #Htm1 := swift.time_init $$ Hpkg
  wp_apply wp_Now $$ [$Htm1] as %tn Htn
  try wp_auto
  -- 6. the ack `&MNewLeaderAckN{r.Id, r.ballot, r.cballot}` and `fillNewLeaderAckN`
  try wp_auto
  try ipersist newLeaderAckN
  -- the run loop in recovery at `b` (`recInvB`): `runSt` at the new values, the stopped epoch at
  -- the new epoch token
  -- `ld` is `r` leading `cballot` (`localOk`, D56 N1-a), which `handleNewLeader` keeps: the hash
  -- logs are unchanged
  have hw21 : w.2.1 < sp.bal b := by
    have hwlt : w.1 < sp.bal b := by
      rw [hw1]; unfold sp.bal; show (sint.Z v.ballot).toNat < (sint.Z b).toNat; omega
    cases hs : w.2.2.1
    · have := (Hn.2 (by rw [← Hn.1, hs])).1; omega
    · have := hnc hs; omega
  obtain ⟨-, -, -, -, -, -, hMn, hloc, hprop, habove, hld, hnd, hpro⟩ := Hok2.1
  have hlok' : swift.localOk x.N x.r ld
      { v with ballot := b, status := swift.stRECOVERING } M0
      ((sp.bal b, w.2.1, false, w.2.2.2) : swift.LView) :=
    ⟨hb0, hvc0, rfl, hw2, ⟨(fun h => by cases h), (fun h => absurd h.symm swift.stNORMAL_ne_REC)⟩,
      (fun h => by cases h), hMn, hloc, hprop, habove, hld, hnd, hpro⟩
  rw [show w.newBal (sp.bal b) = ((sp.bal b, w.2.1, false, w.2.2.2) : swift.LView) from rfl]
  ihave HRB : swift.recInvB rp γ γc γm x b v.cballot $$ [Hrl Hseq Hdr Hpd Fnl Fbs Hnl FPP Hpp Ft
      FFQ Frc Hb2 Hst2 HS Hrc2 He Hxp Hxe Hrm Hdstp Hout Hhs Hfz Hfq Hbal Hcb Hstat Hhd Hhdl Hhdc
      Hpr Hprs Hk Hks Hhl Hhls Hpe Hpes Hls0 Hlso Hw]
  · iunfold swift.recInvB
    iframe Hd Hsc Hrl Hseq Hdr
    isplitl [Hbal Hcb Hstat Hhd Hhdl Hhdc Hpr Hprs Hk Hks Hhl Hhls Hpe Hpes Hls0 Hlso Hw Hpd]
    · iexists ld,
        { v with ballot := b, status := swift.stRECOVERING }, M0, bs, hd,
        ((sp.bal b, w.2.1, false, w.2.2.2) : swift.LView)
      iunfold swift.runSt
      iframe
      iframe Hlb
      ipureintro
      exact ⟨⟨hlok', Hok2.2.1, Hok2.2.2⟩, rfl, hw21, rfl, rfl, rfl⟩
    isplitl [Ft FFQ Frc Fnl Fbs Hnl FPP Hpp]
    · iunfold swift.runFields
      iexists tn, fq, rc, nl, bsN, ppsl, pp
      iframe
      isplitr
      · ipureintro; exact Hpp
      ipureintro; exact Hnlr
    iunfold swift.epStoppedXc
    iexists b, swift.stRECOVERING, stp, stpX, (sp.bal b, w.2.1)
    iframe
    ipureintro; exact hw2
  ihave Htk : swift.repTok x.γrp (sint.Z b).toNat $$ [Htk]
  · iapply (show (swift.repTok x.sn.γrp (sp.bal b) : IProp netDistGF) ⊢
      swift.repTok x.γrp (sint.Z b).toNat from .rfl)
    iexact Htk
  wp_apply (wp_fill «$r0_ptr» me b v.cballot) $$ [$HRB $«$r0» $Htk] as ⟨HRB, %R, #Hack, #HackB, #Hrep, %HRf⟩
  · ipureintro
    have h1 : sp.rid me = (sint.Z me).toNat := rfl
    show sint.Z me = (x.r : Int); rw [← hme, h1]; omega
  try wp_auto
  -- 7. `SendTo(msg.Replica, …)` or `handleNewLeaderAckN`
  have hRc : (⟨sp.bal v.cballot, R.entries⟩ : sp.Report) = R := by
    obtain ⟨c, es⟩ := R
    have h := HRf.1
    simp only [] at h
    rw [h]; rfl
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun vv => iprop(⌜vv = executeVal⌝ ∗
      ∃ s1 : Bool, swift.runInvR rp γ γc γm x s1))) $$ [HRB]
  · try wp_auto
    wp_if_destruct
    · -- its own recovery: its ack to its own set
      wp_apply (wp_ackN «$r0_ptr» (x.r, R) b) $$ [HRB] as HP
      · iframe #
        isplitl
        · iunfold swift.recInv; iexists b, v.cballot; iexact HRB
        ipureintro; exact ⟨hrN, hb0⟩
      try wp_auto
      isplitr
      · ipureintro; rfl
      iunfold swift.runInvP at HP
      icases HP with ⟨%s1, HI, -⟩
      iexists s1
      iexact HI
    · -- another replica's recovery: the ack to its sender
      try wp_auto
      rw [MethodUnfold.method_unfold (t := go.GoType.PointerType replica.Sender.ty)
        (m := go!"SendTo")]
      try wp_auto
      wp_apply (wp_SendTo x.rr γ γc γm x.γw x.N me γs sS r
          (interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #«$r0_ptr»)
          (.newLeaderAckN me b v.cballot R.entries) csv.newLeaderAckNRPC'
          iprop(swift.ackObj «$r0_ptr» (x.r, R)))
      · iframe #
        isplitl
        · unfold replica.toSend
          isplitr
          · have hme' : sint.Z me = ((x.r, R).1 : Int) := by
              have h1 : sp.rid me = (sint.Z me).toNat := rfl
              show sint.Z me = (x.r : Int); rw [← hme, h1]; omega
            have hcb' : sint.Z v.cballot = ((x.r, R).2.cbal : Int) := by
              show sint.Z v.cballot = (R.cbal : Int); rw [HRf.1]; omega
            ihave #Hbin : isPkgInit (PROP := IProp netDistGF) pkg_id.encoding.binary $$ []
            · iPkgInit
            iapply (hmarsh «$r0_ptr» (x.r, R) me b v.cballot HRf.2 hme' hcb') $$ Hbin Hack HackB
          isplitr
          · iexact Hack
          isplitr
          · simp only [sp.msgOk]
            isplitr
            · ipureintro; exact ⟨⟨hme0, hb0⟩, hvc0⟩
            rw [hme, hRc, show sp.bal b = (sint.Z b).toNat from rfl]
            isplitr
            · iexact Hrep
            -- D56 N1-b: the sender is this replica, `< N`
            iexists x.N, fr, lg
            iframe Hcfg
            ipureintro; first | exact hrN | (rw [hme]; exact hrN)
          isplitr
          · unfold replica.freeOk; ileft; ipureintro; rfl
          ipureintro
          exact ⟨HRf.2, by rw [Hcs.2.2.2.2.2.2.2.2.1]; rfl⟩
        ipureintro
        exact ⟨trivial,
          ⟨Hsnd.1, by have := Hsnd.2; unfold sp.rid at this; omega⟩
          ⟩
      try wp_auto
      isplitr
      · ipureintro; rfl
      iexists false
      simp only [swift.runInvR, Bool.false_eq_true, ↓reduceIte]
      iunfold swift.recInv
      iexists b, v.cballot
      iexact HRB
  iintro %vv ⟨%Hvv, ⟨%s1, HI⟩⟩
  subst Hvv
  wp_auto_lc 2
  -- 8. `for r.status == RECOVERING { select { … } }`
  ihave #Hbags3 := Hbags
  iunfold swift.csBags at Hbags3
  icases Hbags3 with ⟨-, -, -, -, -, -, -, #Bnl, #Bnla, #Bsync, -⟩
  ihave #Fcs3 := Fcs2
  iStructNamedPrefix Fcs3 "CS"
  ihave HL : (∃ sl : Bool, "HI" ∷ swift.runInvR rp γ γc γm x sl ∗ "Hlc1" ∷ £ 1 ∗
      "Hlc2" ∷ £ 1 : IProp netDistGF) $$ [HI Hlc1 Hlc2]
  · iexists s1; iframe
  clear s1
  wp_for_core
  icases HL with ⟨%sl, HI, Hlc1, Hlc2⟩
  try wp_auto
  ihave ⟨%st, Hstat, %Hst, Hclst⟩ := swift.runInvR_status rp γ γc γm x sl $$ HI
  wp_auto
  wp_if_destruct
  · -- recovering: the `select`
    have hs1 : sl = false := by
      cases h : sl
      · rfl
      · exfalso; rw [Hst.1 h] at Hif
        have h1 := of_decide_eq_true (go.intoVal_inj Hif)
        exact absurd h1 (by decide)
    subst hs1
    ihave HI := Hclst $$ Hstat
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `newLeaderChan`: the induction hypothesis
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Bnl
      inext
      iintro %v0 Hv
      iunfold sp.chanMsgP at Hv
      icases Hv with ⟨%m, Hr, #Hok, %Hc⟩
      cases m <;> simp [sp.Msg.code, sp.rpcTable] at Hc
      rename_i r0 b0
      iunfold swift.msgRep at Hr
      iunfold swift.msgRepM at Hr
      icases Hr with ⟨%l0, %Hv, Hl0⟩
      subst Hv
      irevert IH
      iapply swift.nlHide_elim
      iintro #IH
      wp_auto_lc 2
      ipersist Hl0
      rw [MethodUnfold.method_unfold (t := go.GoType.PointerType swift.Replica.ty)
        (m := go!"handleNewLeader")]
      wp_apply IH $$ %l0 %r0 %b0 %false [HI Hl0] as HP
      · iframe #; iframe
      iunfold swift.runInvP at HP
      icases HP with ⟨%s2, HI, -⟩
      wp_for_post
      iframe
      iexists s2
      unfold named
      iframe
      try (iunfold swift.runInvR at HI; iexact HI)
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `newLeaderAckNChan`
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Bnla
      inext
      iintro %v0 Hv
      iunfold sp.chanMsgP at Hv
      icases Hv with ⟨%m, Hr, #Hok, %Hc⟩
      cases m <;> simp [sp.Msg.code, sp.rpcTable] at Hc
      rename_i rep0 bl0 cb0 es0
      iunfold swift.msgRep at Hr
      iunfold swift.msgRepM at Hr
      icases Hr with ⟨%l0, %ids, %ph, %cm, %dp, %cmL, %dpL, %Hv, Hr⟩
      subst Hv
      wp_auto_lc 2
      simp only [swift.runInvR, Bool.false_eq_true, ↓reduceIte]
      wp_apply (swift.recArm_ackN rp γ γc γm x wp_ackN l0 rep0 bl0 cb0 es0) $$ [HI Hr] as HP
      · iframe #
        iframe HI
        iunfold swift.msgRepM
        iexists l0, ids, ph, cm, dp, cmL, dpL
        iframe
        ipureintro; rfl
      iunfold swift.runInvP at HP
      icases HP with ⟨%s2, HI, -⟩
      wp_for_post
      iframe
      iexists s2
      unfold named
      iframe
      try (iunfold swift.runInvR at HI; iexact HI)
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `syncChan`
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Bsync
      inext
      iintro %v0 Hv
      iunfold sp.chanMsgP at Hv
      icases Hv with ⟨%m, Hr, #Hok, %Hc⟩
      cases m <;> simp [sp.Msg.code, sp.rpcTable] at Hc
      rename_i m0
      iunfold swift.msgRep at Hr
      iunfold swift.msgRepM at Hr
      icases Hr with ⟨%l0, %x0, %Hv, Hl⟩
      obtain ⟨Hv, Hx⟩ := Hv
      subst Hv
      wp_auto_lc 2
      simp only [swift.runInvR, Bool.false_eq_true, ↓reduceIte]
      wp_apply (swift.recArm_sync rp γ γc γm x wp_hs l0 m0) $$ [HI Hl] as HP
      · iframe #
        iframe HI
        iunfold swift.msgRepM
        iexists l0, x0
        iframe
        ipureintro; exact ⟨rfl, Hx⟩
      iunfold swift.runInvP at HP
      icases HP with ⟨%s2, HI, -⟩
      wp_for_post
      iframe
      iexists s2
      unfold named
      iframe
      try (iunfold swift.runInvR at HI; iexact HI)
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- normal: the loop ends
    have hs1 : sl = true := by
      cases h : sl
      · exfalso; rw [Hst.2 h] at Hif; exact Hif rfl
      · rfl
    subst hs1
    have hst' : st = swift.stNORMAL := Hst.1 rfl
    subst hst'
    ihave HI := Hclst $$ Hstat
    try rw [if_neg (by decide)]
    try wp_auto
    iapply HΦ
    iunfold swift.runInvP
    iexists true
    iframe
    ipureintro; intro _; rfl

end main

section ackdefs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- The run loop's own fields besides `newLeaderAckNs`'s (`runFields` without the set): what
`handleNewLeaderAckN` lends to the set's handler with the rest of the state. -/
def swift.runFieldsNL (rp rr : Loc) (N : Nat) : IProp netDistGF :=
  iprop(∃ (t : time.Time) (fq : replica.QuorumI) (rc : Loc) (ppsl : GoSlice) (pp : List w32),
    swift.fld rp go!"recStart" ↦ t ∗
    typedPointsto (swift.fld rp go!"FQ") fq (DFrac.own (1 : Iris.Qp).half.half) ∗
    typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Iris.Qp).half) ∗
    replica.fld rr go!"PreferredPeerOrder" ↦ ppsl ∗ ppsl ↦* pp ∗
    ⌜pp.length = N ∧ ∀ p ∈ pp, 0 ≤ p.toInt ∧ p.toInt < N⌝)

/-- What the set's handler is lent (`R` of `MsgSet.Add.specQ`): the recovering state at the
set's ballot `bl`, without the set's fields. -/
def swift.ackR (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (bl : w32) :
    IProp netDistGF :=
  iprop(swift.descCtxE γ γc γm x.γl x.γw x.γv x.γe x.γo x.γx x.γxe x.γxm x.γxp x.γxu x.γrp x.γcg x.γout x.γcl x.γdc x.γdl
      x.str rp x.rr x.N x.r x.k ∗
    swift.syncCtx γ x.N x.r x.syncN rp ∗ swift.runLoopCtx rp γ γc γm x ∗
    (∃ (ld : Bool) (v : swift.RunV) (M : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView),
      swift.runSt γ x.γv rp x.N x.r ld v M bs hd w ∗ swift.propDepsOwn rp (bs ++ hd) ∗
      ⌜w.2.2.1 = false ∧ w.2.1 < w.1 ∧ v.ballot = bl ∧ v.status = swift.stRECOVERING⌝ ∗
      swift.epStoppedXc γ x rp (sint.Z v.cballot).toNat) ∗
    swift.seqOwn γ rp x.k ∗ swift.runReader rp x.γdl ∗
    swift.runFieldsNL rp x.rr x.N ∗
    -- D56 N1-c: `r` leads the set's ballot (`runFields`)
    ⌜sp.leaderOf x.N (sp.bal bl) = x.r⌝)

/-- What the handler leaves (`Rdone`): the normal state without the set's fields, and the set's
data back. -/
def swift.ackDone (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (nl : Loc)
    (bs : w32) : IProp netDistGF :=
  iprop(swift.descCtxE γ γc γm x.γl x.γw x.γv x.γe x.γo x.γx x.γxe x.γxm x.γxp x.γxu x.γrp x.γcg x.γout x.γcl x.γdc x.γdl
      x.str rp x.rr x.N x.r x.k ∗
    swift.syncCtx γ x.N x.r x.syncN rp ∗ swift.runLoopCtx rp γ γc γm x ∗
    (∃ (ld : Bool) (v : swift.RunV) (M : Option sp.SyncMsg) (bs' hd : sp.Seq) (w : swift.LView),
      swift.runSt γ x.γv rp x.N x.r ld v M bs' hd w ∗ swift.propDepsOwn rp (bs' ++ hd) ∗
      ⌜w.2.2.1 = true⌝) ∗
    swift.seqOwn γ rp x.k ∗ swift.runReader rp x.γdl ∗
    swift.runFieldsNL rp x.rr x.N ∗ swift.descDS γ γc γm x rp ∗
    replica.mset.ownD nl (swift.nlQ x.N) (x.N / 2 + 1) (fun _ => True) (swift.nlP γ x.N bs)
      (fun _ _ => iprop(True)) (fun _ => iprop(False)) iprop(True) (swift.nlHd rp))


end ackdefs

section handler
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [examples.swiftnet.Assumptions]

/-- The quorum's acks (`handlerPreQ`'s `nlP`, round N3) as `handleNewLeaderAckNs`' reports: the
acks `prs` (each its object and its report at `bs`), in the order of the messages. -/
theorem swift.nl_collect (γ : sp.Names) (N : Nat) (bs : w32)
    (Q : w32 → GoInterface → IProp netDistGF) :
    ∀ kms : List (w32 × GoInterface),
    (□ ∀ k m, ⌜(k, m) ∈ kms⌝ → swift.nlP γ N bs k m ∗ Q k m) ⊢
      ∃ prs : List (Loc × (Nat × sp.Report)),
        ⌜kms.map Prod.snd =
            prs.map (fun q => interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #q.1) ∧
          (prs.map Prod.snd).map Prod.fst = kms.map (fun km => (sint.Z km.1).toNat) ∧
          (∀ q ∈ prs, q.2.1 < N) ∧ ∀ km ∈ kms, 0 ≤ sint.Z km.1⌝ ∗
        ([∗list] q ∈ prs, swift.ackObj q.1 q.2) ∗
        [∗list] p ∈ prs.map Prod.snd, sp.reported γ p.1 (sint.Z bs).toNat p.2
  | [] => by
    iintro -
    iexists []
    simp only [List.map_nil]
    isplitr
    · ipureintro; simp
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    · iapply BigSepL.bigSepL_nil.2; itrivial
  | (k, m) :: kms => by
    iintro #H
    ihave ⟨Hp1, -⟩ := H $$ %k %m %(List.mem_cons_self)
    iunfold swift.nlP at Hp1
    icases Hp1 with ⟨%p, %a, %Hpa, #Hobj, -, #Hrep⟩
    ihave #Hrest : □ ∀ k' m', ⌜(k', m') ∈ kms⌝ → swift.nlP γ N bs k' m' ∗ Q k' m' $$ []
    · imodintro
      iintro %k' %m' %h
      iapply H
      ipureintro; exact List.mem_cons_of_mem _ h
    ihave ⟨%prs, %Hprs, #Hobjs, #Hreps⟩ := swift.nl_collect γ N bs Q kms $$ Hrest
    obtain ⟨hm, hk, hN, -⟩ := Hpa
    iexists (p, a) :: prs
    isplitr
    · ipureintro
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, hm, Hprs.1]
      · simp only [List.map_cons, Hprs.2.1, hk]; simp
      · intro q hq
        rcases List.mem_cons.mp hq with e | e
        · subst e; exact hN
        · exact Hprs.2.2.1 q e
      · intro km hkm
        rcases List.mem_cons.mp hkm with e | e
        · subst e; show 0 ≤ sint.Z k; rw [hk]; omega
        · exact Hprs.2.2.2 km e
    isplitl
    · iapply BigSepL.bigSepL_cons.2
      iframe Hobj Hobjs
    · simp only [List.map_cons]
      iapply BigSepL.bigSepL_cons.2
      iframe Hrep Hreps

/-- **The set's handler** (`handleNewLeaderAckNs` as `MsgSet.Add.specQ`'s `□ handlerOkQ`): lent
the recovering state at the set's ballot (`swift.ackR`), a majority's acks (`handlerPreQ`'s
`nlP`), it ends normal (`swift.ackDone`), by `handleNewLeaderAckNs.specI` (`wp_hnl`, at the
descriptors' state: `swift.Replica.wp_handleNewLeaderAckNsD`). Round N3: the new ballot `b'` has
no row in the view by `localOk`'s row clause (D65 (1)). -/
theorem swift.nlHandlerOk (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (nl : Loc)
    (bs : w32)
    (wp_hnl : swift.Replica.handleNewLeaderAckNs.specI (hG := hG) (fun _ => swift.descDS γ γc γm x rp)
      (swift.descEpS γ γc γm x rp) (fun b => swift.descDF (x.DR γ b)) (swift.stopPS x) γ γc γm x.γl x.γw x.γv x.γd x.γe x.γo
      x.syncN rp x.rr (swift.descPC γ γc γm x rp)) :
    isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢
    □ replica.mset.handlerOkQ nl (swift.nlQ x.N) (swift.nlHd rp) (x.N / 2 + 1) (fun _ => True)
      (swift.nlP γ x.N bs) (fun _ _ => iprop(True)) (fun _ => iprop(False)) iprop(True)
      (swift.ackR rp γ γc γm x bs) (swift.ackDone rp γ γc γm x nl bs) := by
  iintro #Hpkg
  imodintro
  unfold replica.mset.handlerOkQ
  iintro %lm %sl %msl
  imodintro
  iintro %Ψ ⟨HR, Hown, Hsl, #Hpre⟩ HΨ
  -- the quorum's acks
  iunfold replica.mset.handlerPreQ at Hpre
  icases Hpre with ⟨%kms, %Hkms, Hlm, #Hall⟩
  obtain ⟨hms, hnd, -, hsz⟩ := Hkms
  iunfold replica.mset.leaderOk at Hlm
  icases Hlm with (%Hlm | #Hf)
  rotate_left
  · iexfalso; iexact Hf
  have hsz' : x.N / 2 + 1 ≤ msl.length := by
    rcases hsz with h | ⟨h, -⟩
    · exact h
    · exact absurd Hlm h
  ihave ⟨%prs, %Hprs, #Hobjs, #Hreps⟩ := swift.nl_collect γ x.N bs
    (fun _ m => replica.mset.accOk (fun _ _ => iprop(True)) lm m) kms $$ Hall
  obtain ⟨hmk, hfst, hlt, hnn⟩ := Hprs
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  -- the lent state
  iunfold swift.ackR at HR
  icases HR with ⟨#Hd, #Hsc, Hrl, ⟨%ld, %v, %M0, %bs0, %hd, %w, Hrun, Hpd, %Hn, Hep⟩, Hseq, Hdr, Hrf,
    %Hlead⟩
  ihave Hep := swift.epStoppedXc_forget γ x rp _ $$ Hep
  obtain ⟨hnorm, hcw, hvb, hvs⟩ := Hn
  ihave ⟨%Hlok, Hrun⟩ := BI.persistent_entails_right
    (swift.runSt_localOk γ x.γv rp x.N x.r ld v M0 bs0 hd w) $$ Hrun
  have hw1 : w.1 = sp.bal bs := by rw [Hlok.2.2.1, hvb]
  have hrow : ∀ o, (w.1, o) ∉ w.2.2.2 := fun o => Hlok.2.2.2.2.2.2.2.2.2.1 _ o hcw
  ihave #Hctx : swift.runCtxD γ γc γm x.γl x.γw x.γv x.γe x.γo x.sn x.γdl rp x.N x.r x.k $$ [Hrl]
  · ihave #Hd3 := Hd
    iunfold swift.descCtxE at Hd3
    icases Hd3 with ⟨%me, %fr, %l, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #HR, #HisR, %Hids,
      -, -, -, #Hinv, #Hcfg, #HnI, #Hdel, #HdV, #HdI, -, -, -, -, -, -, -, -, #Hng⟩
    iunfold swift.runLoopCtx at Hrl
    icases Hrl with ⟨%s, %b, %γs, %sq, %hsl, %fr', %pl, %sam, %csv, %n, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, #HcntL, -, -, -⟩
    iunfold swift.runCtxD
    iexists x.rr, me, fr, l, dm
    iframe HR HisR Hinv Hcfg HnI Hdel HdV
    isplitr
    · ipureintro; exact Hids
    isplitr
    · iexists x.γx, x.γxp, x.γxm, γa, x.γxe, γrm, x.str; iexact HdI
    iframe Hng
    iexists x.dm, x.γn, x.d
    iexact HcntL
  ihave #Hd2 := Hd
  iunfold swift.descCtxE at Hd2
  icases Hd2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc0, %γrc, #HR, #HisR,
    %Hids, -, -, -, #Hspi, -, #HnI, -, -, -, -, -, -, -, -, -, -, -⟩
  ihave #HisR2 := HisR
  iunfold replica.isReplica at HisR2
  icases HisR2 with ⟨%lg2, %cfgp, %tbl, %pc, %fr2, %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
    %cwm, -, -, #HfN, #HfId, -⟩
  iunfold swift.runFieldsNL at Hrf
  icases Hrf with ⟨%t, %fq, %rc, %ppsl, %pp, Ft, FFQ, Frc, FPP, Hpp, %Hpp⟩
  iunfold swift.propDepsOwn at Hpd
  icases Hpd with ⟨%pdm, %PD, Fpd, Hpdm, -⟩
  ihave Hst := swift.runSt_runStS γ x.γv rp x.N x.r ld v M0 bs0 hd w w.1 $$ Hrun
  ihave ⟨⟨%s, %γs, %csv, #Fsnd, #Hsbag, #Fcs, %Hcs⟩, Hrl⟩ :=
    BI.persistent_entails_right (swift.runLoopCtx_send rp γ γc γm x) $$ Hrl
  ihave ⟨#HPCw, Hrl⟩ := BI.persistent_entails_right (swift.descPC_of rp γ γc γm x x.N x.r) $$ Hrl
  ihave #HPC := HPCw $$ Hsc [Hd]
  · unfold swift.DC.ctx; iexact Hd
  ihave ⟨#Hcset, Hrl⟩ := BI.persistent_entails_right (swift.runLoopCtx_codec rp γ γc γm x) $$ Hrl
  ihave #Hsc2 := Hsc
  iunfold swift.syncCtx at Hsc2
  icases Hsc2 with ⟨%dm2, -, -, -, -, -, -, -, -, -, ⟨%qs, #Hqs, #HQS⟩, -, -, -, -, -, -, -,
    ⟨%sqS, %szS, %memS, #FSQ, #HSQq⟩, -⟩
  ihave #Hsend : swift.sendCtxN γ γc γm rp x.N me $$ []
  · iunfold swift.sendCtxN
    iexists x.rr, s, x.γw, γs, csv
    iframe #
    ipureintro; exact Hcs
  ihave #Hssc : swift.syncSendCtx γ γc γm rp x.N $$ []
  · iunfold swift.syncSendCtx
    iexists me
    iframe Hsend
    iexists sqS, szS, memS
    iframe #
  ihave #Hslp : isPkgInit (PROP := IProp netDistGF) pkg_id.slices $$ []
  · iPkgInit
  have e : x.syncN.γdl = x.γdl := rfl
  have esn : x.syncN.sn x.N x.r = x.sn := rfl
  -- the reports form a majority
  have hmaj : sp.isMajority x.N ((prs.map Prod.snd).map Prod.fst) := by
    rw [hfst]
    refine ⟨?_, ?_, ?_⟩
    · rw [show kms.map (fun km => (sint.Z km.1).toNat) =
          (kms.map Prod.fst).map (fun k : w32 => (sint.Z k).toNat) by rw [List.map_map]; rfl]
      refine swift.nodup_map_on _ _ (fun a ha b hb hab => ?_) hnd
      obtain ⟨ka, hka, rfl⟩ := List.mem_map.mp ha
      obtain ⟨kb, hkb, rfl⟩ := List.mem_map.mp hb
      have h1 := hnn ka hka
      have h2 := hnn kb hkb
      have hab' : (sint.Z ka.1).toNat = (sint.Z kb.1).toNat := hab
      have h3 : sint.Z ka.1 = sint.Z kb.1 := by omega
      exact BitVec.eq_of_toInt_eq h3
    · intro r hr
      rw [← hfst] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      exact hlt q hq
    · have : msl.length = kms.length := by rw [hms]; simp
      simp only [List.length_map]
      omega
  unfold swift.nlHd
  wp_apply (wp_hnl qs x.N x.r x.k me ld v M0 bs0 hd w lm sl msl (prs.map Prod.snd) w.1)
    $$ [Hdr Hst Hep Ft Frc FFQ Fpd Hpdm]
  · simp only [hnorm, Bool.false_eq_true, ↓reduceIte, e, esn]
    iframe #
    iframe Hdr Hst Hep
    isplitl [Ft Frc FFQ Fpd Hpdm]
    · iunfold swift.syncFieldsOwn
      iexists t, rc, fq, pdm, PD
      iframe
    isplitr
    · iunfold swift.acksIs
      iexists prs
      iframe Hobjs
      ipureintro; exact ⟨by rw [hms, hmk], rfl⟩
    isplitr
    · rw [hw1]; unfold sp.bal; iexact Hreps
    ipureintro
    refine ⟨hmaj, Hids.1, by rw [hw1]; exact Hlead, trivial, by omega, ?_, trivial, hrow, hcw,
      Hids.2.1⟩
    rw [hw1]; unfold sp.bal
    have := bs.toInt_lt; omega
  iintro ⟨Hdr, %v', %w', Hrun', Hds', Hsf, %Hw'⟩
  iapply HΨ
  iright
  iunfold swift.syncFieldsOwnE at Hsf
  icases Hsf with ⟨%t', %rc', %fq', %pd', Ft, Fpd, Hpdm, Frc, FFQ⟩
  iunfold swift.descEpS at Hds'
  icases Hds' with ⟨Hds', -⟩
  ihave Hdr2 : swift.runReader rp x.γdl $$ [Hdr]
  · rw [← e]; iexact Hdr
  iunfold swift.ackDone
  unfold swift.nlHd
  iframe Hd Hsc Hrl Hseq Hdr2 Hds' Hown
  isplitl [Hrun' Fpd Hpdm]
  · iexists _, v', _, _, [], w'
    iframe Hrun'
    isplitl [Fpd Hpdm]
    · iapply swift.propDepsOwn_empty rp pd'; iframe
    ipureintro; exact Hw'.2.2
  iunfold swift.runFieldsNL
  iexists t', fq', rc', ppsl, pp
  iframe
  ipureintro; exact Hpp

end handler

/-! ## The run loop's `newLeader` arm, and the callees not proved yet -/

section arm
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [examples.swiftnet.Assumptions]

/-- **The `newLeader` arm** (`RunArms.newLeader`): `handleNewLeader.specN` in normal operation
(`s = true`), whose post is then normal. -/
theorem swift.runArm_newLeader (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_hNL : swift.Replica.handleNewLeader.specN (hG := hG) rp γ γc γm x)
    (l : Loc) (r b : w32) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x ∗ typedPointsto l (swift.MNewLeader.mk r b) DFrac.discard ∗
        sp.msgOk γ γc γm (.newLeader r b) }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleNewLeader")) (Val #l))
    {{ RET #(); swift.runInv rp γ γc γm x }} := by
  iintro %Φ ⟨#Hpkg, HI, #Hl, #Hmok⟩ HΦ
  wp_apply (wp_hNL l r b true) $$ [HI] as HP
  · simp only [swift.runInvR, ↓reduceIte]
    iframe #
    iexact HI
  iapply HΦ
  iunfold swift.runInvP at HP
  icases HP with ⟨%s', HI, %Hs⟩
  have hs : s' = true := Hs rfl
  subst hs
  simp only [swift.runInvR, ↓reduceIte]
  iexact HI

-- `fillNewLeaderAckN.wp_proofN`: FillAckN.lean (round N4).

/-- **`handleNewLeaderAckN`** (recovery.go:67): the two guards, then `newLeaderAckNs.Add`
(`MsgSet.Add.specQ`) lending the set's handler the recovering state (`swift.ackR`). -/
theorem swift.Replica.handleNewLeaderAckN.wp_proofN (rp : Loc) (γ : sp.Names) (γc γm : GName)
    (x : swift.RunX) (wp_Add : replica.mset.MsgSet.Add.specQ (hG := hG))
    (wp_hnl : swift.Replica.handleNewLeaderAckNs.specI (hG := hG) (fun _ => swift.descDS γ γc γm x rp)
      (swift.descEpS γ γc γm x rp) (fun b => swift.descDF (x.DR γ b)) (swift.stopPS x) γ γc γm x.γl x.γw x.γv x.γd x.γe x.γo
      x.syncN rp x.rr (swift.descPC γ γc γm x rp)) :
    swift.Replica.handleNewLeaderAckN.specN (hG := hG) rp γ γc γm x := by
  intro p a bl
  wp_start as ⟨HI, #Hack, #HackB, #Hrep, %Ha⟩
  ihave #Hack2 := Hack
  iunfold swift.ackObj at Hack2
  icases Hack2 with ⟨%rep, %bl', %cb, %ids, %ph, %cm, %dp, %cmL, %dpL, #Hp, -, -, -, -, %Hpa, -⟩
  ihave #HackB2 := HackB
  iunfold swift.ackBal at HackB2
  icases HackB2 with ⟨%rep2, %cb2, %ids2, %ph2, %cm2, %dp2, #Hp2⟩
  icombine Hp Hp2 gives %Heq
  have hbl : bl = bl' := by injection Heq with _ h; exact h.symm
  subst hbl
  ihave #Hp3 := Hp
  iStructNamedPrefix Hp3 "AK"
  iunfold swift.recInv at HI
  icases HI with ⟨%bl0, %cb0, HI⟩
  iunfold swift.recInvB at HI
  icases HI with ⟨#Hd, #Hsc, Hrl, ⟨%ld, %v, %M0, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hep⟩
  iunfold swift.runSt at Hrun
  icases Hrun with ⟨Hbal, Hcb, Hstat, Hhd, Hhdl, Hhdc, Hpr, Hprs, Hk, Hks, Hhl, Hhls, Hpe,
    Hpes, Hls0, Hlso, Hw, #Hlb, %Hok2⟩
  iunfold swift.runFields at Hrf
  icases Hrf with ⟨%t, %fq, %rc, %nl, %bsN, %ppsl, %pp, Ft, FFQ, Frc, Fnl, Fbs, Hnl, FPP, Hpp,
    %Hpp, %Hnlr⟩
  wp_auto
  try ipersist r
  try ipersist msg
  -- `if r.status != RECOVERING || r.ballot != msg.Ballot { return }`
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun vv => iprop(
      typedPointsto (swift.fld rp go!"ballot") v.ballot (DFrac.own (1 : Iris.Qp).half.half) ∗
      typedPointsto (swift.fld rp go!"status") v.status (DFrac.own (1 : Iris.Qp).half) ∗
      ((⌜vv = executeVal⌝ ∗ ⌜v.ballot = bl⌝) ∨ ⌜vv = returnVal #()⌝)))) $$ [Hbal Hstat]
  · try wp_auto
    repeat wp_if_destruct
    all_goals iframe
    all_goals try (ileft; ipureintro; exact ⟨trivial, trivial⟩)
    all_goals (iright; itrivial)
  iintro %vv ⟨Hbal, Hstat, Hg⟩
  icases Hg with (⟨%Hvv, %Hblv⟩ | %Hvv) <;> subst Hvv
  rotate_left
  · -- `return`
    wp_auto
    iapply HΦ
    iunfold swift.runInvP
    iexists false
    isplitl
    · simp only [swift.runInvR, Bool.false_eq_true, ↓reduceIte]
      iunfold swift.recInv
      iexists bl0, cb0
      iunfold swift.recInvB
      iframe Hd Hsc Hrl Hseq Hdr Hep
      isplitl [Hbal Hcb Hstat Hhd Hhdl Hhdc Hpr Hprs Hk Hks Hhl Hhls Hpe Hpes Hls0 Hlso Hw Hpd]
      · iexists ld, v, M0, bs, hd, w
        iunfold swift.runSt
        iframe
        iframe Hlb
        ipureintro; exact ⟨Hok2, Hn⟩
      iunfold swift.runFields
      iexists t, fq, rc, nl, bsN, ppsl, pp
      iframe
      isplitr
      · ipureintro; exact Hpp
      ipureintro; exact Hnlr
    ipureintro; intro h; cases h
  -- `if r.newLeaderAckNs == nil || msg.Ballot != r.newLeaderAckNsBallot { return }`
  wp_auto
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun vv => iprop(
      swift.fld rp go!"newLeaderAckNs" ↦ nl ∗ swift.fld rp go!"newLeaderAckNsBallot" ↦ bsN ∗
      ((⌜vv = executeVal⌝ ∗ ⌜nl ≠ null ∧ bl = bsN⌝) ∨ ⌜vv = returnVal #()⌝)))) $$ [Fnl Fbs]
  · try wp_auto
    repeat wp_if_destruct
    all_goals try rw [← decide_not]
    all_goals try wp_if_destruct
    all_goals iframe
    all_goals try (ileft; ipureintro; exact ⟨rfl, by assumption, by assumption⟩)
    all_goals try (ileft; ipureintro; refine ⟨?_, ?_⟩ <;>
      first | trivial | assumption | exact Classical.not_not.mp ‹_› |
        (refine ⟨?_, ?_⟩ <;> first | assumption | exact Classical.not_not.mp ‹_›))
    all_goals try (ileft; ipureintro; exact ⟨rfl, by simp_all, by simp_all⟩)
    all_goals (iright; itrivial)
  iintro %vv2 ⟨Fnl, Fbs, Hg2⟩
  icases Hg2 with (⟨%Hvv, %Hnb⟩ | %Hvv) <;> subst Hvv
  rotate_left
  · wp_auto
    iapply HΦ
    iunfold swift.runInvP
    iexists false
    isplitl
    · simp only [swift.runInvR, Bool.false_eq_true, ↓reduceIte]
      iunfold swift.recInv
      iexists bl0, cb0
      iunfold swift.recInvB
      iframe Hd Hsc Hrl Hseq Hdr Hep
      isplitl [Hbal Hcb Hstat Hhd Hhdl Hhdc Hpr Hprs Hk Hks Hhl Hhls Hpe Hpes Hls0 Hlso Hw Hpd]
      · iexists ld, v, M0, bs, hd, w
        iunfold swift.runSt
        iframe
        iframe Hlb
        ipureintro; exact ⟨Hok2, Hn⟩
      iunfold swift.runFields
      iexists t, fq, rc, nl, bsN, ppsl, pp
      iframe
      isplitr
      · ipureintro; exact Hpp
      ipureintro; exact Hnlr
    ipureintro; intro h; cases h
  obtain ⟨hnl, hbs⟩ := Hnb
  subst hbs
  iunfold swift.nlSet at Hnl
  icases Hnl with (%Hnull | Hown)
  · exact absurd Hnull hnl
  have hlead : sp.leaderOf x.N (sp.bal bl) = x.r := Hnlr hnl
  -- `r.newLeaderAckNs.Add(msg.Replica, false, msg)`, lending `ackR` to the handler
  ihave #Hpkgs : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift $$ []
  · iPkgInit
  ihave #HhOk := swift.nlHandlerOk rp γ γc γm x nl bl wp_hnl $$ Hpkgs
  ihave #Hrpkg : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica $$ []
  · iPkgInit
  ihave HR : swift.ackR rp γ γc γm x bl $$ [Hrl Hseq Hdr Hpd Hep Hbal Hcb Hstat Hhd Hhdl Hhdc Hpr
      Hprs Hk Hks Hhl Hhls Hpe Hpes Hls0 Hlso Hw Ft FFQ Frc FPP Hpp]
  · iunfold swift.ackR
    iframe Hd Hsc Hrl Hseq Hdr
    isplitl [Hbal Hcb Hstat Hhd Hhdl Hhdc Hpr Hprs Hk Hks Hhl Hhls Hpe Hpes Hls0 Hlso Hw Hpd Hep]
    · have hcb := Hn.2.2.2.1
      subst hcb
      iexists ld, v, M0, bs, hd, w
      iframe Hep
      iunfold swift.runSt
      iframe
      iframe Hlb
      ipureintro; exact ⟨Hok2, Hn.1, Hn.2.1, Hblv, Hn.2.2.2.2⟩
    isplitl [Ft FFQ Frc FPP Hpp]
    · iunfold swift.runFieldsNL
      iexists t, fq, rc, ppsl, pp
      iframe
      ipureintro; exact Hpp
    ipureintro; exact hlead
  try wp_auto
  wp_apply (wp_Add nl (swift.nlQ x.N) (x.N / 2 + 1) (fun _ => True) (swift.nlP γ x.N bl)
      (fun _ _ => iprop(True)) (fun _ => iprop(False)) iprop(True) (swift.ackR rp γ γc γm x bl)
      (swift.ackDone rp γ γc γm x nl bl) (swift.nlHd rp) _ false _) $$ [Hown HR]
    as %added ⟨%Hmem, Hpost⟩
  · try iframe Hrpkg
    iframe HhOk
    isplitl [Hown]
    · iexact Hown
    isplitl [HR]
    · iexact HR
    isplitr
    · imodintro; iintro HR; isplitr
      · itrivial
      iintro -; iexact HR
    simp only [Bool.false_eq_true, ↓reduceIte]
    imodintro
    iunfold swift.nlP
    iexists p, a
    iframe Hack HackB Hrep
    ipureintro
    exact ⟨rfl, Hpa.1.trans rfl, Ha.1, Ha.2⟩
  try wp_auto
  iapply HΦ
  icases Hpost with (⟨Hown, HR⟩ | HD)
  · -- the handler did not run (or gave the state back): still recovering
    iunfold swift.ackR at HR
    icases HR with ⟨#Hd', #Hsc', Hrl', ⟨%ld', %v', %M', %bs', %hd', %w', Hrun', Hpd', %Hn', Hep'⟩, Hseq',
      Hdr', HNL, -⟩
    iunfold swift.runFieldsNL at HNL
    icases HNL with ⟨%t', %fq', %rc', %ppsl', %pp', Ft', FFQ', Frc', FPP', Hpp', %Hpp'⟩
    iunfold swift.runInvP
    iexists false
    isplitl
    · simp only [swift.runInvR, Bool.false_eq_true, ↓reduceIte]
      iunfold swift.recInv
      iexists bl, v'.cballot
      iunfold swift.recInvB
      iframe Hd' Hsc' Hrl' Hseq' Hdr' Hep'
      isplitl [Hrun' Hpd']
      · iexists ld', v', M', bs', hd', w'
        iframe Hrun' Hpd'
        ipureintro; exact ⟨Hn'.1, Hn'.2.1, Hn'.2.2.1, rfl, Hn'.2.2.2⟩
      iunfold swift.runFields
      iexists t', fq', rc', nl, bl, ppsl', pp'
      iframe
      isplitl [Hown]
      · iunfold swift.nlSet; iright; iexact Hown
      isplitr
      · ipureintro; exact Hpp'
      ipureintro; intro _; exact hlead
    ipureintro; intro h; cases h
  · -- the handler ran: normal at the set's ballot
    iunfold swift.ackDone at HD
    icases HD with ⟨#Hd', #Hsc', Hrl', Hrun', Hseq', Hdr', HNL, Hds', Hown⟩
    iunfold swift.runFieldsNL at HNL
    icases HNL with ⟨%t', %fq', %rc', %ppsl', %pp', Ft', FFQ', Frc', FPP', Hpp', %Hpp'⟩
    iunfold swift.runInvP
    iexists true
    isplitl
    · simp only [swift.runInvR, ↓reduceIte]
      iunfold swift.runInv
      iframe Hd' Hsc' Hrl' Hrun' Hseq' Hdr' Hds'
      iunfold swift.runFields
      iexists t', fq', rc', nl, bl, ppsl', pp'
      iframe
      isplitl [Hown]
      · iunfold swift.nlSet; iright; iexact Hown
      isplitr
      · ipureintro; exact Hpp'
      ipureintro; intro _; exact hlead
    ipureintro; intro _; rfl

/-- `(*MNewLeaderAckN).Marshal`. -/
theorem swift.MNewLeaderAckN.marshal_proof : swift.MNewLeaderAckN.marshalH (hG := hG) :=
  swift.MNewLeaderAckN.marshal_proofP swift.PutVarint.wp_proof

end arm

end Perennial.github_com.imdea_software.swiftpaxos

end
