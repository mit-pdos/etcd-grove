/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/FastAckDefs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**FastAckDefs** (round 43, D52 (4): FastAck.lean split by phase): `ackCtx` and the lemmas of the
proof of `r.fastAckFromLeader(msg, desc)` (the chains, `leader_cond`, `fastAck_call`); FastAck.lean
holds the proof itself and its macros.

The proof of `r.fastAckFromLeader(msg, desc)` (spec: Proof/swift/AcksSpecs.lean; round 10,
notes/prove-swift.md §16): `desc.afterPropagate.Call(closure)` with the condition's state
`proposeHalf`; the closure's spec (`closureOk`), and at the leader with a false condition its
no-op spec (the ack is of an earlier ballot: its witness of the current ballot would make the
row pre-accepted, `swift.preacc_row`, hence `propose ≠ nil`, `rowAcc`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcksCommon
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcceptL
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FastAckLemmas
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FastAckCallees
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Batcher
import all Spec.swift.Inv

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256


section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- The replica's fields a leader ack's closure reads besides `descCtx`'s (persistent; round
10): the slow quorum `SQ`, the batcher, the sender and the codes. -/
def swift.ackCtx (c : swift.DC) : IProp netDistGF :=
  iprop(∃ (sq : GoInterface) (szS : Nat) (memS : w32 → Prop) (bt s : Loc) (γs : ChanNames)
      (csv : swift.CommunicationSupply),
    -- round 54 (D74 (3), 53-1): `SQ` has every replica (so a follower's `sendSlowAck` holds)
    swift.fld c.rp go!"SQ" ↦□ sq ∗ replica.mset.quorumIs sq szS memS ∗ ⌜∀ k, memS k⌝ ∗
    swift.fld c.rp go!"batcher" ↦□ bt ∗ swift.batcherH c.γ c.γc c.γm c.rp bt ∗
    swift.fld c.rp go!"sender" ↦□ s ∗ isChanBag γs s (replica.sendArgP c.rr c.γ c.γc c.γm c.N) ∗
    swift.fld c.rp go!"cs" ↦□ csv ∗ ⌜swift.csCodes csv⌝ ∗
    -- round 44: the pool switch, for `handleLightSlowAck`'s `newFastAck` (`newFastAck.specP`)
    ∃ v : Bool, globalAddr swift.useFastAckPool ↦□ v)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
instance swift.ackCtx_persistent (c : swift.DC) : Persistent (swift.ackCtx c) := by
  unfold swift.ackCtx; infer_instance

/-- The pool switch out of `ackCtx` (round 44). -/
theorem swift.ackCtx_ufp (c : swift.DC) :
    swift.ackCtx c ⊢ ∃ v : Bool, globalAddr swift.useFastAckPool ↦□ v := by
  iintro H
  iunfold swift.ackCtx at H
  icases H with ⟨%sq, %szS, %memS, %bt, %s, %γs, %csv, -, -, %-, -, -, -, -, -, %-, #Hv⟩
  iexact Hv

end defs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [sync.Assumptions] [hook.Assumptions]
  [github_com.orcaman.concurrent_map.Assumptions]

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] [sync.Assumptions]
  [hook.Assumptions] [github_com.orcaman.concurrent_map.Assumptions] in
/-- A listed quorum (`replica.Quorum`, ids below `2^31`) does not have every replica. -/
theorem swift.qAll_noList (s : List Nat) (mem : w32 → Prop) (hm : ∀ k, mem k)
    (hlt : ∀ x ∈ s, x < 2 ^ 31) (h : ∀ k, mem k ↔ k ∈ s.map replica.quorum.w32n) : False := by
  have := (h (W32 (2 ^ 31 : Int))).1 (hm _)
  obtain ⟨x, hx, he⟩ := List.mem_map.mp this
  have hx2 := hlt x hx
  unfold replica.quorum.w32n at he
  have h2 := congrArg BitVec.toNat he
  simp at h2
  omega

/-- **`q.Contains(r)` for a quorum with every replica** (round 54, D74 (3), 53-1): `true`
(`SQ = NewMajorityOf(N)`: `Majority.Contains`). -/
theorem swift.wp_qContains_all (i : GoInterfaceOk) (sz : Nat) (mem : w32 → Prop) (r : w32)
    (hm : ∀ k, mem k) :
  {{ replica.mset.quorumIs (GoInterface.ok i) sz mem }}
    (App (Val #(methods i.ty go!"Contains" i.v)) (Val #r))
  {{ RET #true; True }} := by
  unfold replica.mset.quorumIs
  iintro %Φ ⟨%Hsz, Hq⟩ HΦ
  icases Hq with (⟨%Hq, -⟩ | ⟨%ql, %s, ⟨%Hq, %Hs, %Hnd, %Hlt, %Hm⟩, -⟩)
  · rcases Hq with h | h <;> cases h
    · wp_apply replica.Majority.Contains.wp_proof
      iapply HΦ; itrivial
    · wp_apply replica.ThreeQuarters.Contains.wp_proof
      iapply HΦ; itrivial
  · exact (swift.qAll_noList s mem hm Hlt Hm).elim

/-- `shOwnR`'s `status`, `FQ`, reader and pin (round 43, table §3R11b) out, and back (round 33). -/
theorem swift.shOwnR_openR (c : swift.DC) (d : Loc) (b : Nat) (q : Qp) :
    swift.shOwnR c d b q ⊢
      ∃ (st : w64) (fq : GoInterface) (szF : Nat) (memF : w32 → Prop),
        typedPointsto (swift.fld c.rp go!"status") st (DFrac.own q) ∗
        typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own q) ∗
        replica.mset.quorumIs fq szF memF ∗ ⌜∀ i : w32, memF i → sp.rid i ∈ sp.AQ c.N b⌝ ∗
        swift.ownRdr c.rp c.γdl ∗ swift.epochPinQ c.γxp q b ∗
        (typedPointsto (swift.fld c.rp go!"status") st (DFrac.own q) -∗
          typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own q) -∗ swift.ownRdr c.rp c.γdl -∗
          swift.epochPinQ c.γxp q b -∗ swift.shOwnR c d b q) := by
  iintro HR
  iunfold swift.shOwnR at HR
  icases HR with ⟨⟨%st, Hst⟩, ⟨%fq, %szF, %memF, HFQ, #HqF, %HAQ⟩, Hrd, Henv, Hpin⟩
  iexists st, fq, szF, memF
  iunfold swift.epochPinQ
  iframe Hst HFQ HqF Hrd Hpin
  isplitr
  · ipureintro; exact HAQ.1
  iintro Hst HFQ Hrd Hpin
  iunfold swift.shOwnR
  iframe Hrd Henv Hpin
  isplitl [Hst]
  · iexists st; iexact Hst
  iexists fq, szF, memF
  iframe HFQ HqF
  ipureintro; exact HAQ

/-- `rowPhaseOk` at `ACCEPT` with the row accepted (:615; PF13c: whatever the phase before). -/
theorem swift.rowPhaseOk_acc (N r b : Nat) (dv : swift.DescV) (rv : swift.RowV)
    (hp : dv.propose ≠ null) (h2 : dv.phase = W64 2) (ha : rv.2.2.1 = true) :
    swift.rowPhaseOk N r b dv rv := by
  unfold swift.rowPhaseOk
  refine ⟨fun h => absurd h hp, fun _ => ⟨by rw [h2]; decide, fun h0 => absurd (h2.symm.trans h0) (by decide),
    fun h1 => absurd (h2.symm.trans h1) (by decide), fun _ => ha, fun _ => by rw [h2]; decide,
    fun _ => Or.inl (by rw [h2]; decide)⟩⟩

/-- `depWhy` at a follower that accepted with the leader's dependencies (round 53, 52-1: the
leader's ack's `sp.locDeps`, `leadWit`'s `fastAckOk`). -/
theorem swift.depWhy_foll (γ : sp.Names) (γxm : GName) (N r b : Nat) (x : swift.CommandId)
    (dv : swift.DescV) (D : List sp.CmdId) (h : r ≠ sp.leaderOf N b)
    (hD : (dv.D.map toCmdId).Perm D) :
    sp.locDeps γ (sp.leaderOf N b) b (toCmdId x) D ⊢ swift.depWhy γ γxm N r b x dv := by
  iintro #Hld
  iunfold swift.depWhy; iright; iright; iright
  isplitr
  · ipureintro; exact h
  iexists D; iframe Hld; ipureintro; exact hD

/-- **53-3' (round 55, D77 (1)).** `fastAckFromLeader` at a follower, `sendSlowAck` with different
dependencies, but `delivered.Has` true at the adoption (swift.go:643): `phase = ACCEPT` with the
descriptor's own `dep`. `depWhy`'s "executed in `b`" disjunct: the `Has` hit, against the
owner's epoch pin and `delivInv`'s record (`swift.delivFz`'s `exLb`), gives `exIn γxm b x`. -/
theorem swift.depWhy_dlvd (γ : sp.Names) (γxm : GName) (N r b : Nat) (x : swift.CommandId)
    (dv : swift.DescV) (h : r ≠ sp.leaderOf N b) :
    swift.exIn γxm b x ⊢ swift.depWhy γ γxm N r b x dv := by
  iintro #Hex
  iunfold swift.depWhy; ileft; iright
  isplitr
  · ipureintro; exact h
  iexact Hex

/-- The closure's `Add` frame `F ∗ ocfRes0` has an `OptCondF` part and `F`. -/
theorem swift.ocf0Dc_ok (d : Loc) (F : IProp netDistGF) :
    iprop(F ∗ swift.ocfRes0 d) ⊢ ∃ (cf : Loc) (cond : GoFunc) (fs : List GoFunc) (v : Bool),
      swift.ocfRes d cf cond fs v ∗ F := by
  iintro ⟨HF, Ho⟩
  iunfold swift.ocfRes0 at Ho
  icases Ho with ⟨%cf, %cond, Ho, -⟩
  iexists cf, cond, [], true
  iframe

/-- The ballot's and `status`'s read shares and the sets' fields out of the lent state, and
back (round 24: `status` is `descSt`'s `shOwn`). -/
theorem swift.setR_openS (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) (s f : Loc) (qO : GoInterface) (szO : Nat) (memO : w32 → Prop)
    (hd : GoFunc) (slow : Bool) :
    swift.setR c RC MP γd d x b Do s f qO szO memO hd slow ⊢
      ∃ (qe : Qp) (bw : w32) (st : w64),
        typedPointsto (swift.fld c.rp go!"ballot") bw (DFrac.own qe) ∗
        typedPointsto (swift.fld c.rp go!"status") st (DFrac.own qe) ∗
        swift.dfld d go!"slowPathH" ↦ s ∗ swift.dfld d go!"fastPathH" ↦ f ∗
        ⌜sp.bal bw = b ∧ 0 ≤ sint.Z bw⌝ ∗
        (typedPointsto (swift.fld c.rp go!"ballot") bw (DFrac.own qe) -∗
          typedPointsto (swift.fld c.rp go!"status") st (DFrac.own qe) -∗
          swift.dfld d go!"slowPathH" ↦ s -∗ swift.dfld d go!"fastPathH" ↦ f -∗
          swift.setR c RC MP γd d x b Do s f qO szO memO hd slow) := by
  unfold swift.setR swift.descSt swift.epochRd
  iintro ⟨%qe, %bw, %stp, %rcp, %dv, %rv, ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩, Hsh, HRC, Hd, Htok, Hcom,
    #Hra, %Hph, #Hpw, #Hdw, %Hrp, #HsB, ⟨HsF, HfF, HRs⟩⟩
  ihave ⟨%st, %fq, %szF', %memF', Hst, HFQ, #HqF, %HAQ, Hshb⟩ := swift.shOwn_open c d b qe $$ Hsh
  iexists qe, bw, st
  iframe Hbal Hst HsF HfF
  isplitr
  · ipureintro; exact Hbw
  iintro Hbal Hst HsF HfF
  ihave Hsh := Hshb $$ Hst HFQ
  iexists qe, bw, stp, rcp, dv, rv
  iframe Hsh Hbal HStf Hrcf Het Hxe HRC Hd Htok Hcom Hra HRs HsF HfF Hpw Hdw HsB
  isplitr
  · ipureintro; exact Hbw
  isplitr
  · ipureintro; exact Hph
  ipureintro; exact Hrp

/-- `slowPath` out of the lent state (`descCore`), and back with any value. -/
theorem swift.setR_slowPath (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (s f : Loc) (qO : GoInterface) (szO : Nat)
    (memO : w32 → Prop) (hd : GoFunc) (slow : Bool) :
    swift.setR c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) s f qO szO memO hd slow ⊢
      ∃ sl : Bool, swift.dfld d go!"slowPath" ↦ sl ∗
        (∀ sl' : Bool, swift.dfld d go!"slowPath" ↦ sl' -∗
          swift.setR c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) s f qO szO memO hd
            slow) := by
  unfold swift.setR swift.descSt swift.descCore
  iintro ⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, #Hra, %Hph, #Hpw, #Hdw, %Hrp, #HsB,
    ⟨HsF, HfF, HdO, ⟨%wa, %sl, Hwa, Hsl, Hw⟩, HDo⟩⟩
  iexists sl
  iframe Hsl
  iintro %sl' Hsl
  iexists qe, bw, stp, rcp, dv, rv
  iframe Hsh Hrd HRC Hd Htok Hcom Hra HsF HfF HdO HDo Hpw Hdw HsB
  isplitr
  · ipureintro; exact Hph
  isplitr
  · ipureintro; exact Hrp
  iexists wa, sl'
  iframe Hwa Hsl Hw

/-- The owner state opened at `waitingAck` (`descCore`'s; moved from HandleMsg.lean for handlePropose's N2-nofast check): nil, or the ballot's leader's ack for
`x` with its witness. -/
theorem swift.descOwn_waiting (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) :
    swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ⊢
      ∃ wa : Loc, swift.dfld d go!"waitingAck" ↦ wa ∗
        (⌜wa = null⌝ ∨ ∃ fa : swift.MFastAck,
          ⌜fa.CmdId' = x ∧ sp.rid fa.Replica' = sp.leaderOf c.N b⌝ ∗ swift.leadWit c wa fa) ∗
        (swift.dfld d go!"waitingAck" ↦ wa -∗
          swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do)) := by
  unfold swift.descOwn
  iintro ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF, HdS, HR⟩
  iunfold swift.setR at HR
  iunfold swift.descSt at HR
  icases HR with ⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, #Hra, %Hph,
    #Hpw, #Hdw, %Hrp, #HsB, ⟨HsF, HfF, HdF, ⟨Hcore, HDo⟩⟩⟩
  iunfold swift.descCore at Hcore
  icases Hcore with ⟨%wa, %sl, Hwa, Hsl, #Hw⟩
  iexists wa
  iframe Hwa Hw
  iintro Hwa
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe HhS HhF HdS
  iunfold swift.setR
  iunfold swift.descSt
  iexists qe, bw, stp, rcp, dv, rv
  ihave Hcore : swift.descCore c d x b $$ [Hwa Hsl]
  · iunfold swift.descCore
    iexists wa, sl
    iframe Hwa Hsl Hw
  iframe Hrd Hsh HRC Hd Htok Hcom Hra HsF HfF HdF HDo Hcore Hpw Hdw HsB
  isplitr
  · ipureintro; exact Hph
  ipureintro; exact Hrp

/-- The stored closures and then `f` at a follower: each from the owner state or retired. -/
theorem swift.chain_follower (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (hL : c.r ≠ sp.leaderOf c.N b) (Q : IProp netDistGF) :
    ∀ gs : List GoFunc,
    ([∗list] g ∈ gs, □ swift.closureOk c RC MP γd d x b Do g) ⊢
      ((swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) ∨
          swift.descDone c b x d) -∗
      (((swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) ∨
          swift.descDone c b x d) -∗ Q) -∗ hook.ocf.chain gs Q
  | [] => by
    iintro - Hs HQ
    simp only [hook.ocf.chain]
    iapply HQ; iexact Hs
  | g :: gs => by
    iintro ⟨#Hg, #Hgs⟩ Hst HQ
    simp only [hook.ocf.chain]
    iunfold swift.closureOk at Hg
    iapply Hg $$ [Hst]
    · icases Hst with (H | H)
      · ileft; iexact H
      · iright; iframe H; ipureintro; exact hL
    inext
    iintro Hs
    isplitr
    · ipureintro; rfl
    iapply (swift.chain_follower c RC MP γd d x b Do hL Q gs) $$ Hgs Hs HQ

/-- The stored closures at the ballot's leader (no-ops), then the rest. -/
theorem swift.chain_leader (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (rest : List GoFunc) (Q : IProp netDistGF) :
    ∀ gs : List GoFunc,
    ([∗list] g ∈ gs, □ swift.closureNop c RC MP γd d x b Do g) ⊢
      (swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ∗
        swift.ocfRes0 d) -∗
      ((swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ∗
        swift.ocfRes0 d) -∗ hook.ocf.chain rest Q) -∗
        hook.ocf.chain (gs ++ rest) Q
  | [] => by
    iintro - Hs HQ
    simp only [List.nil_append]
    iapply HQ; iexact Hs
  | g :: gs => by
    iintro ⟨#Hg, #Hgs⟩ ⟨Hown, Ho⟩ HQ
    simp only [List.cons_append, hook.ocf.chain]
    iunfold swift.closureNop at Hg
    iapply Hg $$ [Hown]
    · iframe Hown
    inext
    iintro Hown
    isplitr
    · ipureintro; rfl
    iapply (swift.chain_leader c RC MP γd d x b Do rest Q gs) $$ Hgs [Hown Ho] HQ
    iframe Hown Ho

/-- **At the ballot's leader, a false condition means an ack of an earlier ballot**: the ack's
witness of the current ballot (`fastAckOk`: the leader pre-accepted `x` in `b`) makes `x`'s row
pre-accepted (`preacc_row`), so the descriptor has its proposal (`rowAcc`): `propose != nil`. -/
theorem swift.leader_cond (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do0 : IProp netDistGF) (v : Bool) (l : Loc) (fa : swift.MFastAck)
    (hx : fa.CmdId' = x) :
    c.ctx ∗ swift.descOwn c RC MP γd d x b Do0 ∗ swift.proposeHalf d v ∗ swift.leadWitB c b l fa ⊢
    |={⊤}=> swift.descOwn c RC MP γd d x b Do0 ∗ swift.proposeHalf d v ∗
      (⌜v = false → c.r = sp.leaderOf c.N b → sp.rid fa.Replica' = sp.leaderOf c.N b →
        sp.bal fa.Ballot' ≠ b⌝ ∨ ∃ D : List sp.CmdId, sp.preacc c.γ c.r b (toCmdId x) D) := by
  iintro ⟨#Hctx, Hown, HPc, #Hwit⟩
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, %Hids, -, -, -,
    #Hinv, #Hcfg, #Hninv, -⟩
  obtain ⟨-, -, hrN, -, -, hk⟩ := Hids
  iunfold swift.descOwn at Hown
  icases Hown with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF, HdS,
    HR⟩
  iunfold swift.setR at HR
  iunfold swift.descSt at HR
  icases HR with ⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, ⟨#Hra, #HrP⟩, %Hph, #Hpw,
    #Hdw, %Hrp, #HsB, HRs⟩
  iunfold swift.proposeHalf at HPc
  icases HPc with ⟨%p, Hp, %Hpv⟩
  iunfold swift.descF at Hd
  icases Hd with ⟨Hph', Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hprop, Hseq, Hmsgs, #Hmb, #HsL, %Hop⟩
  icombine Hprop Hp gives %Heq
  iunfold swift.epochRd at Hrd
  icases Hrd with ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩
  ihave Hupd : iprop(|={⊤}=> swift.epochTok c.γe qe (b, b) ∗
      swift.rowTokO c b x dv rv ∗
      (⌜v = false → c.r = sp.leaderOf c.N b → sp.rid fa.Replica' = sp.leaderOf c.N b →
        sp.bal fa.Ballot' ≠ b⌝ ∨ ∃ D : List sp.CmdId, sp.preacc c.γ c.r b (toCmdId x) D))
      $$ [Het Htok]
  · by_cases hcase : v = false ∧ c.r = sp.leaderOf c.N b ∧
        sp.rid fa.Replica' = sp.leaderOf c.N b ∧ sp.bal fa.Ballot' = b
    · obtain ⟨hv, hr, hrep, hbal⟩ := hcase
      iunfold swift.leadWitB at Hwit
      icases Hwit with (%hne | #Hwit)
      · exfalso; exact hne hbal
      iunfold swift.leadWit at Hwit
      icases Hwit with ⟨%fw, -, ⟨%h1, %h2, %h3⟩, -, #Hok, -⟩
      iunfold sp.fastAckOk at Hok
      icases Hok with ⟨-, #Hpre, -⟩
      have e1 : sp.rid fw.rep = c.r := by rw [← h1, hrep, hr]
      have e2 : sp.bal fw.bal = b := by rw [← h2, hbal]
      have e3 : fw.id = toCmdId x := by rw [← h3, hx]
      ihave #Hpre' : sp.preacc c.γ c.r b (toCmdId x) fw.dep $$ [Hpre]
      · rw [← e1, ← e2, ← e3]; iexact Hpre
      iunfold swift.rowTokO at Htok
      icases Htok with (⟨Htok, Hslt⟩ | ⟨%Hn, Hj, Hslt⟩)
      rotate_left
      · -- G10: no token (a second incarnation of `x` in `b`): the leader's pre-acceptance
        imodintro; iframe Het
        isplitl [Hj Hslt]
        · iunfold swift.rowTokO; iright; iframe Hj Hslt; ipureintro; exact Hn
        iright; iexists fw.dep; iexact Hpre'
      imod (swift.preacc_row c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr lg qe b
        (toCmdId x) fw.dep rv hrN hk) $$ [Het Htok] with ⟨Het, Htok, %Hrv⟩
      · iframe Hinv Hcfg Hninv Het Htok Hpre'
      iunfold swift.rowAcc at Hra
      icases Hra with ⟨-, %Hra, -⟩
      exfalso
      have hp : dv.propose ≠ null := Hra (Or.inl (by rw [Hrv]; rfl))
      rw [Heq] at hp
      rw [hv] at Hpv
      simp [hp] at Hpv
    · imodintro
      iframe Het Htok
      ileft
      ipureintro
      intro hv hr hrep hbal
      exact hcase ⟨hv, hr, hrep, hbal⟩
  imod Hupd with ⟨Het, Htok, #Hfact⟩
  imodintro
  isplitr [Hp]
  · iunfold swift.descOwn
    iexists s, f, qS, qF, szS, szF, memS, memF, hd
    iframe HhS HhF HdS
    iunfold swift.setR
    iunfold swift.descSt
    iexists qe, bw, stp, rcp, dv, rv
    iframe Hsh HRC Htok Hcom Hra HrP HRs Hpw Hdw HsB
    isplitl [Hbal HStf Hrcf Het Hxe]
    · iunfold swift.epochRd; iframe Hbal HStf Hrcf Het Hxe; ipureintro; exact Hbw
    isplitl [Hph' Hcmd Hdep Hhs Hprop Hseq Hmsgs]
    · iunfold swift.descF
      iframe Hph' Hcmd Hdep Hhs Hprop Hseq Hmsgs Hvs HD HHs Hmb HsL
      ipureintro; exact Hop
    isplitr
    · ipureintro; exact Hph
    ipureintro; exact Hrp
  isplitl [Hp]
  · iunfold swift.proposeHalf; iexists p; iframe Hp; ipureintro; exact Hpv
  iexact Hfact

/-- The stored closures' specs give the follower's form. -/
theorem swift.stored_closureOk (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (fs : List GoFunc) :
    ([∗list] g ∈ fs, swift.storedOk c RC MP γd d x b Do g) ⊢
      [∗list] g ∈ fs, □ swift.closureOk c RC MP γd d x b Do g := by
  iintro #Hfs
  iapply BigSepL.bigSepL_mono _ $$ Hfs
  intro _ g _
  unfold swift.storedOk
  iintro ⟨#H, -⟩; iexact H

/-- At the ballot's leader, the stored closures are no-ops (round 28, G10: a closure stored
with the leader's pre-acceptance is refuted by the row token of a not yet pre-accepted row). -/
theorem swift.stored_closureNopT (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (hL : c.r = sp.leaderOf c.N b) (fr : Bool)
    (lg : List GoString) (qe : Qp) (rv : swift.RowV) (hrv : rv.1 = none) (hrN : c.r < c.N)
    (hk : nodeOf lg c.r = some c.k) :
    ∀ fs : List GoFunc,
    sp.inv c.γ c.γc c.γm c.γl ∗ sp.cfg c.γc c.γm c.N fr lg ∗
      inv swift.nodeN (swift.nodeInvD c.γ c.γv c.γe c.γo c.sn c.k) ∗
      swift.epochTok c.γe qe (b, b) ∗ swift.rowTok c.γo b (toCmdId x) rv ∗
      ([∗list] g ∈ fs, swift.storedOk c RC MP γd d x b Do g) ⊢
    |={⊤}=> swift.epochTok c.γe qe (b, b) ∗ swift.rowTok c.γo b (toCmdId x) rv ∗
      [∗list] g ∈ fs, □ swift.closureNop c RC MP γd d x b Do g
  | [] => by
    iintro ⟨-, -, -, Het, Htok, -⟩
    imodintro; iframe Het Htok
    iapply BigSepL.bigSepL_nil.2; itrivial
  | g :: gs => by
    iintro ⟨#Hinv, #Hcfg, #Hninv, Het, Htok, ⟨#Hg, #Hgs⟩⟩
    iunfold swift.storedOk at Hg
    icases Hg with ⟨-, (%Hn | #Hn | ⟨%D, #Hp⟩)⟩
    · exact absurd hL Hn
    · imod (swift.stored_closureNopT c RC MP γd d x b Do hL fr lg qe rv hrv hrN hk gs)
        $$ [Het Htok] with ⟨Het, Htok, #Hns⟩
      · iframe Hinv Hcfg Hninv Het Htok Hgs
      imodintro; iframe Het Htok
      isplitr
      · iexact Hn
      · iexact Hns
    · imod (swift.preacc_row c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr lg qe b
        (toCmdId x) D rv hrN hk) $$ [Het Htok] with ⟨Het, Htok, %Hrv⟩
      · iframe Hinv Hcfg Hninv Het Htok Hp
      rw [hrv] at Hrv; cases Hrv

/-- At the ballot's leader, `storedOk2` closures are no-ops (round 29, G14). -/
theorem swift.stored2_nop (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (hL : c.r = sp.leaderOf c.N b) :
    ∀ fs : List GoFunc,
    ([∗list] g ∈ fs, swift.storedOk2 c RC MP γd d x b Do g) ⊢
      [∗list] g ∈ fs, □ swift.closureNop c RC MP γd d x b Do g
  | [] => by
    iintro -
    iapply BigSepL.bigSepL_nil.2; itrivial
  | g :: gs => by
    iintro ⟨#Hg, #Hgs⟩
    iunfold swift.storedOk2 at Hg
    icases Hg with ⟨-, (%Hn | #Hn)⟩
    · exact absurd hL Hn
    isplitr
    · iexact Hn
    iapply swift.stored2_nop c RC MP γd d x b Do hL gs $$ Hgs

/-- The stored closures' specs without the pre-acceptance disjunct, by the row token of a not
yet pre-accepted row (round 28, G10). -/
theorem swift.stored_ok2T (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (fr : Bool)
    (lg : List GoString) (qe : Qp) (rv : swift.RowV) (hrv : rv.1 = none) (hrN : c.r < c.N)
    (hk : nodeOf lg c.r = some c.k) :
    ∀ fs : List GoFunc,
    sp.inv c.γ c.γc c.γm c.γl ∗ sp.cfg c.γc c.γm c.N fr lg ∗
      inv swift.nodeN (swift.nodeInvD c.γ c.γv c.γe c.γo c.sn c.k) ∗
      swift.epochTok c.γe qe (b, b) ∗ swift.rowTok c.γo b (toCmdId x) rv ∗
      ([∗list] g ∈ fs, swift.storedOk c RC MP γd d x b Do g) ⊢
    |={⊤}=> swift.epochTok c.γe qe (b, b) ∗ swift.rowTok c.γo b (toCmdId x) rv ∗
      [∗list] g ∈ fs, swift.storedOk2 c RC MP γd d x b Do g
  | [] => by
    iintro ⟨-, -, -, Het, Htok, -⟩
    imodintro; iframe Het Htok
    iapply BigSepL.bigSepL_nil.2; itrivial
  | g :: gs => by
    iintro ⟨#Hinv, #Hcfg, #Hninv, Het, Htok, ⟨#Hg, #Hgs⟩⟩
    iunfold swift.storedOk at Hg
    icases Hg with ⟨#Hok, (%Hn | #Hn | ⟨%D, #Hp⟩)⟩
    rotate_right
    · imod (swift.preacc_row c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr lg qe b
        (toCmdId x) D rv hrN hk) $$ [Het Htok] with ⟨Het, Htok, %Hrv⟩
      · iframe Hinv Hcfg Hninv Het Htok Hp
      rw [hrv] at Hrv; cases Hrv
    all_goals
      imod (swift.stored_ok2T c RC MP γd d x b Do fr lg qe rv hrv hrN hk gs)
        $$ [Het Htok] with ⟨Het, Htok, #Hns⟩
      · iframe Hinv Hcfg Hninv Het Htok Hgs
      imodintro; iframe Het Htok
      isplitr
      · iunfold swift.storedOk2; iframe Hok
        first | (ileft; ipureintro; exact Hn) | (iright; iexact Hn)
      · iexact Hns

/-- **`desc.afterPropagate.Call(f)`** for a leader ack's closure `f` with its specs (`closureOk`,
and `closureNop` when it may be stored at the ballot's leader). -/
theorem swift.fastAck_call (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (cf : Loc) (cond : GoFunc) (fs : List GoFunc) (v : Bool)
    (f : GoFunc) (sb : GoSlice) (bs : List w32)
    (Hb : bs.Nodup ∧ fs.length ≤ bs.length ∧ (v = false → fs.length + 1 ≤ bs.length))
    (wp_Call : hook.ocf.OptCondF.Call.specI) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.hook ∗
        swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ∗
        swift.dfld d go!"afterPropagate" ↦ cf ∗
        hook.ocf.ownOcf cf cond fs ∗ □ hook.ocf.condOk cond (swift.proposeHalf d) ∗
        swift.proposeHalf d v ∗ ([∗list] g ∈ fs, swift.storedOk c RC MP γd d x b Do g) ∗
        swift.ocfV c RC MP γd d x b Do v fs ∗
        □ swift.closureOk c RC MP γd d x b Do f ∗
        (⌜v = true ∨ c.r ≠ sp.leaderOf c.N b⌝ ∨ □ swift.closureNop c RC MP γd d x b Do f ∨
          ∃ D : List sp.CmdId, sp.preacc c.γ c.r b (toCmdId x) D) ∗
        swift.dfld d go!"storedBallots" ↦ sb ∗ sb ↦* bs ∗ ownSliceCap w32 sb (DFrac.own 1) }}
      (App (Val #(methods (go.GoType.PointerType hook.OptCondF.ty) go!"Call" #cf)) (Val #f))
    {{ (bb : Bool), RET #bb; swift.descOwnF c RC MP γd d x b Do ∨ swift.descDone c b x d }} := by
  iintro %Φ ⟨#Hpkg, Hown, Hapf, Hocf, #Hcond, HPc, #Hfs, #Hvf, #Hf, #Hfn, Hsb, Hbs, Hbsc⟩ HΦ
  -- SWB-10 closed by the fork's P3: the stored closures are at most the stored ballots
  have hbound : fs.length + 1 < 2 ^ 62 := by
    have := swift.nodup_w32_len bs Hb.1; have := Hb.2.1; omega
  cases v
  · wp_apply (wp_Call cf cond fs f (swift.proposeHalf d) false iprop(True)) $$ [Hocf HPc]
      as %bb ⟨%Hbb, Hres⟩
    · iframe Hocf Hcond HPc
      isplitr
      · ipureintro; exact hbound
      simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hres with ⟨Hocf, HPc⟩
    iapply HΦ
    ileft
    iunfold swift.descOwnF
    iframe Hown
    iunfold swift.descOcf
    iexists cf, cond, fs ++ [f], false
    iframe Hcond
    isplitl [Hapf Hocf HPc Hsb Hbs Hbsc]
    · iunfold swift.ocfRes
      iframe Hapf Hocf HPc
      iexists sb, bs; iframe Hsb Hbs Hbsc; ipureintro
      exact ⟨Hb.1, by simpa using Hb.2.2 rfl⟩
    isplitr
    · iapply swift.ocfV_false
    iapply BigSepL.bigSepL_snoc.2
    iframe Hfs
    iunfold swift.storedOk
    iframe Hf
    icases Hfn with (%H | #H | #H)
    · ileft; ipureintro; rcases H with h | h
      · cases h
      · exact h
    · iright; ileft; iexact H
    · iright; iright; iexact H
  · let Q : IProp netDistGF := iprop(((swift.descOwn c RC MP γd d x b
        iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) ∨ swift.descDone c b x d))
    wp_apply (wp_Call cf cond fs f (swift.proposeHalf d) true Q)
      $$ [Hocf HPc Hown Hapf Hsb Hbs Hbsc] as %bb ⟨%Hbb, Hres⟩
    · iframe Hocf Hcond HPc
      isplitr
      · ipureintro; exact hbound
      simp only [↓reduceIte]
      iintro HPc Hocf
      -- round 33 (table rev 4 §3.6b): the spec-free `OptCondF` part goes down the chain
      ihave Ho0 : swift.ocfRes0 d $$ [Hapf Hocf HPc Hsb Hbs Hbsc]
      · iunfold swift.ocfRes0; iexists cf, cond; iframe Hcond
        iunfold swift.ocfRes; iframe Hapf Hocf HPc
        iexists sb, bs; iframe Hsb Hbs Hbsc; ipureintro; exact ⟨Hb.1, by simp⟩
      by_cases hL : c.r = sp.leaderOf c.N b
      · ihave #Hnops : [∗list] g ∈ fs, □ swift.closureNop c RC MP γd d x b Do g $$ []
        · iunfold swift.ocfV at Hvf
          icases Hvf with (%Hv | #Hvf)
          · cases Hv
          iapply swift.stored2_nop c RC MP γd d x b Do hL fs $$ Hvf
        iapply (swift.chain_leader c RC MP γd d x b Do [f] Q fs) $$ Hnops [Hown Ho0]
        · iframe Hown Ho0
        iintro ⟨Hown, Ho0⟩
        simp only [hook.ocf.chain]
        iunfold swift.closureOk at Hf
        iapply Hf $$ [Hown Ho0]
        · ileft; iframe Hown Ho0
        inext
        iintro Hs
        isplitr
        · ipureintro; rfl
        iexact Hs
      · ihave #Hok := swift.stored_closureOk c RC MP γd d x b Do fs $$ Hfs
        iapply (swift.chain_follower c RC MP γd d x b Do hL Q (fs ++ [f])) $$ [Hok] [Hown Ho0]
        · iapply BigSepL.bigSepL_snoc.2; iframe Hok Hf
        · ileft; iframe Hown Ho0
        iintro Hs
        iexact Hs
    simp only [↓reduceIte]
    iapply HΦ
    icases Hres with (⟨Hown, Ho0⟩ | Hdone)
    · ileft
      iunfold swift.descOwnF
      iframe Hown
      iunfold swift.ocfRes0 at Ho0
      icases Ho0 with ⟨%cf', %cond', Ho, #Hcond'⟩
      iunfold swift.descOcf
      iexists cf', cond', [], true
      iframe Ho Hcond'
      isplitr
      · iapply swift.ocfV_nil
      iapply BigSepL.bigSepL_nil.2; itrivial
    · iright; iexact Hdone

end proof

end Perennial.github_com.imdea_software.swiftpaxos
