/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SeqPark.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**A sequential descriptor's owner state between two inline calls** (round 35, sv-swb; table rev
5 C6, R5, T7; notes/prove-swift.md §43): the run loop's inline `handleMsg` (T7) lends the
descriptor an inline loan at its start and returns it at its end, so between two calls the owner
state is kept without its epoch share's part (`epochRd q`, `shOwnR c d b q`, the reply channel's
object `RC rcp bw`). The run loop's freeze (T20, `soOk`'s second clause) needs the fields, so the
parked state exposes them: it is `descOwnF`'s structure with `descSt`'s epoch part removed
(`swift.descStP`), at the `γsh` value `q` its `γsh` half has.

* `swift.descStP`, `swift.setRP`, `swift.descOwnP`, `swift.descOwnFP`: the parked forms.
* `swift.descOwnF_park`: the owner state is its epoch part and its parked form (round 47, Q1-a:
  when tokenless, with `c.slot none` out; with its token, the token out).
* `swift.descOwnF_unpark`: the converse, at the parked state's `γsh` value (and `c.slot none`).
* `swift.descOwnFP_sh`: the parked state's `γsh` half out, and back at any value (T7's start
  updates the element to the new loan's share, `shInv_update`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescKind
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- **The tokenless parked row** (round 37; table rev 8 G-pslot, plan R8.1): `rowTokO`'s tokenless
disjunct without the ledger slot (the parked state keeps no registry share). Round 47 (Q1-a, D63):
with the row `rv` (empty), and the parked free form's row (`descStP`): a sequential descriptor
parks free only without its token, and gives its `c.slot none` back at the park. -/
def swift.rowTokP (c : swift.DC) (b : Nat) (x : swift.CommandId) (dv : swift.DescV) (rv : swift.RowV) :
    IProp netDistGF :=
  iprop(⌜rv = swift.rowEmpty ∧ dv.propose = null⌝ ∗
    (⌜dv.phase ≠ swift.phCOMMIT⌝ ∨ ⌜c.r = sp.leaderOf c.N b⌝ ∨ sp.accepted c.γ c.r b (toCmdId x)))

/-- `descSt` without its epoch part, at the `γsh` value `q` (see the file header). Round 47
(Q1-a, D63): its row is tokenless (`rowTokP`); (D61 (2)) with `repPre`. -/
def swift.descStP (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (q : Qp) (Rs : IProp netDistGF) :
    IProp netDistGF :=
  iprop(∃ (dv : swift.DescV) (rv : swift.RowV),
    ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) q ∗ swift.descF d γd MP dv ∗
    swift.rowTokP c b x dv rv ∗
    (⌜rv.2.2.2 = false⌝ ∨ sp.committed c.γ c.r b (toCmdId x)) ∗
    (swift.rowAcc c b x dv rv ∗ swift.repPre c.γ c.N c.r b x dv) ∗
    ⌜dv.phase = swift.phCOMMIT → rv.2.2.2 = true ∨ dv.propose = null⌝ ∗
    swift.phaseWhy c.γ c.N c.r b x dv ∗ swift.depWhy c.γ c.γxm c.N c.r b x dv ∗
    ⌜swift.rowPhaseOk c.N c.r b dv rv ∧ dv.seq = c.sq⌝ ∗ □ swift.slotB MP c.γxm b x ∗ Rs)

/-- `setR` over `descStP`. -/
def swift.setRP (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (q : Qp) (Do : IProp netDistGF)
    (s f : Loc) (qO : GoInterface) (szO : Nat) (memO : w32 → Prop) (hd : GoFunc) (slow : Bool) :
    IProp netDistGF :=
  swift.descStP c RC MP γd d x b q iprop(swift.dfld d go!"slowPathH" ↦ s ∗
    swift.dfld d go!"fastPathH" ↦ f ∗
    replica.mset.ownD (if slow then f else s) qO szO memO (swift.ackP x) swift.ackA
      (swift.leadAckP c b x) iprop(True) hd ∗ Do)

/-- `descOwn` over `setRP`. -/
def swift.descOwnP (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (q : Qp) (Do : IProp netDistGF) :
    IProp netDistGF :=
  iprop(∃ (s f : Loc) (qS qF : GoInterface) (szS szF : Nat) (memS memF : w32 → Prop) (hd : GoFunc),
    swift.acksHdOk c RC MP γd d x b hd ∗ swift.slotCap c MP γd d x b Do ∗
    replica.mset.ownD s qS szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd ∗
    swift.setRP c RC MP γd d x b q Do s f qF szF memF hd true)

/-- **The parked owner state** (see the file header). -/
def swift.descOwnFP (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (q : Qp) (Do : IProp netDistGF) :
    IProp netDistGF :=
  iprop(swift.descOwnP c RC MP γd d x b q iprop(swift.descCore c d x b ∗ Do) ∗
    swift.descOcf c RC MP γd d x b Do)

/-- **`descF` with the rest record's shares out** (round 37; table rev 8 G-pslot): `phase` and `dep`
at ½ and `propose` at ¼ (the store's rest record holds ½, ½ and ¼). -/
def swift.descFT (d : Loc) (γm : ChanNames) (MP : GoInterface → IProp netDistGF)
    (dv : swift.DescV) : IProp netDistGF :=
  iprop(typedPointsto (swift.dfld d go!"phase") dv.phase (DFrac.own (1 : Qp).half) ∗
    swift.dfld d go!"cmd" ↦ state.Command.mk dv.c.op dv.c.key dv.vs ∗ dv.vs ↦*□ dv.c.val ∗
    typedPointsto (swift.dfld d go!"dep") dv.dep (DFrac.own (1 : Qp).half) ∗ dv.dep ↦*□ dv.D ∗
    typedPointsto (swift.dfld d go!"hs") dv.hs (DFrac.own (1 : Qp).half) ∗ dv.hs ↦*□ dv.Hs ∗
    typedPointsto (swift.dfld d go!"propose") dv.propose (DFrac.own (1 : Qp).half.half) ∗
    typedPointsto (swift.dfld d go!"seq") dv.seq (DFrac.own (1 : Qp).half.half) ∗
    typedPointsto (swift.dfld d go!"msgs") dv.msgs (DFrac.own (1 : Qp).half) ∗
    isChanBag γm dv.msgs MP ∗
    sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d) ∗ ⌜dv.c.op ≠ W8 3⌝)

/-- **`descSt` parked with its token in the store** (round 37; table rev 8 G-pslot): the fields at
`descFT`'s fractions and the facts the store's rest record does not keep (`phaseWhy`, `depWhy`;
the record has `rowPhaseOk`, `rowFacts`, `stopFacts`), the slot builder (K1), at `γsh`'s value `q`.
Round 47: with `repPre` (D61 (2)) and (Q1-b, D63) `dv.propose = null → dv.D = []` (`rowPhaseOk`'s
no-proposal clause, which the rest record's `stopFacts` give no source for). -/
def swift.descStT (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (q : Qp) (Rs : IProp netDistGF) :
    IProp netDistGF :=
  iprop(∃ dv : swift.DescV, ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) q ∗ swift.descFT d γd MP dv ∗
    swift.phaseWhy c.γ c.N c.r b x dv ∗ swift.depWhy c.γ c.γxm c.N c.r b x dv ∗
    swift.repPre c.γ c.N c.r b x dv ∗ ⌜dv.seq = c.sq ∧ (dv.propose = null → dv.D = [])⌝ ∗
    □ swift.slotB MP c.γxm b x ∗ Rs)

/-- **The token-out parked owner state** (round 37; table rev 8 G-pslot): `descOwnFP`'s structure
over `descStT`, with the specs at the frame `Do` (the frame the owner state has when it is taken
back, T7s) and the resources at the frame `Dr` (what is parked now: `descRest` and `kfK0`). Round 47
(Q1-c, D63): the slot capability at `descCore c d x b ∗ Do`, as `descOwnFP`'s (`descOwnP`'s). -/
def swift.descOwnFT (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (q : Qp) (Do Dr : IProp netDistGF) :
    IProp netDistGF :=
  iprop((∃ (s f : Loc) (qS qF : GoInterface) (szS szF : Nat) (memS memF : w32 → Prop) (hd : GoFunc),
      swift.acksHdOk c RC MP γd d x b hd ∗ swift.slotCap c MP γd d x b iprop(swift.descCore c d x b ∗ Do) ∗
      replica.mset.ownD s qS szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd ∗
      swift.descStT c RC MP γd d x b q iprop(swift.dfld d go!"slowPathH" ↦ s ∗
        swift.dfld d go!"fastPathH" ↦ f ∗
        replica.mset.ownD f qF szF memF (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd ∗
        swift.descCore c d x b ∗ Dr)) ∗
    swift.descOcf c RC MP γd d x b Do)

/-- **The bag predicate of an incarnation** (round 37; plan R8.2 abbreviation `MPi`): the epoch's
message predicate of `y` with the incarnation's commit witness. -/
abbrev swift.MPi (g : swift.DescG) (y : swift.CommandId) (γi γsg : GName) :
    GoInterface → IProp netDistGF :=
  fun v => iprop(g.mp y v ∗ □ swift.incW g γi γsg)

/-- **A new sequential descriptor's raw owner state** (round 37; table rev 8 G-circ/G-sqγi, plan
R8.2 (1)): kind-free (`descRaw` at the replica's record `x.dc`), with half of `msgs` (its bag at
`MPi`), `active`, a quarter of `seq`, `stopChan`, the `γsh` element, the incarnation's half and its
commit witness. The only form the goroutines' inbox holds (`g.sr`). -/
def swift.soRaw (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (RC : Loc → w32 → IProp netDistGF)
    (g : swift.DescG) (d : Loc) (y : swift.CommandId) : IProp netDistGF :=
  iprop(∃ (γi γsg : GName) (γmc : ChanNames) (m sc : Loc) (q : Qp) (sqv fqv : GoInterface) (szS szF : Nat)
      (memS memF : w32 → Prop),
    □ swift.incW g γi γsg ∗ ghostVar γi (1 : Qp).half (x.str y, d) ∗
    typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half) ∗ isChanBag γmc m (swift.MPi g y γi γsg) ∗
    typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗
    typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half.half) ∗
    swift.dfld d go!"stopChan" ↦ sc ∗ ghostMapElem x.γsh d (DFrac.own 1) q ∗
    swift.descRaw (x.dc γ γc γm rp) RC (swift.MPi g y γi γsg) y g.ev.b sqv fqv szS szF memS memF γmc d)

end defs

section defsO
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- **A sequential descriptor's state between two inline calls** (round 37; table rev 8 §3.1 P,
plan R8.2 (1); `g.so := soO … g0`): the raw form (`g0.sr`), or the parked owner state at the
inline record `cI` of `g0` (`dcK g0 (.seq γi)`; `rfl`-equal to `dcK g (.seq γi)`, G-circ), free
(tokenless: `descOwnFP`) or with its token in the store (the claim `rest d γi` and `descOwnFT`). -/
def swift.soO (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (RC : Loc → w32 → IProp netDistGF)
    (g0 : swift.DescG) (d : Loc) (y : swift.CommandId) : IProp netDistGF :=
  iprop(g0.sr d y ∨
    ∃ (γi γsg : GName) (γmc : ChanNames) (q : Qp),
      □ swift.incW g0 γi γsg ∗ swift.cgG x g0 ∗ (x.dc γ γc γm rp).ctx ∗
      (swift.descOwnFP (x.dcK γ γc γm rp g0 (.seq γi)) RC (swift.MPi g0 y γi γsg) γmc d y g0.ev.b q
          iprop(swift.descRest (x.dcK γ γc γm rp g0 (.seq γi)) g0.ev.b y d ∗
            (x.dcK γ γc γm rp g0 (.seq γi)).kf d y) ∨
       (swift.claimTok x.γcl (g0.ev.b, toCmdId y) (.rest d γi) ∗
        swift.descOwnFT (x.dcK γ γc γm rp g0 (.seq γi)) RC (swift.MPi g0 y γi γsg) γmc d y g0.ev.b q
          iprop(swift.descRest (x.dcK γ γc γm rp g0 (.seq γi)) g0.ev.b y d ∗
            (x.dcK γ γc γm rp g0 (.seq γi)).kf d y)
          iprop(swift.descRest (x.dcK γ γc γm rp g0 (.seq γi)) g0.ev.b y d ∗ swift.kfK0 x d))))

end defsO


section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- **Park** (T7's end, before the loan's return; see the file header). Round 47 (Q1-a, D63): the
row decides. Tokenless (`rowTokO`'s right disjunct): the epoch part, the parked free form and the
ledger's `c.slot none` (T7e tokenless). With the token: the token and its slot out, and the owner
state back from them (T7e's `store_putR` parks it token-out, `descOwnFT`; the caller's step). -/
theorem swift.descOwnF_park (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) :
    swift.descOwnF c RC MP γd d x b Do ⊢
      (∃ (q : Qp) (bw : w32) (stp rcp : Loc), swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗
        swift.shOwnR c d b q ∗ RC rcp bw ∗ swift.descOwnFP c RC MP γd d x b q Do ∗ c.slot none) ∨
      (∃ rv : swift.RowV, swift.rowTok c.γo b (toCmdId x) rv ∗ swift.slotT c (b, toCmdId x) ∗
        (swift.rowTok c.γo b (toCmdId x) rv -∗ swift.slotT c (b, toCmdId x) -∗
          swift.descOwnF c RC MP γd d x b Do)) := by
  iintro H
  iunfold swift.descOwnF at H
  icases H with ⟨Ho, Hocf⟩
  iunfold swift.descOwn at Ho
  icases Ho with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #Hhd, #Hcap, HoS, HsR⟩
  iunfold swift.setR at HsR
  iunfold swift.descSt at HsR
  icases HsR with ⟨%q, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, #Hra, Hph, #Hpw,
    #Hdw, Hrp, #HsB, HRs⟩
  iunfold swift.rowTokO at Htok
  icases Htok with (⟨Htk, Hslt⟩ | ⟨%Hn, Hj, Hslt⟩)
  · iright
    iexists rv
    iframe Htk Hslt
    iintro Htk Hslt
    iunfold swift.descOwnF
    iframe Hocf
    iunfold swift.descOwn
    iexists s, f, qS, qF, szS, szF, memS, memF, hd
    iframe Hhd Hcap HoS
    iunfold swift.setR
    iunfold swift.descSt
    iexists q, bw, stp, rcp, dv, rv
    iframe Hrd Hsh HRC Hd Hcom Hra Hph Hpw Hdw Hrp HsB HRs
    iunfold swift.rowTokO
    ileft
    iframe Htk Hslt
  ileft
  iunfold swift.shOwn at Hsh
  icases Hsh with ⟨Hγ, HshR⟩
  iexists q, bw, stp, rcp
  iframe Hrd HshR HRC Hslt
  iunfold swift.descOwnFP
  iframe Hocf
  iunfold swift.descOwnP
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe Hhd Hcap HoS
  iunfold swift.setRP
  iunfold swift.descStP
  iexists dv, rv
  iframe Hγ Hd Hcom Hra Hph Hpw Hdw Hrp HsB HRs
  iunfold swift.rowTokP
  iframe Hj
  ipureintro; exact Hn

/-- **Unpark** (T7's start, after the loan; see the file header). Round 47 (Q1-a, D63): with the
ledger's `c.slot none` the tokenless row gave back at the park. -/
theorem swift.descOwnF_unpark (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) (q : Qp) (bw : w32) (stp rcp : Loc) :
    swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗ swift.shOwnR c d b q ∗ RC rcp bw ∗
      swift.descOwnFP c RC MP γd d x b q Do ∗ c.slot none ⊢
    swift.descOwnF c RC MP γd d x b Do := by
  iintro ⟨Hrd, HshR, HRC, Hp, Hslt⟩
  iunfold swift.descOwnFP at Hp
  icases Hp with ⟨Ho, Hocf⟩
  iunfold swift.descOwnP at Ho
  icases Ho with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #Hhd, #Hcap, HoS, HsR⟩
  iunfold swift.setRP at HsR
  iunfold swift.descStP at HsR
  icases HsR with ⟨%dv, %rv, Hγ, Hd, Htok, Hcom, #Hra, Hph, #Hpw, #Hdw, Hrp, #HsB, HRs⟩
  iunfold swift.rowTokP at Htok
  icases Htok with ⟨%Hn, Hj⟩
  iunfold swift.descOwnF
  iframe Hocf
  iunfold swift.descOwn
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe Hhd Hcap HoS
  iunfold swift.setR
  iunfold swift.descSt
  iexists q, bw, stp, rcp, dv, rv
  iframe Hrd HRC Hd Hcom Hra Hph Hpw Hdw Hrp HsB HRs
  isplitl [Hγ HshR]
  · iunfold swift.shOwn
    iframe Hγ HshR
  iunfold swift.rowTokO
  iright
  iframe Hj Hslt
  ipureintro; exact Hn

/-- **The parked state's `γsh` half** (T7's start: the element is updated to the new loan's share;
see the file header). -/
theorem swift.descOwnFP_sh (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) (q : Qp) :
    swift.descOwnFP c RC MP γd d x b q Do ⊢
      ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) q ∗
      (∀ q' : Qp, ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) q' -∗
        swift.descOwnFP c RC MP γd d x b q' Do) := by
  iintro Hp
  iunfold swift.descOwnFP at Hp
  icases Hp with ⟨Ho, Hocf⟩
  iunfold swift.descOwnP at Ho
  icases Ho with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #Hhd, #Hcap, HoS, HsR⟩
  iunfold swift.setRP at HsR
  iunfold swift.descStP at HsR
  icases HsR with ⟨%dv, %rv, Hγ, Hd, Htok, Hcom, #Hra, Hph, #Hpw, #Hdw, Hrp, #HsB, HRs⟩
  iframe Hγ
  iintro %q' Hγ'
  iunfold swift.descOwnFP
  iframe Hocf
  iunfold swift.descOwnP
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe Hhd Hcap HoS
  iunfold swift.setRP
  iunfold swift.descStP
  iexists dv, rv
  iframe Hγ' Hd Htok Hcom Hra Hph Hpw Hdw Hrp HsB HRs

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
