/-
The definitions, specs and lemmas of `HandleMsg.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FastAckDefs
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- A fast ack's witness for `x`'s descriptor in epoch `b`: its sender is not `b`'s leader, or
the leader's ack's (gated) witness. -/
def swift.fastWhy (c : swift.DC) (b : Nat) (l : Loc) (fa : swift.MFastAck) : IProp netDistGF :=
  iprop(⌜sp.rid fa.Replica' ≠ sp.leaderOf c.N b⌝ ∨ swift.leadWitB c b l fa)

instance swift.fastWhy_persistent (c : swift.DC) (b : Nat) (l : Loc) (fa : swift.MFastAck) :
    Persistent (swift.fastWhy c b l fa) := by unfold swift.fastWhy; infer_instance

/-- The messages of `x`'s descriptor in epoch `b` other than a proposal, a `*syncEntry` and a
history slot (see the file header). -/
def swift.ackMsgP (c : swift.DC) (b : Nat) (x : swift.CommandId) (m : GoInterface) :
    IProp netDistGF :=
  iprop((∃ (l : Loc) (fa : swift.MFastAck),
      ⌜m = interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l ∧ 0 ≤ sint.Z fa.Replica'⌝ ∗
      l ↦□ fa ∗ (∃ D : List swift.CommandId, fa.Dep' ↦*□ D) ∗ swift.fastWhy c b l fa) ∨
    (∃ (l : Loc) (sa : swift.MLightSlowAck),
      ⌜m = interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l⌝ ∗ l ↦□ sa ∗
      swift.ackWhy c b x sa.Replica' sa.Ballot') ∨
    ⌜∃ s : GoString, m = interface.mkOk go.string #s⌝)

instance swift.ackMsgP_persistent (c : swift.DC) (b : Nat) (x : swift.CommandId) (m : GoInterface) :
    Persistent (swift.ackMsgP c b x m) := by unfold swift.ackMsgP; infer_instance

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [hook.Assumptions]

/-- `r.handleMsg(m, desc, cmdId)` for a message of `ackMsgP` (see the file header). -/
abbrev swift.Replica.handleMsg.ackSpecIc (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (AC : swift.DC → IProp netDistGF) (c : swift.DC) : Prop :=
  ∀ (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF)
    (m : GoInterface),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ □ AC c ∗ swift.descOwnF c RC MP γd d x b Do ∗ swift.ackMsgP c b x m }}
    (App (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleMsg"))
      (Val #m)) (Val #d)) (Val #x))
  {{ RET #false; swift.descOwnF c RC MP γd d x b Do ∨ swift.descDone c b x d }}

/-- `swift.Replica.handleMsg.ackSpecI` at every record (round 44, D53 (1): the per-record form `swift.Replica.handleMsg.ackSpecIc`). -/
abbrev swift.Replica.handleMsg.ackSpecI (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (AC : swift.DC → IProp netDistGF) : Prop :=
  ∀ c : swift.DC, swift.Replica.handleMsg.ackSpecIc RC MP AC c

end specs

theorem swift.cmdId_eq_iff (a b : swift.CommandId) (h : a.ClientId' = b.ClientId') :
    (a.SeqNum' = b.SeqNum') ↔ (a = b) := by
  cases a; cases b; simp_all

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [sync.Assumptions] [hook.Assumptions]
  [github_com.orcaman.concurrent_map.Assumptions]

/-- **Why the owner may `deliver`** (round 33, table rev 4/5 §3.7): from `descSt`'s facts. At
`b`'s leader with a proposal and not at `COMMIT`, `rowPhaseOk` leaves `PRE_ACCEPT` (`phaseWhy`:
pre-accepted with `dep`) or `ACCEPT` (the row accepted: `rowAcc`'s fact). -/
theorem swift.execWhy_of (c : swift.DC) (b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (rv : swift.RowV) (h : swift.rowPhaseOk c.N c.r b dv rv) :
    swift.phaseWhy c.γ c.N c.r b x dv ∗ swift.depWhy c.γ c.γxm c.N c.r b x dv ∗ swift.rowAcc c b x dv rv ⊢
      swift.execWhy c.γ c.γxm c.N c.r b x dv := by
  iintro ⟨#Hpw, #Hdw, #Hra⟩
  iunfold swift.execWhy
  iframe Hdw
  by_cases hp : dv.propose = null
  · ileft; ipureintro; exact Or.inl hp
  by_cases hl : c.r = sp.leaderOf c.N b
  rotate_left
  · ileft; ipureintro; exact Or.inr (Or.inl hl)
  by_cases h3 : dv.phase = swift.phCOMMIT
  · ileft; ipureintro; exact Or.inr (Or.inr h3)
  obtain ⟨hle, h0, -, h2, -, -⟩ := h.2 hp
  by_cases hph1 : dv.phase = W64 1
  · iright; iright
    isplitr
    · ipureintro; exact hph1
    iunfold swift.phaseWhy at Hpw
    icases Hpw with (%Hn | #Hp)
    · exact absurd hph1 Hn
    iexact Hp
  by_cases hph2 : dv.phase = W64 2
  · iright; ileft
    isplitr
    · ipureintro; exact hph2
    iunfold swift.rowAcc at Hra
    icases Hra with ⟨(%Hf | #Ha), -, -⟩
    · rw [h2 hph2] at Hf; cases Hf
    iexact Ha
  exfalso
  by_cases hph0 : dv.phase = W64 0
  · exact (h0 hph0).2 hl
  apply h3
  unfold swift.phCOMMIT
  apply BitVec.eq_of_toNat_eq
  have e0 : dv.phase.toNat ≠ 0 := fun e => hph0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  have e1 : dv.phase.toNat ≠ 1 := fun e => hph1 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  have e2 : dv.phase.toNat ≠ 2 := fun e => hph2 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  have e3 : dv.phase.toNat ≤ 3 := hle
  show dv.phase.toNat = 3
  omega

/-- **The owner state opened for `deliver`** (round 33; Path D of table rev 4 §3.6): with the
`OptCondF` part `ocfRes`, the owner's whole state is `deliver`'s frame `Rs` (the slot frees it):
its epoch share and reader, the reply channel's object, the fields `descF`, the commit fact,
why it may execute (`execWhy`) and the slot's capability over `Rs` (`slotOk`, from `descOwn`'s
`slotCap`), the kept parts `Rk` (`status`, `FQ`); back from the same parts, or (the
descriptor retired) `descGone` from `x` executed and the slot's residue. -/
theorem swift.descOwn_deliver (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    [hRC : ∀ l bw, Persistent (RC l bw)]
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) (cf : Loc) (cond : GoFunc) (fs : List GoFunc) (v : Bool) :
    swift.descOwn c RC MP γd d x b Do ∗ swift.ocfRes d cf cond fs v ⊢
      ∃ (q : Qp) (bw : w32) (stp rcp : Loc) (dv : swift.DescV) (Rs Rk : IProp netDistGF),
        swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗ swift.ownRdr c.rp c.γdl ∗
        swift.epochPinQ c.γxp q b ∗
        RC rcp bw ∗ □ swift.slotB MP c.γxm b x ∗ swift.descF d γd MP dv ∗ Rs ∗ Rk ∗
        (if decide (dv.phase = swift.phCOMMIT ∧ dv.propose ≠ null) then
          sp.committed c.γ c.r b (toCmdId x) else True) ∗
        swift.execWhy c.γ c.γxm c.N c.r b x dv ∗
        swift.repPre c.γ c.N c.r b x dv ∗ swift.tixD c.γxu c.γxm b x dv ∗
        (⌜dv.seq = false⌝ ∨ swift.slotOk MP γd c.γxm c.rp d b x dv Rs
          iprop(⌜c.sq = true⌝ ∗ c.ret d x ∗ c.env d q)) ∗
        (swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp -∗ swift.ownRdr c.rp c.γdl -∗
          swift.epochPinQ c.γxp q b -∗ swift.descF d γd MP dv -∗ Rs -∗
          swift.tixD c.γxu c.γxm b x dv -∗ Rk -∗
          swift.descOwn c RC MP γd d x b Do ∗ swift.ocfRes d cf cond fs v) ∗
        (swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp -∗ swift.ownRdr c.rp c.γdl -∗
          swift.epochPinQ c.γxp q b -∗ Rk -∗
          swift.exIn c.γxm b x -∗ (⌜c.sq = true⌝ ∗ c.ret d x ∗ c.env d q) -∗
          swift.descGone c b x d) := by
  iintro ⟨Hown, Hocf⟩
  iunfold swift.descOwn at Hown
  icases Hown with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF, HdS, HR⟩
  iunfold swift.setR at HR
  iunfold swift.descSt at HR
  icases HR with ⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, #HRC, Hd, Htok, #Hcom, ⟨#Hra, #Hrep⟩, %Hph,
    #Hpw, #Hdw, %Hrp, #HsB, ⟨HsF, HfF, HdF, HDo⟩⟩
  iunfold swift.shOwn at Hsh
  icases Hsh with ⟨Hshe, HshR⟩
  iunfold swift.shOwnR at HshR
  icases HshR with ⟨Hst, HFQ, HrdR, Henv, Hpin⟩
  ihave Hcf : iprop(if decide (dv.phase = swift.phCOMMIT ∧ dv.propose ≠ null) then
      sp.committed c.γ c.r b (toCmdId x) else True) $$ []
  · by_cases h : dv.phase = swift.phCOMMIT ∧ dv.propose ≠ null
    · rw [decide_eq_true h]; simp only [↓reduceIte]
      icases Hcom with (%h' | #Hc)
      · exfalso
        rcases Hph h.1 with h2 | h2
        · rw [h2] at h'; cases h'
        · exact h.2 h2
      · iexact Hc
    · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  ihave #Hwhy := swift.execWhy_of c b x dv rv Hrp.1 $$ [Hpw Hdw Hra]
  · iframe Hpw Hdw Hra
  ihave ⟨Htix, Htokw⟩ := swift.rowTokO_tix c b x dv rv $$ Htok
  ihave #HcapR := swift.slotCap_R c MP γd d x b Do s
    iprop(swift.dfld d go!"slowPathH" ↦ s ∗ swift.dfld d go!"fastPathH" ↦ f ∗
      replica.mset.ownD (if (true : Bool) then f else s) qF szF memF (swift.ackP x) swift.ackA
        (swift.leadAckP c b x) iprop(True) hd ∗ iprop(Do ∗ swift.ocfRes d cf cond fs v))
      (by
        iintro ⟨⟨Hs, Hf, HdO, HD0, Ho⟩, Hms⟩
        iexists s, f, cf, cond, fs, v
        iframe Hs Hf Hms Ho HD0
        simp only [↓reduceIte]
        iapply swift.msetF_of $$ HdO) $$ HhF
  ihave Hsl := swift.slotCapR_slotOkT c MP γd d x b s
    iprop(swift.dfld d go!"slowPathH" ↦ s ∗ swift.dfld d go!"fastPathH" ↦ f ∗
      replica.mset.ownD (if (true : Bool) then f else s) qF szF memF (swift.ackP x) swift.ackA
        (swift.leadAckP c b x) iprop(True) hd ∗ iprop(Do ∗ swift.ocfRes d cf cond fs v))
    (replica.mset.ownD s qS szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd)
    dv rv qe Hrp.2 (swift.msetF_of _ _ _ _ _ _ _ _) $$ HcapR
  iexists qe, bw, stp, rcp, dv,
    iprop((swift.dfld d go!"slowPathH" ↦ s ∗ swift.dfld d go!"fastPathH" ↦ f ∗
      replica.mset.ownD (if (true : Bool) then f else s) qF szF memF (swift.ackP x) swift.ackA
        (swift.leadAckP c b x) iprop(True) hd ∗ iprop(Do ∗ swift.ocfRes d cf cond fs v)) ∗
      replica.mset.ownD s qS szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd ∗
      (swift.tixD c.γxu c.γxm b x dv -∗ swift.rowTokO c b x dv rv) ∗
      ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) qe ∗ c.env d qe),
    iprop((∃ st : w64, typedPointsto (swift.fld c.rp go!"status") st (DFrac.own qe)) ∗
      (∃ (fq : GoInterface) (szF : Nat) (memF : w32 → Prop),
        typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own qe) ∗ replica.mset.quorumIs fq szF memF ∗
        ⌜(∀ i : w32, memF i → sp.rid i ∈ sp.AQ c.N b) ∧
          (∀ i : w32, 0 ≤ sint.Z i → sp.rid i = sp.leaderOf c.N b → memF i)⌝))
  iframe Hrd HrdR HRC HsB Hd Hcf Hwhy Hsl Hst HFQ Hrep Htix
  isplitl [Hpin]
  · iunfold swift.epochPinQ; iexact Hpin
  isplitl [HsF HfF HdF HDo Hocf HdS Htokw Hshe Henv]
  · iframe HsF HfF HdF HDo Hocf HdS Htokw Hshe Henv
  isplitr
  · iintro Hrd HrdR Hpin Hd ⟨⟨HsF, HfF, HdF, HDo, Hocf⟩, HdS, Htokw, Hshe, Henv⟩ Htix ⟨Hst, HFQ⟩
    ihave Htok := Htokw $$ Htix
    iunfold swift.epochPinQ at Hpin
    iframe Hocf
    iunfold swift.descOwn
    iexists s, f, qS, qF, szS, szF, memS, memF, hd
    iframe HhS HhF HdS
    iunfold swift.setR
    iunfold swift.descSt
    iexists qe, bw, stp, rcp, dv, rv
    iframe Hrd HRC Hd Htok Hcom Hra Hrep HsF HfF HdF HDo Hpw Hdw HsB
    isplitl [Hshe Hst HFQ HrdR Henv Hpin]
    · iunfold swift.shOwn; iframe Hshe; iunfold swift.shOwnR; iframe Hst HFQ HrdR Henv Hpin
    isplitr
    · ipureintro; exact Hph
    ipureintro; exact Hrp
  iintro Hrd HrdR Hpin ⟨Hst, HFQ⟩ #Hex ⟨%Hsq, Hret, Henv⟩
  iunfold swift.epochPinQ at Hpin
  iunfold swift.descGone
  iframe Hex Hret
  isplitr
  · ipureintro; exact Hsq
  iexists qe, bw, stp, rcp
  iframe Hrd
  iunfold swift.shOwnR; iframe Hst HFQ HrdR Henv Hpin

end proof

end Perennial.github_com.imdea_software.swiftpaxos
