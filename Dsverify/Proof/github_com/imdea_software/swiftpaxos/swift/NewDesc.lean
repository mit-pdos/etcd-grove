/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/NewDesc.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.newDesc()` (swift.go:895; round 22, sv-swb; notes/prove-swift.md §28): a descriptor from
`allocDesc` (at rest: `descPooled (descDFA γsh)`) with every field `newDesc` writes at its new
value (`swift.descNew`): `dep`/`hs`/`storedBallots`/`propose`/`proposeDep`/`waitingAck` nil
(P12), `phase = START`, `active`, `slowPath = false`, `seq` some `s`, a no-op `defered`, fresh
`msgs`/`stopChan` channels with the caller's bags (`MP`, `SP d sc`), `afterPropagate` an
`OptCondF` with an empty store and the condition `desc.propose != nil` (`condOk … proposeHalf`),
the two message sets (slow over `SQ`, fast over `FQ`) with one handler `hd` (`acksHdOk`: its
spec at any frame, so the spawn states the sets' lent states, which mention each other).
`successors` is reset under `successorsL` (its mutex is kept by the share map's invariant and
by the descriptor at rest). The share map's element whole, `cmd` as at rest.

The accept closure reads both acks' `Dep` slices: `ackP`/`leadAckP` carry them read-only
(SWB-16, D18; round 23): `acceptOk` over `Dep.Equals.specAnyV`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AllocDesc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcksSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunCtx
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepEqualsV

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [hook.Assumptions]

/-- A closure that does nothing (`func() {}`): any state is kept. -/
def swift.nopOk (f : GoFunc) : IProp netDistGF :=
  iprop(∀ (P : IProp netDistGF), {{ P }} (App (Val #f) (Val #())) {{ RET #(); P }})

/-- **A descriptor as `newDesc` leaves it** (see the file header), for `x` in epoch `b` (the
handler's and the sets' predicates), its message channel's predicate `MP`, its stop channel's
`SP d sc`, the slow quorum `sq` and the fast one `fq`. -/
def swift.descNew (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (SP : Loc → Loc → Loc → IProp netDistGF) (γsh : GName) (x : swift.CommandId) (b : Nat)
    (sq fq : GoInterface) (szS szF : Nat) (memS memF : w32 → Prop) (d : Loc) : IProp netDistGF :=
  iprop(∃ (s : Bool) (γm γs : ChanNames) (m sc cf sl fa : Loc) (cond df hd : GoFunc) (q : Qp)
      (cc : sp.Cmd) (vs : GoSlice) (sn : w64),
    ghostMapElem γsh d (DFrac.own 1) q ∗
    sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d) ∗
    swift.dfld d go!"cmd" ↦ state.Command.mk cc.op cc.key vs ∗ vs ↦*□ cc.val ∗ ⌜cc.op ≠ W8 3⌝ ∗
    swift.dfld d go!"dep" ↦ slice.nil ∗ swift.dfld d go!"hs" ↦ slice.nil ∗
    swift.dfld d go!"seqnum" ↦ sn ∗
    swift.dfld d go!"msgs" ↦ m ∗ isChanBag γm m MP ∗
    swift.dfld d go!"active" ↦ true ∗ swift.dfld d go!"phase" ↦ (W64 0) ∗
    swift.dfld d go!"slowPath" ↦ false ∗ swift.dfld d go!"seq" ↦ s ∗
    swift.dfld d go!"defered" ↦ df ∗ □ swift.nopOk df ∗
    swift.dfld d go!"storedBallots" ↦ slice.nil ∗ swift.dfld d go!"propose" ↦ null ∗
    swift.dfld d go!"proposeDep" ↦ slice.nil ∗ swift.dfld d go!"waitingAck" ↦ null ∗
    swift.dfld d go!"stopChan" ↦ sc ∗ isChanBag γs sc (SP d sc) ∗
    swift.dfld d go!"afterPropagate" ↦ cf ∗ hook.ocf.ownOcf cf cond [] ∗
    □ hook.ocf.condOk cond (swift.proposeHalf d) ∗
    swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
    replica.mset.ownD sl sq szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd ∗
    replica.mset.ownD fa fq szF memF (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd ∗
    swift.acksHdOkB c RC MP γm d x b hd)

/-- **`descNew` without the fields the spawn splits** (round 27, sv-swb): `msgs`, `active`, `seq`,
`stopChan` (shared between the descriptor's owner and its `cmdDescs` entry), their bags, and the
share map's element (updated to the goroutine's loan): every other field as `newDesc` left it,
at the `msgs` channel's names `γm` (the handler's spec mentions them). -/
def swift.descRaw (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (x : swift.CommandId) (b : Nat) (sq fq : GoInterface) (szS szF : Nat) (memS memF : w32 → Prop)
    (γm : ChanNames) (d : Loc) : IProp netDistGF :=
  iprop(∃ (cf sl fa : Loc) (cond df hd : GoFunc) (cc : sp.Cmd) (vs : GoSlice) (sn : w64),
    sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d) ∗
    swift.dfld d go!"cmd" ↦ state.Command.mk cc.op cc.key vs ∗ vs ↦*□ cc.val ∗ ⌜cc.op ≠ W8 3⌝ ∗
    swift.dfld d go!"dep" ↦ slice.nil ∗ swift.dfld d go!"hs" ↦ slice.nil ∗
    swift.dfld d go!"seqnum" ↦ sn ∗
    swift.dfld d go!"phase" ↦ (W64 0) ∗
    swift.dfld d go!"slowPath" ↦ false ∗
    swift.dfld d go!"defered" ↦ df ∗ □ swift.nopOk df ∗
    swift.dfld d go!"storedBallots" ↦ slice.nil ∗ swift.dfld d go!"propose" ↦ null ∗
    swift.dfld d go!"proposeDep" ↦ slice.nil ∗ swift.dfld d go!"waitingAck" ↦ null ∗
    swift.dfld d go!"afterPropagate" ↦ cf ∗ hook.ocf.ownOcf cf cond [] ∗
    □ hook.ocf.condOk cond (swift.proposeHalf d) ∗
    swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
    replica.mset.ownD sl sq szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd ∗
    replica.mset.ownD fa fq szF memF (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd ∗
    swift.acksHdOkB c RC MP γm d x b hd)

end defs

section split
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [hook.Assumptions]

/-- `descNew` split for the spawn (round 27): the four shared fields, their bags, the share map's
element, and `descRaw`. -/
theorem swift.descNew_split (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (SP : Loc → Loc → Loc → IProp netDistGF) (γsh : GName)
    (x : swift.CommandId) (b : Nat) (sq fq : GoInterface) (szS szF : Nat) (memS memF : w32 → Prop)
    (d : Loc) :
    swift.descNew c RC MP SP γsh x b sq fq szS szF memS memF d ⊢
    ∃ (s : Bool) (γm γs : ChanNames) (m sc : Loc) (q : Qp),
      swift.dfld d go!"msgs" ↦ m ∗ isChanBag γm m MP ∗
      swift.dfld d go!"active" ↦ true ∗ swift.dfld d go!"seq" ↦ s ∗
      swift.dfld d go!"stopChan" ↦ sc ∗ isChanBag γs sc (SP d sc) ∗
      ghostMapElem γsh d (DFrac.own 1) q ∗
      swift.descRaw c RC MP x b sq fq szS szF memS memF γm d := by
  iunfold swift.descNew
  iintro ⟨%s, %γm, %γs, %m, %sc, %cf, %sl, %fa, %cond, %df, %hd, %q, %cc, %vs, %sn, He, #Hmx,
    Hcmd, #Hvs, %Hop, Hdep, Hhs, Hsn, Hm, #Hmb, Ha, Hph, Hslw, Hseq, Hdf, #Hnop, Hsb, Hp, Hpd, Hwa,
    Hsc, #Hsb2, Hap, Hocf, #Hcond, Hsl, Hfa, Hsls, Hfas, #Hhd⟩
  iexists s, γm, γs, m, sc, q
  iframe Hm Hmb Ha Hseq Hsc Hsb2 He
  iunfold swift.descRaw
  iexists cf, sl, fa, cond, df, hd, cc, vs, sn
  iframe
  iframe Hmx Hvs Hnop Hcond Hhd
  ipureintro; exact Hop

/-- The new descriptor's `successorsL` mutex (persistent) out of `descRaw` (round O1: `depSpecR`'s
post for a created descriptor; round 46, D60 O1-a: `descR`'s mutex). -/
theorem swift.descRaw_mutex (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (y : swift.CommandId) (b : Nat) (sq fq : GoInterface)
    (szS szF : Nat) (memS memF : w32 → Prop) (γm : ChanNames) (d : Loc) :
    swift.descRaw c RC MP y b sq fq szS szF memS memF γm d ⊢
      swift.descRaw c RC MP y b sq fq szS szF memS memF γm d ∗
        sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d) := by
  iunfold swift.descRaw
  iintro ⟨%cf, %sl, %fa, %cond, %df, %hd, %cc, %vs, %sn, #Hmx, H⟩
  isplitl [H]
  · iexists cf, sl, fa, cond, df, hd, cc, vs, sn
    isplitr
    · iexact Hmx
    iexact H
  iexact Hmx

end split

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [hook.Assumptions]

/-- **The message predicates `deliver` accepts** (round 39, D43 (5)): an `int` payload is a
`w64` (`deliver.wp_proof`'s `hMPty`). The descriptors' `MPi g y γi` satisfy it
(`swift.mpOk_ty`, GetDescWith.lean). -/
def swift.mpTy (MP : GoInterface → IProp netDistGF) : Prop :=
  ∀ m, MP m ⊢ ⌜∀ ii : GoInterfaceOk, m = GoInterface.ok ii → ii.ty = go.int → ∃ s : w64, ii.v = #s⌝

/-- `getFastAndSlowAcksHandler.specI` at one record `c` (round 39, D43 (5)): what `newDesc` needs
of the handler at the record it is called with; `specI RC MP` is `∀ c, specIc c RC MP`. The
linked proof (`getFastAndSlowAcksHandler.wp_proofS`, AcksHandler.lean) holds at the records of
the replica's `str`, the only ones whose `deliver` is proved. -/
abbrev swift.getFastAndSlowAcksHandler.specIc (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) : Prop :=
  ∀ (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx }}
    (App (App (Val (@! swift.getFastAndSlowAcksHandler)) (Val #c.rp)) (Val #d))
  {{ (hd : GoFunc), RET #hd; swift.acksHdOkB c RC MP γd d x b hd }}

/-- **`r.newDesc()` at one record `c`** (round 39, D43 (5)): `specN RC MP` is `∀ c, specNc c RC MP`.
The creators call it at the replica's kind-free record `x.dc …` (table §3R9.7 T2). -/
abbrev swift.Replica.newDesc.specNc (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) : Prop :=
  ∀ (SP : Loc → Loc → Loc → IProp netDistGF) (γsh : GName) (x : swift.CommandId)
    (b : Nat) (dm : GoSlice) (γdl γn : GName) (D : w64) (sq fq : GoInterface) (szS szF : Nat)
    (memS memF : w32 → Prop) (qf : Qp),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ swift.descPoolCtx (swift.descDFA γsh) c.rp ∗ inv swift.shN (swift.shInv γsh) ∗
      sync.isMutex (swift.fld c.rp go!"cntL") (swift.cntLInvR c.rp dm γdl γn D) ∗
      globalAddr swift.MaxDescRoutines ↦□ D ∗
      swift.fld c.rp go!"SQ" ↦□ sq ∗ replica.mset.quorumIs sq szS memS ∗
      typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own qf) ∗ replica.mset.quorumIs fq szF memF }}
    (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"newDesc")) (Val #()))
  {{ (d : Loc), RET #d; swift.descNew c RC MP SP γsh x b sq fq szS szF memS memF d ∗
      typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own qf) }}

/-- **`r.newDesc()`** (see the file header): over the descriptor pool and the share map, `cntL`
(it reads `routineCount`), `SQ` (read-only) and a read share of `FQ` (given back). -/
abbrev swift.Replica.newDesc.specN (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) : Prop :=
  ∀ (c : swift.DC) (SP : Loc → Loc → Loc → IProp netDistGF) (γsh : GName) (x : swift.CommandId)
    (b : Nat) (dm : GoSlice) (γdl γn : GName) (D : w64) (sq fq : GoInterface) (szS szF : Nat)
    (memS memF : w32 → Prop) (qf : Qp),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ swift.descPoolCtx (swift.descDFA γsh) c.rp ∗ inv swift.shN (swift.shInv γsh) ∗
      sync.isMutex (swift.fld c.rp go!"cntL") (swift.cntLInvR c.rp dm γdl γn D) ∗
      globalAddr swift.MaxDescRoutines ↦□ D ∗
      swift.fld c.rp go!"SQ" ↦□ sq ∗ replica.mset.quorumIs sq szS memS ∗
      typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own qf) ∗ replica.mset.quorumIs fq szF memF }}
    (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"newDesc")) (Val #()))
  {{ (d : Loc), RET #d; swift.descNew c RC MP SP γsh x b sq fq szS szF memS memF d ∗
      typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own qf) }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [hook.Assumptions] [replica.Assumptions] [sync.Assumptions]

set_option goose.wp.extras true

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [replica.Assumptions] [sync.Assumptions] [swift.Assumptions] [hook.Assumptions] in
/-- `ocfAny` as `ReinitCondF`'s precondition. -/
theorem swift.ocfAny_ex (cf : Loc) :
    swift.ocfAny cf ⊢ ∃ (cond0 : GoFunc) (fs : List GoFunc), ⌜cf = null⌝ ∨ hook.ocf.ownOcf cf cond0 fs := by
  iunfold swift.ocfAny
  iintro (%h | ⟨%cond, %fs, %sl, %L, H⟩)
  · iexists func.nil, []; ileft; ipureintro; exact h
  · iexists cond, fs; iright; iunfold hook.ocf.ownOcf; iexists sl, L; iexact H

set_option hygiene false in
/-- The accept closure (`acceptFastAndSlowAck`): any Boolean is safe (`ackA` is `True`); it reads
both acks' `Dep` slices (read-only by `ackP`/`leadAckP`, SWB-16). -/
macro "acceptProof" : tactic => `(tactic| (
  iunfold replica.mset.acceptOk; imodintro; iintro %k %m %lm; imodintro
  iintro %Ψ ⟨HR, #HP, #HL⟩ HΨ
  wp_auto
  iunfold replica.mset.leaderOk at HL
  icases HL with (%Hn | #HL)
  · subst Hn
    try wp_auto
    iapply HΨ; iframe HR; iintro -; iunfold replica.mset.accOk; ileft; ipureintro; rfl
  iunfold swift.leadAckP at HL
  icases HL with ⟨%l1, %fa1, ⟨%Hlm, -⟩, #Hl1, ⟨%D1, #HD1⟩, -⟩
  iunfold swift.ackP at HP
  icases HP with ⟨%l2, %fa2, ⟨%Hm, -⟩, #Hl2, ⟨%D2, #HD2⟩⟩
  subst Hlm Hm
  ihave #Hf1 := Hl1
  iStructNamedSuffix Hf1 "1"
  ihave #Hf2 := Hl2
  iStructNamedSuffix Hf2 "2"
  wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΨ; iframe HR; iintro -; iunfold replica.mset.accOk; iright; iunfold swift.ackA; imodintro; itrivial
  · wp_apply wp_eqV $$ [HD1 HD2] as %bb -
    · iframe HD1 HD2
    iapply HΨ; iframe HR; iintro -; iunfold replica.mset.accOk; iright; iunfold swift.ackA; imodintro; itrivial))

/-- `newDesc` at one record `c` (round 39, D43 (5)), from the handler's spec at `c`. -/
theorem swift.Replica.newDesc.wp_proofc (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF)
    (wp_alloc : swift.Replica.allocDesc.specA (hG := hG))
    (wp_hd : swift.getFastAndSlowAcksHandler.specIc c RC MP)
    (wp_RCF : hook.ocf.OptCondF.ReinitCondF.specI (hG := hG))
    (wp_RMS : replica.mset.MsgSet.ReinitMsgSet.specD (hG := hG))
    (wp_eqV : swift.Dep.Equals.specAnyV (hG := hG)) :
    swift.Replica.newDesc.specNc c RC MP := by
  intro SP γsh x b dm γdl γn D sq fq szS szF memS memF qf
  wp_start as ⟨#Hctx, #Hpool, #Hsh, #HcntL, #HD, #HSQ, #HqS, HFQ, #HqF⟩
  wp_auto
  wp_apply wp_alloc $$ [$Hpool $Hsh] as %d Hd
  iunfold swift.descPooled at Hd
  icases Hd with ⟨%m0, %s0, %sl0, %fa0, Hm0, Hs0, Hsl0, Hfa0, Hsl0a, Hfa0a, Hdf⟩
  simp only [swift.descDFA]
  iunfold swift.descDF at Hdf
  icases Hdf with ⟨%a0, %q0, Ha0, Hq0, -, Hr⟩
  iunfold swift.descRestA at Hr
  icases Hr with ⟨%qs, %ph, %sn, %cc, %vs, %dep, %hs, %pd, %sb, %p, %ap, %wa, %slw, %df, He, #Hmx, Hph,
    Hcmd, #Hvs, %Hop, Hdep, Hhs, Hsn, Hp, Hpd, Hap, Hapa, Hslw, Hdfr, Hwa, Hsb⟩
  wp_auto
  wp_apply chan.wp_make2 (V := GoInterface) (W64 8) as %mc %γm ⟨#Hmc, %Hmcap, Hmown⟩
  · ipureintro; decide
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmx] as ⟨Hlk, HS⟩
  iunfold swift.succInv at HS
  icases HS with ⟨%ssl, %sll, Hsucc, -, -⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmx $Hlk Hsucc]
  · iunfold swift.succInv
    iexists slice.nil, []
    iframe Hsucc
    isplitr
    · iapply (ownSlice_nil (V := swift.CommandId) (DFrac.own 1))
    · iapply ownSliceCap_nil
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$HcntL] as ⟨Hclk, HC⟩
  iunfold swift.cntLInvR at HC
  icases HC with ⟨%n, %cnt, %T, Hn, Hcnt, HG⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hclk Hn Hcnt HG]
  · iunfold swift.cntLInvR
    iexists n, cnt, T
    iframe Hn Hcnt HG
  try wp_auto
  wp_apply chan.wp_make2 (V := Loc) (W64 8) as %sc %γs ⟨#Hsc, %Hsccap, Hsown⟩
  · ipureintro; decide
  iapply fupd_wp
  imod start_bag MP (ChanState.Buffered []) mc γm (by trivial) $$ [$Hmc] [Hmown] with #Hbm
  · iexact Hmown
  imod start_bag (SP d sc) (ChanState.Buffered []) sc γs (by trivial) $$ [$Hsc] [Hsown] with #Hbs
  · iexact Hsown
  imodintro
  try wp_auto
  ipersist desc
  ihave ⟨%cond0, %fs0, Hocf0⟩ := swift.ocfAny_ex $$ Hapa
  wp_apply wp_RCF $$ [Hocf0] as %cf Hocf
  · iframe Hocf0
  try wp_auto
  ipersist acceptFastAndSlowAck
  ipersist freeFastAck
  wp_apply (wp_hd γm d x b) $$ [$Hctx] as %hd #Hhd
  try wp_auto
  iunfold swift.msetAny at Hsl0a
  wp_apply (wp_RMS sl0 sq szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True))
    $$ [Hsl0a] as %sl Hsl
  · iframe Hsl0a HqS
    isplitr
    · acceptProof
    · iunfold replica.mset.freeOk; imodintro; iintro %m; imodintro
      iintro %Ψ ⟨HR, -⟩ HΨ; wp_auto; iapply HΨ; iexact HR
  try wp_auto
  iunfold swift.msetAny at Hfa0a
  wp_apply (wp_RMS fa0 fq szF memF (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True))
    $$ [Hfa0a] as %fa Hfa
  · iframe Hfa0a HqF
    isplitr
    · acceptProof
    · iunfold replica.mset.freeOk; imodintro; iintro %m; imodintro
      iintro %Ψ ⟨HR, -⟩ HΨ; wp_auto; iapply HΨ; iexact HR
  iapply HΦ
  iframe HFQ
  iunfold swift.descNew
  iexists _, γm, γs, mc, sc, cf, sl, fa, _, _, hd, qs, cc, vs, _
  iframe He Hmx Hcmd Hvs Hdep Hhs Hsn Hm0 Hbm Ha0 Hph Hslw Hq0 Hdfr Hsb Hp Hpd Hwa Hs0 Hbs Hap Hocf
  iframe Hsl0 Hfa0 Hsl Hfa Hhd
  isplitr
  · ipureintro; exact Hop
  isplitr
  · iunfold swift.nopOk; imodintro; iintro %P; imodintro
    iintro %Ψ HP HΨ; wp_auto; iapply HΨ; iexact HP
  iunfold hook.ocf.condOk; imodintro; iintro %v; imodintro
  iintro %Ψ Hph HΨ
  iunfold swift.proposeHalf at Hph
  icases Hph with ⟨%pp, Hpp, %Hv⟩
  wp_auto
  have hv : (!decide (pp = null)) = v := by rw [← Hv]; by_cases h : pp = null <;> simp [h]
  rw [hv]
  iapply HΨ
  iunfold swift.proposeHalf
  iexists pp; iframe Hpp; ipureintro; exact Hv

theorem swift.Replica.newDesc.wp_proof (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF)
    (wp_alloc : swift.Replica.allocDesc.specA (hG := hG))
    (wp_hd : swift.getFastAndSlowAcksHandler.specI RC MP)
    (wp_RCF : hook.ocf.OptCondF.ReinitCondF.specI (hG := hG))
    (wp_RMS : replica.mset.MsgSet.ReinitMsgSet.specD (hG := hG))
    (wp_eqV : swift.Dep.Equals.specAnyV (hG := hG)) :
    swift.Replica.newDesc.specN RC MP := fun c =>
  swift.Replica.newDesc.wp_proofc c RC MP wp_alloc (wp_hd c) wp_RCF wp_RMS wp_eqV
