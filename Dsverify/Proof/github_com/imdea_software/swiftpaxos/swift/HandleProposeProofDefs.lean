/-
The definitions, specs and lemmas of `HandleProposeProof.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GhostSteps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleProposeDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ProposePure
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.PoolFnsDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.BatcherFastDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.IdBound
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Store

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS] [sp.GobFmt]
variable [swift.Assumptions]

theorem swift.pt_halves {V : Type} [TypedPointsto (GF := netDistGF) V] (l : Loc) (v : V) :
    (typedPointsto (V := V) l v (DFrac.own 1) : IProp netDistGF) ⊣⊢
      (typedPointsto (V := V) l v (DFrac.own (1 : Qp).half) ∗
        typedPointsto (V := V) l v (DFrac.own (1 : Qp).half)) := by
  have h : (DFrac.own 1 : DFrac) = DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half := by
    rw [DFrac.op_own, Qp.half_add_half]
  rw [h]
  exact (typedPointsto_dfractional (GF := netDistGF) l v).dfractional _ _

/-- **A claim refutes a held token of its key** (round 47, 46-2): the store holds the token of a
claimed key (`storeOk_take`'s `Rt K = some _`), and row tokens are exclusive. -/
theorem swift.claim_rowTok_false (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat)
    (K : Nat × sp.CmdId) (ck : swift.ClK) (rv : swift.RowV) :
    inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗ swift.claimTok sn.γcl K ck ∗
      swift.rowTok γo K.1 K.2 rv ⊢ |={⊤}=> (False : IProp netDistGF) := by
  iintro ⟨#HN, Hcl, Htok⟩
  iinv HN with Hn Hclose
  iunfold swift.nodeInvD at Hn
  imod Hn
  icases Hn with ⟨%st, %O, Hstn, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  iunfold swift.storeD at HS
  icases HS with ⟨%Rt, %Out, %Cl, %U, Ha, Hc, Hm, Hu, %h, %hU⟩
  iunfold swift.claimTok at Hcl
  ihave %Hl := ghost_map_lookup $$ Hc Hcl
  obtain ⟨-, -, hR⟩ := swift.storeOk_take st.cballot O Rt Out Cl K ck (0, 1) h Hl
  icases (BigSepM.bigSepM_delete (show PartialMap.get? Rt K = some (swift.recOf ck) from hR)).1
    $$ Hm with ⟨⟨%rv', Htok', -, -⟩, -⟩
  iunfold swift.rowTok at Htok Htok'
  icombine Htok Htok' gives %Hv
  exfalso; have := DFrac.valid_own_op Hv.1; simp at this

/-- A command of a `locLb` is the registered one (round 47). -/
theorem swift.locLb_cmd_agree (γ : sp.Names) (r b : Nat) (s : sp.Seq) (y : sp.CmdId) (c c' : sp.Cmd)
    (h : (y, c') ∈ s) : sp.locLb γ r b s ∗ sp.cmdIs γ y c ⊢ (⌜c = c'⌝ : IProp netDistGF) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  unfold sp.locLb
  iintro ⟨H1, #Hc⟩
  ihave ⟨-, #Hc1⟩ := BigSepL.bigSepL_lookup hi $$ H1
  iapply sp.cmdIs_agree
  isplitr
  · iexact Hc
  iexact Hc1

/-- **The reply facts of a proposal** (round 47, 46-2, D61 (2); `descSt`'s `repPre` at
`handlePropose`): the proposal read-only with its client id, the message's hash `H` of the path
`P` (`startHash`), and at the leader its `pathIs` and its sequence `s` (`locLb`) with `x` and its
dependencies. -/
theorem swift.repPre_prop (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (pp w mu : Loc) (addr : GoString) (H : swift.SHash) (P : List sp.CmdId) (s : sp.Seq)
    (hHs : dv.Hs = [H]) (hwf : dv.c.wf) (hD : dv.D.length < 2 ^ 62)
    (hlast : P.getLast? = some (toCmdId x)) (hcl : (toCmdId x).cl ≠ -1)
    (hs : r = sp.leaderOf N b →
      (toCmdId x, dv.c) ∈ s ∧ (dv.D.map toCmdId).Perm (sp.depsIn s (toCmdId x))) :
    dv.propose ↦□ replica.defs.GPropose.mk pp w mu false addr ∗
      typedPointsto (pp.[replica.defs.Propose, go!"ClientId"]) x.ClientId' DFrac.discard ∗
      sp.startHash P H.H'.arr ∗
      (⌜r ≠ sp.leaderOf N b⌝ ∨ sp.pathIs γ r b (toCmdId x) P ∗ sp.locLb γ r b s) ∗
      swift.propIs γ dv.propose (toCmdId x) dv.c ⊢
    swift.repPre γ N r b x dv := by
  iintro ⟨#Hg, #Hcl, #Hsh, #Hl, #HpI⟩
  ihave %Hlen := sp.startHash_len P H.H'.arr $$ Hsh
  have hsh : swift.handler.shashOf H.H'.arr = H := by cases H; rfl
  iunfold swift.repPre
  iright
  isplitr
  · iunfold swift.replyPre
    iexists [H.H'.arr], pp, w, mu, addr
    iframe Hg Hcl
    isplitr
    · ipureintro
      refine ⟨by rw [hHs]; simp [hsh], ⟨by simp, fun h hh => ?_⟩, by simp, hD⟩
      simp at hh; subst hh; exact Hlen
    icases Hl with (%Hn | ⟨#Hp, -⟩)
    · ileft; ipureintro; exact Hn
    iright
    iexists [P]
    isplitr
    · iunfold sp.pathHashes
      isplitr
      · ipureintro
        refine ⟨rfl, fun P' hP' => ?_⟩
        simp at hP'; subst hP'
        rw [List.getLast?_eq_some_iff] at hlast
        obtain ⟨Q, hQ⟩ := hlast
        exact ⟨Q, toCmdId x, hQ, hcl⟩
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iexists H.H'.arr; iframe Hsh; ipureintro; rfl
      iapply BigSepL.bigSepL_nil.2; itrivial
    iright; iexists P; iframe Hp; ipureintro; rfl
  isplitr
  · ipureintro; exact hwf
  iframe HpI
  iunfold swift.ldrPrefix
  icases Hl with (%Hn | ⟨-, #Hlb⟩)
  · ileft; ipureintro; exact Hn
  by_cases hl : r = sp.leaderOf N b
  · iright; iexists s; iframe Hlb; ipureintro; exact hs hl
  · ileft; ipureintro; exact hl

/-- A set proposal (the condition's half `p ≠ null`) is a read-only `*GPropose` (`rowAcc`). -/
theorem swift.descOwn_propose (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) (p : Loc) (hp : p ≠ null) :
    swift.descOwn c RC MP γd d x b Do ∗
      typedPointsto (swift.dfld d go!"propose") p (DFrac.own (1 : Qp).half) ⊢
      swift.descOwn c RC MP γd d x b Do ∗
      typedPointsto (swift.dfld d go!"propose") p (DFrac.own (1 : Qp).half) ∗
      ∃ gv : replica.defs.GPropose, p ↦□ gv := by
  unfold swift.descOwn
  iintro ⟨⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF, HdS, HR⟩,
    Hp⟩
  iunfold swift.setR at HR
  iunfold swift.descSt at HR
  icases HR with ⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, ⟨#Hra, #HrP⟩, %Hph, #Hpw,
    #Hdw, %Hrp, #HsB, HRs⟩
  iunfold swift.descF at Hd
  icases Hd with ⟨Hph', Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hprop, Hseq, Hmsgs, #Hmb, #HsL, %Hop⟩
  icombine Hprop Hp gives %Heq
  ihave #Hra2 := Hra
  iunfold swift.rowAcc at Hra2
  icases Hra2 with ⟨-, -, (%Hn | #Hg)⟩
  · exfalso; exact hp (Heq ▸ Hn)
  iframe Hp
  isplitr [Hg]
  rotate_left
  · rw [← Heq]; iexact Hg
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe HhS HhF HdS
  iunfold swift.setR
  iunfold swift.descSt
  iexists qe, bw, stp, rcp, dv, rv
  iframe Hsh Hrd HRC Htok Hcom HRs Hra HrP Hpw Hdw HsB
  isplitl
  · iunfold swift.descF
    iframe Hph' Hcmd Hvs Hdep HD Hhs HHs Hprop Hseq Hmsgs Hmb HsL
    ipureintro; exact Hop
  isplitr
  · ipureintro; exact Hph
  ipureintro; exact Hrp

/-- `shOwn_open` with `shOwnR`'s whole pure fact (E7: the leader is in `FQ`; round 33). -/
theorem swift.shOwn_openE (c : swift.DC) (d : Loc) (b : Nat) (q : Qp) :
    swift.shOwn c d b q ⊢
      ∃ (st : w64) (fq : GoInterface) (szF : Nat) (memF : w32 → Prop),
        typedPointsto (swift.fld c.rp go!"status") st (DFrac.own q) ∗
        typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own q) ∗
        replica.mset.quorumIs fq szF memF ∗
        ⌜(∀ i : w32, memF i → sp.rid i ∈ sp.AQ c.N b) ∧
          (∀ i : w32, 0 ≤ sint.Z i → sp.rid i = sp.leaderOf c.N b → memF i)⌝ ∗ c.env d q ∗
        (typedPointsto (swift.fld c.rp go!"status") st (DFrac.own q) -∗
          typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own q) -∗ c.env d q -∗
          swift.shOwn c d b q) := by
  iintro H
  iunfold swift.shOwn at H
  icases H with ⟨He, HR⟩
  iunfold swift.shOwnR at HR
  icases HR with ⟨⟨%st, Hst⟩, ⟨%fq, %szF, %memF, HFQ, #HqF, %HAQ⟩, Hrd, Henv, Hpin⟩
  iexists st, fq, szF, memF
  iframe Hst HFQ HqF Henv
  isplitr
  · ipureintro; exact HAQ
  iintro Hst HFQ Henv
  iunfold swift.shOwn
  iframe He
  iunfold swift.shOwnR
  iframe Hrd Henv Hpin
  isplitl [Hst]
  · iexists st; iexact Hst
  iexists fq, szF, memF
  iframe HFQ HqF
  ipureintro; exact HAQ

/-- `rowPhaseOk` when the proposal is set without pre-accepting (:508, then `Recall` at a
replica outside `FQ`): the phase is `START` or `COMMIT` as before (`D = []`), the fresh row. -/
theorem swift.rowPhaseOk_prop (N r b : Nat) (dv : swift.DescV) (rv : swift.RowV)
    (hp : dv.propose ≠ null) (hph : dv.phase = W64 0 ∨ dv.phase = W64 3) (hD : dv.D = [])
    (hnl : dv.phase = W64 0 → r ≠ sp.leaderOf N b)
    (h1 : rv.1 = none) (hacc : rv.2.2.1 = false) (hcom : rv.2.2.2 = true → dv.phase = W64 3) :
    swift.rowPhaseOk N r b dv rv := by
  unfold swift.rowPhaseOk
  refine ⟨fun h => absurd h hp, fun _ => ⟨?_, fun h0 => ⟨hD, hnl h0⟩, ?_, ?_, ?_, ?_⟩⟩
  · rcases hph with h | h <;> rw [h] <;> decide
  · intro h'; rcases hph with h | h <;> rw [h] at h' <;> exact absurd h' (by decide)
  · intro h'; rcases hph with h | h <;> rw [h] at h' <;> exact absurd h' (by decide)
  · intro h; rw [h1] at h; cases h
  · intro h
    rcases h with h | h
    · rw [hacc] at h; cases h
    · left; rw [hcom h]; decide

/-- `rowPhaseOk` at `PRE_ACCEPT` (:520-521; PF13b: a committed row only at the leader). -/
theorem swift.rowPhaseOk_pre (N r b : Nat) (dv : swift.DescV) (rv : swift.RowV)
    (hp : dv.propose ≠ null) (h1 : dv.phase = W64 1) (hrv : rv.1 = some (dv.D.map toCmdId))
    (hacc : rv.2.2.1 = false) (hcom : rv.2.2.2 = true → r = sp.leaderOf N b) :
    swift.rowPhaseOk N r b dv rv := by
  unfold swift.rowPhaseOk
  refine ⟨fun h => absurd h hp, fun _ => ⟨by rw [h1]; decide, fun h0 => absurd (h1.symm.trans h0) (by decide),
    fun _ => hrv, fun h2 => absurd (h1.symm.trans h2) (by decide), fun _ => by rw [h1]; decide, ?_⟩⟩
  intro h
  rcases h with h | h
  · rw [hacc] at h; cases h
  · right; exact ⟨hcom h, by rw [h1]; decide⟩

/-- `Contains` decides the membership (round 33; for E7 at :515: the replica `b`'s leader is in
`FQ`, so `Contains(r.Id)` is true at the leader). Unfolds `replica.mset.quorumIs` (listed in
notes/prove-swift.md §41). -/
theorem swift.wp_qContainsIff [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
    (i : GoInterfaceOk) (sz : Nat) (mem : w32 → Prop) (r : w32) :
  {{ replica.mset.quorumIs (GoInterface.ok i) sz mem }}
    (App (Val #(methods i.ty go!"Contains" i.v)) (Val #r))
  {{ (b : Bool), RET #b; ⌜b = true ↔ mem r⌝ }} := by
  unfold replica.mset.quorumIs
  iintro %Φ ⟨%Hsz, Hq⟩ HΦ
  icases Hq with (⟨%Hq, %Hm⟩ | ⟨%ql, %s, ⟨%Hq, %Hs, %Hnd, %Hlt, %Hm⟩, #Hql⟩)
  · rcases Hq with h | h <;> cases h
    · wp_apply replica.Majority.Contains.wp_proof
      iapply HΦ; ipureintro; exact ⟨fun _ => Hm r, fun _ => rfl⟩
    · wp_apply replica.ThreeQuarters.Contains.wp_proof
      iapply HΦ; ipureintro; exact ⟨fun _ => Hm r, fun _ => rfl⟩
  · cases Hq
    wp_apply replica.Quorum.Contains.wp_proof $$ [$Hql] as -
    iapply HΦ; ipureintro; rw [Hm r]; simp

end lemmas

set_option hygiene false in
/-- `descRest` back into the frame `HDo` (`handlePropose`'s names). -/
macro "restHP" : tactic => `(tactic| (
  ihave HDo : iprop(swift.descRest c b x d ∗ Do) $$ [Hpd Hsq Hhs0 Hdf HDo]
  · iframe HDo
    iunfold swift.descRest; iexists pd', hs', sq', df; iframe Hpd Hsq Hhs0 Hdf Hpdok'))

set_option hygiene false in
/-- `descOwn` back after the P4 prefix (`handlePropose`'s names). -/
macro "refoldHP1" : tactic => `(tactic| (
  try (ihave Hsh := Hshb $$ Hst HFQ Henv)
  restHP
  iunfold swift.descOwn
  iexists msS, msF, qS, qF, szS, szF, memS, memF, hd
  iframe HhS HhF HdS
  iunfold swift.setR
  iunfold swift.descSt
  iexists qe, bw, stp, rcp, { dv with hs := hs', Hs := Hs' }, rv
  simp only [if_true, ↓reduceIte]
  ihave Htok := swift.rowTokO_mono c b x dv { dv with hs := hs', Hs := Hs' } rv rfl (fun h => h)
    $$ Htok
  iframe Hsh Hrd HRC Htok Hcom HsB HsF HfF HdF Hcore HDo
  isplitl [Hph' Hcmd Hdep Hhs Hprop Hseq Hmsgs]
  · iunfold swift.descF; iframe Hph' Hcmd Hdep Hhs Hprop Hseq Hmsgs Hvs HD HHs' Hmb HsL
    ipureintro; exact Hop
  isplitr
  · isplitr
    · iunfold swift.rowAcc at Hra; iunfold swift.rowAcc; iexact Hra
    iapply swift.repPre_null; exact hpn0
  isplitr
  · ipureintro; exact Hph
  isplitr
  · ihave Hpw2 := swift.phaseWhy_congr c.γ c.N c.r b x dv { dv with hs := hs', Hs := Hs' } rfl rfl
      $$ Hpw
    iexact Hpw2
  isplitr
  · ihave Hdw2 := swift.depWhy_congr c.γ c.γxm c.N c.r b x dv { dv with hs := hs', Hs := Hs' } rfl rfl rfl
      $$ Hdw
    iexact Hdw2
  ipureintro; exact Hrp))

section ctx
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- What `handlePropose` reads of the replica besides `descCtx` (persistent; the run loop's
`runLoopCtx` has it): `ackCtx` (for `handleFastAck`), `slowAddrs` (empty), `fastRead` with the
configuration's flag, the fast-ack pool's flag. -/
def swift.proposeCtx (c : swift.DC) : IProp netDistGF :=
  iprop(swift.ackCtx c ∗ swift.takeLaw c ∗
    ∃ (sam : GoMap) (fr : Bool) (lg : List GoString) (v : Bool),
      swift.fld c.rp go!"slowAddrs" ↦□ sam ∗ sam ↦$□ (∅ : GMap GoString Unit) ∗
      swift.fld c.rp go!"fastRead" ↦□ fr ∗ sp.cfg c.γc c.γm c.N fr lg ∗
      globalAddr swift.useFastAckPool ↦□ v)

instance swift.proposeCtx_persistent (c : swift.DC) : Persistent (swift.proposeCtx c) := by
  unfold swift.proposeCtx; infer_instance

/-- `proposeCtx` from its base part and the record's take law (round 37, plan R8b.1 (3)). -/
theorem swift.proposeCtx_ofB (c : swift.DC) :
    swift.proposeCtxB c ∗ swift.takeLaw c ⊢ swift.proposeCtx c := by
  iintro ⟨#HB, #HT⟩
  iunfold swift.proposeCtxB at HB
  icases HB with ⟨#HA, %sam, %fr, %lg, %v, #H1, #H2, #H3, #H4, #H5⟩
  iunfold swift.proposeCtx
  iframe HA HT
  iexists sam, fr, lg, v
  iframe H1 H2 H3 H4 H5

end ctx

set_option hygiene false in
/-- `handlePropose`'s exit with the owner state `Hown` (fast path): `descOcf` from the
`Recall`'s remnants, `HΦ`. -/
macro "exitOwnP" : tactic => `(tactic| (
  iapply HΦ
  ileft
  iunfold swift.descOwnF
  iframe Hown
  iunfold swift.descOcf
  iexists cf, cond, [], true
  iframe Hcond
  isplitl [Hapf Hocf HPc Hsb Hbs Hbsc]
  · iunfold swift.ocfRes; iframe Hapf Hocf HPc
    iexists sb, bs; iframe Hsb Hbs Hbsc; ipureintro; exact ⟨Hb.1, by simp⟩
  isplitr
  · iapply swift.ocfV_nil
  iapply BigSepL.bigSepL_nil.2; itrivial))

set_option hygiene false in
/-- `r.delivered.Has(cmdId.String())` with any result (`handlePropose`'s names). -/
macro "hasAnyP" : tactic => `(tactic| (
  wp_apply (wp_String c) $$ [cmdId] as cmdId
  · iexact cmdId
  ihave Hb : iprop(|={⊤}=> github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ∗
      (github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ={⊤}=∗ swift.ownRdr c.rp c.γdl)) $$ [HrdR]
  · iapply swift.ownRdr_take; iframe Hdm HrdR
  iapply fupd_wp
  imod Hb with ⟨Hrdr, HbackR⟩
  imodintro
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType github_com.orcaman.concurrent_map.ConcurrentMap.ty)
    (m := go!"Has")]
  try wp_auto
  wp_apply (wp_HasV dm c.γdl _ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
      (fun _ => iprop(True))) $$ [Hrdr] as %dl ⟨Hrdr, -⟩
  · iframe Hrdr
    imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
      swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
    iunfold swift.delivInv at Hi
    icases Hi with ⟨%M, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
    imodintro
    iexists M
    iframe HV
    iintro HV
    imod Hclose $$ [HV HXi HXeD HMx HXx] with -
    · inext; iunfold swift.delivInv; iexists M, bX', X', Mx, rm; iframe; ipureintro; exact HM
    imodintro
    itrivial
  iapply fupd_wp
  imod HbackR $$ Hrdr with HrdR
  imodintro))

set_option hygiene false in
/-- `r.delivered.Has(cmdId.String())` is true when `x` was executed in the epoch (`Hex`, the
pin `Hpin` at the fraction `q`, round 43, table §3R11b; `handlePropose`'s names). -/
macro "hasGoneP" q:term : tactic => `(tactic| (
  wp_apply (wp_String c) $$ [cmdId] as cmdId
  · iexact cmdId
  ihave Hb : iprop(|={⊤}=> github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ∗
      (github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ={⊤}=∗ swift.ownRdr c.rp c.γdl)) $$ [HrdR]
  · iapply swift.ownRdr_take; iframe Hdm HrdR
  iapply fupd_wp
  imod Hb with ⟨Hrdr, HbackR⟩
  imodintro
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType github_com.orcaman.concurrent_map.ConcurrentMap.ty)
    (m := go!"Has")]
  try wp_auto
  wp_apply (wp_HasV dm c.γdl _ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
      (fun ok => iprop(⌜ok = true⌝ ∗ swift.epochPinQ c.γxp $q b))) $$ [Hrdr Hpin] as %dl ⟨Hrdr, %Hdl, Hpin⟩
  · iframe Hrdr
    imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
      swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
    iunfold swift.delivInv at Hi
    icases Hi with ⟨%M, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
    ihave ⟨Hpin, HXeD, %Hag⟩ := swift.epochPinQ_agree c.γxp $q b bX' rm $$ [Hpin HXeD]
    · iframe Hpin HXeD
    obtain ⟨rfl, rfl⟩ := Hag
    ihave %Hin := swift.exIn_delivered c.str c.γxm bX' x M X' Mx HM $$ [Hex HMx]
    · iframe Hex HMx
    imodintro
    iexists M
    iframe HV
    iintro HV
    imod Hclose $$ [HV HXi HXeD HMx HXx] with -
    · inext; iunfold swift.delivInv; iexists M, bX', X', Mx, false; iframe; ipureintro; exact HM
    imodintro
    isplitr
    · ipureintro; exact Hin
    iexact Hpin
  iapply fupd_wp
  imod HbackR $$ Hrdr with HrdR
  imodintro
  subst Hdl))

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [hook.Assumptions] [replica.Assumptions] [sync.Assumptions]
  [github_com.orcaman.concurrent_map.Assumptions]

/-- `slowPath` out of the owner state, back with any value. -/
theorem swift.descOwn_slowPath (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) :
    swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ⊢
      ∃ sl : Bool, swift.dfld d go!"slowPath" ↦ sl ∗
        (swift.dfld d go!"slowPath" ↦ sl -∗
          swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do)) := by
  unfold swift.descOwn
  iintro ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF, HdS, HR⟩
  ihave ⟨%sl, Hsl, HRb⟩ := swift.setR_slowPath c RC MP γd d x b Do s f qF szF memF hd true $$ HR
  iexists sl
  iframe Hsl
  iintro Hsl
  ihave HR := HRb $$ Hsl
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe HhS HhF HdS HR

/-- The stored closures run by `Recall` (the leader's no-ops, or each from the owner state or
retired at a follower), then `Q`. Round 28 (G10): over `storedOk2` (the pre-acceptance disjunct
refuted at the token's arrival), the condition's state threaded. -/
theorem swift.recall_chain (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do Q : IProp netDistGF) (fs : List GoFunc) :
    ([∗list] g ∈ fs, swift.storedOk2 c RC MP γd d x b Do g) ⊢
      (swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ∗
        swift.ocfRes0 d) -∗
      (((swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) ∨
          swift.descDone c b x d) -∗ Q) -∗
        hook.ocf.chain fs Q := by
  iintro #Hfs ⟨Hown, Ho⟩ HQ
  by_cases hL : c.r = sp.leaderOf c.N b
  · ihave #Hn : iprop([∗list] g ∈ fs, □ swift.closureNop c RC MP γd d x b Do g) $$ [Hfs]
    · iapply BigSepL.bigSepL_mono _ $$ Hfs
      intro _ g _
      unfold swift.storedOk2
      iintro ⟨-, (%H | #H)⟩
      · exact absurd hL H
      · iexact H
    have h := swift.chain_leader c RC MP γd d x b Do [] Q fs
    rw [List.append_nil] at h
    iapply h $$ Hn [Hown Ho]
    · iframe Hown Ho
    iintro ⟨Hown, Ho⟩
    simp only [hook.ocf.chain]
    iapply HQ
    ileft; iframe Hown Ho
  · ihave #Hok : iprop([∗list] g ∈ fs, □ swift.closureOk c RC MP γd d x b Do g) $$ [Hfs]
    · iapply BigSepL.bigSepL_mono _ $$ Hfs
      intro _ g _
      unfold swift.storedOk2
      iintro ⟨#H, -⟩; iexact H
    iapply (swift.chain_follower c RC MP γd d x b Do hL Q fs) $$ [Hok] [Hown Ho] HQ
    · iexact Hok
    · ileft; iframe Hown Ho

/-- **The row token's arrival** (round 28, G7/G10): `handle_stepD`'s fresh token for `x`'s row
at a descriptor without a proposal (so without a token: two tokens are refuted); the deferred
commit is done if the descriptor says committed (its justification in `rowTokO`); the stored
closures' pre-acceptance disjunct is refuted (`storedOk2`). The row after: not pre-accepted, no
path, not accepted. -/
theorem swift.install_tok (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (dv : swift.DescV) (rv0 : swift.RowV) (qe : Qp) (bw : w32)
    (stp rcp : Loc) (fs : List GoFunc) :
    c.ctx ∗ swift.takeLaw c ∗ c.env d qe ∗
      swift.epochRd c.γe c.γxe c.rp c.rr qe b bw stp rcp ∗ swift.rowTokO c b x dv rv0 ∗
      ([∗list] g ∈ fs, swift.storedOk c RC MP γd d x b Do g) ∗
      swift.claimTok c.γcl (b, toCmdId x) .fresh ⊢
    |={⊤}=> swift.epochRd c.γe c.γxe c.rp c.rr qe b bw stp rcp ∗
      c.env d qe ∗ swift.rowTok c.γo b (toCmdId x) swift.rowEmpty ∗ swift.slotT c (b, toCmdId x) ∗
      ⌜dv.phase = swift.phCOMMIT → c.r = sp.leaderOf c.N b⌝ ∗
      [∗list] g ∈ fs, swift.storedOk2 c RC MP γd d x b Do g := by
  iintro ⟨#Hctx, #Htl, Henv, Hrd, Htok, #Hfs, Hcl⟩
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, %Hids, -, -, -,
    #Hinv, #Hcfg, #Hninv, -⟩
  obtain ⟨-, -, hrN, -, -, hk⟩ := Hids
  iunfold swift.epochRd at Hrd
  icases Hrd with ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩
  iunfold swift.rowTokO at Htok
  icases Htok with (⟨Htok, -⟩ | ⟨%Hn, #Hj, Hslt⟩)
  · -- a token already there: the claim's token is in the store (refuted)
    imod (swift.claim_tok_false c (b, toCmdId x) .fresh rv0) $$ [Hcl Htok] with Hf
    · iframe Hctx Hcl Htok
    iexfalso; iexact Hf
  -- T11₀ (table rev 6, G-slot): the token out of the store, the slot holding its receipt
  iunfold swift.takeLaw at Htl
  ihave Htk := Htl $$ %d %qe %(b, toCmdId x) %swift.ClK.fresh Henv Hslt Hcl
  imod Htk with ⟨%rvt, Hnt, Hw, Henv, Hslt⟩
  ihave %Hrvt := swift.retWhy_fresh c.γ c.γxm c.γcg c.str c.N c.r (b, toCmdId x) rvt $$ Hw
  subst Hrvt
  imod (swift.stored_ok2T c RC MP γd d x b Do fr lg qe swift.rowEmpty rfl hrN hk fs)
    $$ [Het Hnt] with ⟨Het, Hnt, #Hfs2⟩
  · iframe Hinv Hcfg Hninv Het Hnt Hfs
  by_cases hc : dv.phase = swift.phCOMMIT
  · icases Hj with (%h | %hl | #Hacc)
    · exact absurd hc h
    rotate_right
    · -- table rev 4/5 (PF13b): a follower's tokenless COMMIT (justified by `accepted`) is
      -- refuted by the fresh token's row (not accepted)
      imod (swift.accepted_row c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr lg qe b
          (toCmdId x) swift.rowEmpty hrN hk) $$ [Het Hnt] with ⟨-, -, %Hacc1⟩
      · iframe Hinv Hcfg Hninv Het Hnt Hacc
      exfalso; simp [swift.rowEmpty] at Hacc1
    -- L2 (item 4): the deferred commit happens at `ghostCommit`'s resolution (the caller)
    imodintro
    iframe Hnt Hfs2 Henv Hslt
    isplitl [Hbal HStf Hrcf Het Hxe]
    · iunfold swift.epochRd; iframe Hbal HStf Hrcf Het Hxe; ipureintro; exact Hbw
    ipureintro; exact fun _ => hl
  · imodintro
    iframe Hnt Hfs2 Henv Hslt
    isplitl [Hbal HStf Hrcf Het Hxe]
    · iunfold swift.epochRd; iframe Hbal HStf Hrcf Het Hxe; ipureintro; exact Hbw
    ipureintro; exact fun h => absurd h hc

/-- The fast ack's witness from the pre-acceptance (`preacc`, `pathIs`) and the path's hash. -/
theorem swift.propose_fastAckOk (γ : sp.Names) (me bw : w32) (x : swift.CommandId)
    (D P : List sp.CmdId) (H : swift.SHash) (sq : w64) (r b : Nat)
    (hme : sp.rid me = r) (hbw : sp.bal bw = b) (hwire : sp.wireOk me bw)
    (hlast : P.getLast? = some (toCmdId x)) (hcl : (toCmdId x).cl ≠ -1) :
    sp.preacc γ r b (toCmdId x) D ∗ sp.pathIs γ r b (toCmdId x) P ∗ sp.startHash P H.H'.arr ∗
      sp.numAck γ r b (toCmdId x) sq ∗ sp.locDeps γ r b (toCmdId x) D ⊢
      sp.fastAckOk γ ⟨me, bw, toCmdId x, D, [H.H'.arr], sq⟩ ∗ ⌜sp.hashesWf [H.H'.arr]⌝ := by
  iintro ⟨#Hpre, #Hpath, #Hsh, #Hnq, #Hld⟩
  ihave %Hl := sp.startHash_len P H.H'.arr $$ Hsh
  isplitl
  · iunfold sp.fastAckOk
    isplitr
    · ipureintro; exact hwire
    simp only
    rw [hme, hbw]
    iframe Hpre
    iexists P
    iframe Hpath Hnq Hld
    iunfold sp.pathHashes
    isplitr
    · ipureintro
      refine ⟨rfl, fun P' hP' => ?_⟩
      simp at hP'; subst hP'
      rw [List.getLast?_eq_some_iff] at hlast
      obtain ⟨Q, hQ⟩ := hlast
      exact ⟨Q, toCmdId x, hQ, hcl⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl
    · iexists H.H'.arr; iframe Hsh; ipureintro; rfl
    iapply BigSepL.bigSepL_nil.2; itrivial
  ipureintro
  refine ⟨by simp, fun h hh => ?_⟩
  simp at hh; subst hh; exact Hl

/-- `afterPropagate.Recall()` in `handlePropose` (the proposal set, its half `gp` held): the
stored closures run (from the owner state, as `recall_chain`) or nothing; after, the owner
state or (a closure retired the descriptor) `descDone`, and the condition's half back (its value
existential, `propose`'s other half in `descOwn` agrees with it). -/
theorem swift.wp_recallP (wp_Recall : hook.ocf.OptCondF.Recall.specI) (c : swift.DC)
    (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc)
    (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF) (cf : Loc) (cond : GoFunc)
    (fs : List GoFunc) (gp : Loc) (hgp : gp ≠ null) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.hook ∗
        hook.ocf.ownOcf cf cond fs ∗ □ hook.ocf.condOk cond (swift.proposeHalf d) ∗
        typedPointsto (swift.dfld d go!"propose") gp (DFrac.own (1 : Qp).half) ∗
        ([∗list] g ∈ fs, swift.storedOk2 c RC MP γd d x b Do g) ∗
        swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ∗
        swift.dfld d go!"afterPropagate" ↦ cf ∗
        (∃ (sb : GoSlice) (bs : List w32), swift.dfld d go!"storedBallots" ↦ sb ∗ sb ↦* bs ∗
          ownSliceCap w32 sb (DFrac.own 1) ∗ ⌜bs.Nodup⌝) }}
      (App (Val (cf @!! go.GoType.PointerType hook.OptCondF.ty @!! go!"Recall")) (Val #()))
    {{ (rb : Bool), RET #rb;
        ((swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) ∨
          (swift.descDone c b x d ∗ ⌜rb = true⌝)) }} := by
  iintro %Φ ⟨#Hpkg, Hocf, #Hcond, Hp1, #Hfs, Hown, Hapf, ⟨%sb, %bs, Hsb, Hbs, Hbsc, %Hbn⟩⟩ HΦ
  ihave HPc : swift.proposeHalf d true $$ [Hp1]
  · iunfold swift.proposeHalf; iexists gp; iframe Hp1; ipureintro; simp [hgp]
  by_cases hfs : fs.isEmpty = true
  · wp_apply (wp_Recall cf cond fs (swift.proposeHalf d) true iprop(True)) $$ [Hocf HPc]
      as %rb ⟨%Hrb, Hres⟩
    · iframe Hocf Hcond HPc
      simp only [hfs, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      itrivial
    simp only [hfs, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    icases Hres with ⟨Hocf, HPc⟩
    iapply HΦ
    ileft; iframe Hown
    have : fs = [] := by simpa using hfs
    subst this
    iunfold swift.ocfRes0; iexists cf, cond; iframe Hcond
    iunfold swift.ocfRes; iframe Hapf Hocf HPc
    iexists sb, bs; iframe Hsb Hbs Hbsc; ipureintro; exact ⟨Hbn, by simp⟩
  · let Q : IProp netDistGF := iprop(((swift.descOwn c RC MP γd d x b
        iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) ∨ swift.descDone c b x d))
    wp_apply (wp_Recall cf cond fs (swift.proposeHalf d) true Q)
      $$ [Hocf HPc Hown Hapf Hsb Hbs Hbsc] as %rb ⟨%Hrb, Hres⟩
    · iframe Hocf Hcond HPc
      simp only [hfs, Bool.not_false, Bool.and_true, ↓reduceIte]
      iintro HPc Hocf
      ihave Ho : swift.ocfRes0 d $$ [Hapf Hocf HPc Hsb Hbs Hbsc]
      · iunfold swift.ocfRes0; iexists cf, cond; iframe Hcond
        iunfold swift.ocfRes; iframe Hapf Hocf HPc
        iexists sb, bs; iframe Hsb Hbs Hbsc; ipureintro; exact ⟨Hbn, by simp⟩
      iapply (swift.recall_chain c RC MP γd d x b Do Q fs) $$ Hfs [Hown Ho]
      · iframe Hown Ho
      iintro Hst
      iexact Hst
    simp only [hfs, Bool.not_false, Bool.and_true, ↓reduceIte] at Hrb ⊢
    iapply HΦ
    icases Hres with (Hown | Hdone)
    · ileft; iexact Hown
    · iright; iframe Hdone; ipureintro; exact Hrb

end proof

end Perennial.github_com.imdea_software.swiftpaxos
