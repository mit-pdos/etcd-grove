/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DescDS.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The run loop's descriptor state `DS`** (round 21, sv-swb; notes/prove-swift.md §27): the
instance of `handleProposal.specI DS` / `getCmdDescWith.propSpecI DS` (HandleProposal.lean)
that the descriptor side's `getCmdDescWith` proof is to use, and that `runInv` should hold between
arms in place of its provisional `swift.descState` (with the running epoch `epRun`, which it
contains as `epRunAt`).

`swift.descDS γ γc γm x rp`: for some epoch values `ev` and pool name `γp` (RunAlloc.lean's
`epRunAt`), the descriptors' state `descStateR` of the epoch `g` (DescState.lean) at the
concrete `DR := x.DR γ` (round 35: `descRestS`, DescState.lean; C5) and `Run := descGo x.γn g x.str`, the
descriptors' sub-pool `g.Qd` lent from the run loop's pool (its loan token `i`), and `g.ev = ev`.

PROVISIONAL until `getCmdDescWith`'s proof: what the spawn needs from the run loop is all here
(the epoch's sub-pool via `descInv`, the `cntL` freeze half, `cmdDescs` and its reader); the
link between `propMsgR`'s ballot `b` and `ev.b` comes from `propSpecI`'s fraction of `ballot`
(round 21) agreeing with `epRunAt`'s.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescState
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunAlloc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.StopDescsProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Store

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- The running epoch with its pool's loans known (round 22): `epRunAt` at `ev γp` whose pool
has exactly one loan, `i` of `Qd` (the descriptors' sub-pool): what `stopDescs` needs to give
the run loop the whole pool back. -/
def swift.epRunL (γ : sp.Names) (γc γm : GName) (rp : Loc) (x : swift.RunX) (ev : swift.EpV)
    (γp : GName) (i : Nat) (Qd : Qp) : IProp netDistGF :=
  iprop(∃ (γl : swift.CellNames) (q0 : Qp),
    swift.epochPool (x.epN rp) ev (1 : Qp).half.half γp q0 ((∅ : GMap Nat Qp).insert i Qd) ∗
    swift.epochRest (x.epN rp) ev ∗
    swift.replyChanH γ γc γm rp γl ev.bw ev.rcp ∗ swift.cellFilled γl ∗
    swift.rmTok x.γrm none ∗ ⌜ev.st = swift.stNORMAL⌝)

/-- `epHaltedAt` with its pool's one loan (round 22). -/
def swift.epHaltedL (rp : Loc) (x : swift.RunX) (ev : swift.EpV) (γp : GName) (i : Nat) (Qd : Qp) :
    IProp netDistGF :=
  iprop(∃ q0 : Qp,
    swift.epochPool (x.epN rp) ev (1 : Qp).half.half γp q0 ((∅ : GMap Nat Qp).insert i Qd) ∗
    swift.epochRest (x.epN rp) ev ∗
    swift.replyCellRes rp ev.bw ∗ swift.rmTok x.γrm none ∗ ⌜ev.st = swift.stNORMAL⌝)

/-- The descriptors' context record `swift.DC` of the replica `rp` with the names `x` (round 24:
every descriptor of the replica shares it; `descDS` fixes its epoch's message predicates `g.mp`
at it). -/
abbrev swift.RunX.dc (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) : swift.DC :=
  ⟨γ, γc, γm, x.γl, x.γw, x.γv, x.γe, x.γo, x.γx, x.γxe, x.γxm, x.γxp, x.γdc, x.γdl, x.str, rp,
    x.rr, x.N, x.r, x.k, x.γsh, x.γout, x.γcl, x.γxu, x.γrp, x.γcg,
    -- round 34 (D35, table rev 6 §3.10): the kind-free record of the messages' predicates and the
    -- context (`descMP` and `ctx` read no owner field); the owners' records are
    -- `swift.RunX.dcK x γ γc γm rp g k` (DescKind.lean), with `descMP_dcK`/`ctx_dcK`.
    false, fun _ _ => iprop(True), fun _ _ => iprop(True), fun _ _ => iprop(True), fun _ => iprop(True)⟩

/-- **A history slot for `y`'s descriptor in epoch `b`** (round 35; table rev 5 §3.0 Messages,
TS; plan R.2): the reply goroutine's `int s` (`args.finish <- slot`, replychan.go:72), in the
history's bounds, sent only after `deliver` executed `y` in `b` (`exIn`, from `replyWit`). -/
def swift.slotMP (γxm : GName) (b : Nat) (y : swift.CommandId) (m : GoInterface) : IProp netDistGF :=
  iprop(∃ s : w64, ⌜m = interface.mkOk go.int #s ∧ swift.slotIn s⌝ ∗ swift.exIn γxm b y)

instance swift.slotMP_persistent (γxm : GName) (b : Nat) (y : swift.CommandId) (m : GoInterface) :
    Persistent (swift.slotMP γxm b y m) := by
  unfold swift.slotMP; infer_instance

/-- **A sync entry for `y`'s descriptor in epoch `b`** (round 35; table rev 5 §3.0 Messages, T24;
plan R.2): `getCmdDesc.syncSpecI`'s payload (`handleSync`'s `&syncEntry{…}`, recovery.go:557):
the entry (owned: the descriptor reads it), the command's value and dependencies (read-only), the
proposal's record, `y`'s place in `b`'s sync order, the replica `r`'s acceptance of `y` in `b`, and
the entry's `sync` claim (its token is in the store, T28). Round 47 (46-2): `0 < b` and a non-nil
`dep` (`proposeDep`'s `pdOk`; the sync entry's descriptor keeps `hs` nil, so no hashes). Round 48
(47-a, D64): the replica's `sp.locLb γ r b (syncSeq M)` (`takeSync_stepD` gives every replica the
`locAt`s of the order, so it is unconditional: D64's `r ≠ leaderOf N b ∨ …` without the left
disjunct, and no `N`). -/
def swift.syncMP (γ : sp.Names) (γcl : GName) (r L b : Nat) (y : swift.CommandId) (m : GoInterface) :
    IProp netDistGF :=
  iprop(∃ (se gp : Loc) (c : sp.Cmd) (vs dsl : GoSlice) (D : List sp.CmdId) (M : sp.SyncMsg) (i : Nat),
    ⌜m = interface.mkOk (go.GoType.PointerType swift.syncEntry.ty) #se⌝ ∗
    se ↦ swift.syncEntry.mk gp (state.Command.mk c.op c.key vs) dsl ∗
    vs ↦*□ c.val ∗ dsl ↦*□ (D.map ofCmdId) ∗
    swift.propIs γ gp (toCmdId y) c ∗ sp.syncIs γ b M ∗
    sp.locAt γ r b i (toCmdId y) ∗ sp.accepted γ r b (toCmdId y) ∗
    swift.claimTok γcl (b, toCmdId y) .sync ∗
    -- round 48 (47-a, D64): the replica's `locLb` of the `MSync`'s sequence (`ldrPrefix`)
    sp.locLb γ r b (sp.syncSeq M) ∗
    -- round 54 (D74 (2), 53-4): the ballot's leader `L`'s (`msgOk (.sync)`'s)
    sp.locLb γ L b (sp.syncSeq M) ∗
    ⌜(toCmdId y, c, D) ∈ M ∧ (sp.syncOrder M)[i]? = some (toCmdId y) ∧ 0 < b ∧ dsl ≠ slice.nil⌝)

/-- **The epoch's message predicates** (round 24; round 35: concrete `SL`/`SE`, plan R.2): `y`'s
descriptor's channel carries `descMP` at the replica's record and the epoch's ballot, with the
history slots' and sync entries' payloads `slotMP`/`syncMP`. -/
def swift.mpOk (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) (g : swift.DescG) :
    Prop :=
  g.mp = fun y => swift.descMP (x.dc γ γc γm rp) g.ev.b y (swift.slotMP x.γxm g.ev.b y)
    (swift.syncMP γ x.γcl x.r (sp.leaderOf x.N g.ev.b) g.ev.b y)

/-- The persistent facts the descriptors' state needs (round 22): `cntL`'s mutex and the
descriptor pool (both `runLoopCtx`'s); round 27 (D24): what the spawn's `newDesc` reads, the
share map's invariant, `MaxDescRoutines` and the slow quorum `SQ` with its quorum. -/
def swift.descDSCtx (rp : Loc) (x : swift.RunX) : IProp netDistGF :=
  iprop(sync.isMutex (swift.fld rp go!"cntL") (swift.cntLInvR rp x.dm x.γdl x.γn x.d) ∗
    swift.descPoolCtx (swift.descDFA x.γsh) rp ∗
    inv swift.shN (swift.shInv x.γsh) ∗ globalAddr swift.MaxDescRoutines ↦□ x.d ∗
    -- round 54 (D74 (3), 53-1): `SQ` has every replica (New's `NewMajorityOf`)
    (∃ (sq : GoInterface) (szS : Nat) (memS : w32 → Prop),
      swift.fld rp go!"SQ" ↦□ sq ∗ replica.mset.quorumIs sq szS memS ∗ ⌜∀ k, memS k⌝) ∗
    -- round 42 (table §3R11 gap 11-2): `delivered`'s value is `cntL`'s readers' `x.dm` (PF29)
    swift.fld rp go!"delivered" ↦□ x.dm)

instance swift.descDSCtx_persistent (rp : Loc) (x : swift.RunX) :
    Persistent (swift.descDSCtx rp x) := by
  unfold swift.descDSCtx swift.descPoolCtx; infer_instance

/-- **`descDS` once the reply goroutine stopped** (`EpH` of `replyChan.stop`/`stopDescs`). -/
def swift.descDSH (γ : sp.Names) (x : swift.RunX) (rp : Loc) : IProp netDistGF :=
  iprop(∃ (g : swift.DescG) (ev : swift.EpV) (γp : GName) (i : Nat),
    swift.epHaltedL rp x ev γp i g.Qd ∗
    swift.descStateR γ rp x (x.DR γ g.ev.b) (swift.descGo x.γn g x.str) g ∗
    swift.epochLoan γp i g.Qd ∗ ⌜g.ev = ev⌝ ∗ swift.descDSCtx rp x ∗
    ⌜swift.sqOk γ (x.DR γ g.ev.b) (swift.sqE g) g.mp⌝ ∗
    (∃ (c0 : swift.DC) (RC : Loc → w32 → IProp netDistGF), ⌜swift.soOk γ (x.DR γ g.ev.b) c0 RC g⌝) ∗
    -- round 56 (D79 (1), 52-3): the epoch's registration (for `stopPS`)
    swift.cgG x g ∗
    -- round B1 (D82 (4)): the epoch's free permit (for `stopPS`) and the node invariant
    swift.freeP x.γcg g.ev.b ∗ inv swift.nodeN (swift.nodeInvD γ x.γv x.γe x.γo x.sn x.k))

end defs


section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- `r.repchan.stop()` on `epRunL` (`swift.epRunAt_stop` with the pool framed). -/
theorem swift.epRunL_stop (wp_stop : swift.replyChan.stop.specR (hG := hG)) (γ : sp.Names)
    (γc γm : GName) (rp : Loc) (x : swift.RunX) (ev : swift.EpV) (γp : GName) (i : Nat) (Qd : Qp)
    (rc : Loc) :
    {{ swift.epRunL γ γc γm rp x ev γp i Qd ∗
        typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Qp).half) }}
      (App (Val (rc @!! go.GoType.PointerType swift.replyChan.ty @!! go!"stop")) (Val #()))
    {{ RET #(); swift.epHaltedL rp x ev γp i Qd ∗
        typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Qp).half) }} := by
  unfold swift.epRunL swift.epochRest swift.RunX.epN
  iintro %Φ ⟨Hep, Hrc⟩ HΦ
  icases Hep with ⟨%γl, %q0, Hpool, Hrest, #HrcH, #Hfilled, Hrm, %Hst⟩
  icases Hrest with ⟨Hs, HS1, HS2, Hr, He, Hxe, Hxp, HFQ1⟩
  ihave %Hrceq : ⌜rc = ev.rcp⌝ $$ [Hrc Hr]
  · iapply typedPointsto_agree_wand _ _ _ _ _ $$ Hrc Hr
  subst Hrceq
  ihave #HrcH2 := HrcH
  iunfold swift.replyChanH at HrcH2
  icases HrcH2 with ⟨%rep, %ok, %ex, %ar, %γok, %γex, %γa, -, -, -, -, #Hcell⟩
  iapply wp_fupd
  iapply (wp_stop γ γc γm rp γl ev.bw ev.rcp) $$ [HrcH]
  · iexact HrcH
  inext
  iintro Hback
  ihave Hres : |={⊤}=> swift.replyCellRes rp ev.bw $$ [Hback]
  · iunfold swift.replyBack at Hback
    icases Hback with (Hb | Hk)
    · imodintro; iexact Hb
    · imod swift.cell_claim swift.replyCellN ⊤ (by simp) γl (swift.replyCellRes rp ev.bw)
        $$ [$Hcell $Hk $Hfilled] with >Hb
      imodintro; iexact Hb
  imod Hres
  imodintro
  iapply HΦ
  iframe Hrc
  iunfold swift.epHaltedL
  simp only [swift.RunX.epN]
  iexists q0
  iframe Hpool Hres Hrm
  isplitl [Hs HS1 HS2 Hr He Hxe Hxp HFQ1]
  · unfold swift.epochRest; iframe
  ipureintro; exact Hst

/-- **The stopped epoch from the halted one** (round 22): the descriptors' sub-pool's share back
(`stopDescs`' `descsDone`), the pool's one loan returned, the run loop's pool whole, with the
rest of the epoch and the reply goroutine's cell: `epStopped`. -/
theorem swift.epHaltedL_stopped (γ : sp.Names) (rp : Loc) (x : swift.RunX) (ev : swift.EpV) (γp : GName)
    (i : Nat) (Qd : Qp) :
    swift.epHaltedL rp x ev γp i Qd ∗ swift.epochLoan γp i Qd ∗
      swift.epochShare (x.epN rp) ev Qd ∗ swift.descsStopped x.γd (swift.descDF (x.DR γ ev.b)) (swift.stopPS x ev.b) rp ∗
      swift.cntFrozen x.γn true ∗ ghostMapAuth x.γout (1 : Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Qp)) ⊢
    |==> swift.epStopped x.syncN x.γe x.γd (fun b => swift.descDF (x.DR γ b)) (swift.stopPS x) rp x.rr := by
  iintro ⟨Hh, Hl, Hsh, Hds, Hfz, Hout⟩
  iunfold swift.epHaltedL at Hh
  icases Hh with ⟨%q0, Hpool, Hrest, Hcell, Hrm, %Hst⟩
  imod swift.epochPool_return _ _ _ γp q0 _ i Qd $$ [Hpool Hsh Hl] with Hp
  · iframe
  have hL : GMap.delete i ((∅ : GMap Nat Qp).insert i Qd) = (∅ : GMap Nat Qp) :=
    GMap.delete_insert ∅ i Qd (GMap.lookup_empty i)
  ihave Hq := swift.epochPool_stopped _ _ _ _ _ _ $$ [Hp]
  · iframe Hp; rw [hL]; iapply BigSepM.bigSepM_empty.2; iempintro
  imodintro
  simp only [swift.RunX.syncN, swift.RunX.epN]
  unfold swift.epochShare swift.epochRd swift.epochTok swift.fqShare at *
  unfold swift.epochRest swift.epochTok swift.replyCellRes swift.replyRes at *
  icases Hq with ⟨⟨Hb, HS, Hr, He, Hxe, -⟩, Hxp, Hs, HFQ, -, -⟩
  icases Hrest with ⟨Hs2, HS1, HS2, Hr2, He2, Hxe2, Hxp2, HFQ1⟩
  icases Hcell with ⟨Hb2, %hs, Hhs, -⟩
  iunfold swift.epStopped
  iexists ev.bw, ev.st, ev.stp, ev.stp, (ev.b, ev.b)
  iframe Hrm Hds Hfz Hout
  isplitl [Hb Hb2]
  · iapply (typedPointsto_half_split _ _ _).2; iframe
  isplitl [Hs Hs2]
  · iapply (typedPointsto_half_split _ _ _).2; iframe
  isplitl [HS HS1 HS2]
  · iapply (typedPointsto_half_split _ _ _).2
    iframe HS1
    iapply (typedPointsto_half_split _ _ _).2; iframe
  isplitl [Hr Hr2]
  · iexists ev.rcp; iapply (typedPointsto_half_split _ _ _).2; iframe
  isplitl [He He2]
  · iunfold swift.epochTok; iapply (ghostVar_split_half _ _ _).2; iframe
  isplitl [Hxp Hxp2]
  · iapply (ghostVar_split_half _ _ _).2; iframe
  isplitl [Hxe Hxe2]
  · iapply (ghostVar_split_half _ _ _).2; iframe
  isplitl [Hhs]
  · iexists hs; iframe
  iexists ev.fq
  iframe HFQ1 HFQ

/-- **`stopDescs` at the descriptors' state** (round 22; task 3 of §27): `stopDescs.specI` with
`EpH := descDSH` (the halted epoch with the descriptors' state), over `stopDescs.wp_specD`. -/
theorem swift.Replica.stopDescs.wp_specI (γ : sp.Names) (x : swift.RunX) (rp : Loc) :
    swift.Replica.stopDescs.specI (hG := hG) (fun _ => swift.descDSH γ x rp) γ x.syncN x.γe x.γd
      (fun b => swift.descDF (x.DR γ b)) (swift.stopPS x) x.rr rp := by
  intro pM
  iintro %Φ ⟨#Hpkg, Hd⟩ HΦ
  iunfold swift.descDSH at Hd
  icases Hd with ⟨%g, %ev, %γp, %i, Hh, Hs, Hl, %Hg, #Hc, %Hsq, ⟨%c0, %RC, %Hso⟩, #Hcg, Hfp,
    #HnI⟩
  iunfold swift.descDSCtx at Hc
  icases Hc with ⟨#HcntL, #Hpool, -⟩
  iapply wp_fupd
  iapply (swift.Replica.stopDescs.wp_specD γ rp x (x.DR γ g.ev.b) g x.dm x.d Hsq c0 RC Hso) $$ [Hs]
  · iframe Hpkg HcntL Hs
  inext
  iintro Hdone
  -- round 35 (C5): the pool's context for the stopped homes (`descRestS_forget` at T23); round B1
  -- (D82 (4)): its law needs the epoch's free permit spent, which `handleSync` does with `stopPS`
  ihave #HpoolF : swift.descPoolCtxS (swift.descDF (x.DR γ g.ev.b)) (swift.stopPS x g.ev.b) rp $$ []
  · iunfold swift.descPoolCtxS
    iexists (swift.descDFA x.γsh), (swift.freeSp x.γcg g.ev.b)
    iframe Hpool
    isplitr
    · imodintro
      iintro %Mc HPS
      iunfold swift.stopPS at HPS
      icases HPS with ⟨-, Hfp', -⟩
      imod (swift.freeP_spend γ x.γv x.γe x.γo x.sn x.k g.ev.b) $$ [HnI Hfp'] with #Hsp
      · iframe HnI; iexact Hfp'
      imodintro; imodintro; iexact Hsp
    imodintro
    iintro %d #Hsp H
    iunfold swift.descDF at H
    icases H with ⟨%a, %s, Ha, Hs, %Has, HR⟩
    imod swift.descRestS_forget γ x.γv x.γe x.γo x.sn x.k x.γsh g.ev.b d $$ [Hsp HR] with HR
    · isplitl []
      · iexact Hsp
      iexact HR
    imodintro
    unfold swift.descDFA swift.descDF
    iexists a, s
    iframe
    ipureintro; exact Has
  ihave ⟨Hds, Hfz, Hsh, -, Hout⟩ := swift.descsDone_stopped γ rp x (x.DR γ g.ev.b) g $$ [Hdone Hfp]
  · iframe Hdone HpoolF Hcg Hfp
  rw [Hg] at *
  imod swift.epHaltedL_stopped γ rp x ev γp i g.Qd $$ [Hh Hl Hsh Hds Hfz Hout] with Hst
  · iframe
  imodintro
  iapply HΦ $$ Hst

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
