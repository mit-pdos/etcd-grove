/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DescFresh.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**A new epoch's descriptors' state** (round 23, sv-swb; task 3 of the round-23 brief): from a
fresh pool (`epochPool … ¼ γp ¼ ∅`, the rest of the running epoch), a fresh `cmdDescs`
(`descsFresh`), `cntL`'s registry unfrozen and the descriptors' context, the run loop's
`descDS`: the descriptors' sub-pool lent from the pool (loan `0`, half of the pool's share),
the descriptors' invariant allocated empty (`descInv`: the view `∅`, no running key, the
sub-pool with no loan), `stopDescs`' authorities, and the per-epoch names `g` (`g.mp`, `g.sq`
unconstrained: no entry yet; `g.sq := False`, so `sqOk` holds).

* `swift.descDS_alloc`: the allocation;
* `swift.epRunL_fresh`: `epFresh` (handleSync's new epoch) as the allocation's premise
  (`epRun_fresh`'s steps with the pool's loans known);
* `swift.descEpS γ γc γm x rp := fun _ _ => descDS … ∗ descPC …` and **`swift.descEpS_of`**:
  `handleSync`'s `EpS_start` at it (`syncCtx` gives the descriptors' context; round 47, 45-b: the
  persistent `PC := descPC`, the owners' contexts, kept in the new epoch's state).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescDS
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SeqPark

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


end defs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [replica.Assumptions] [replica.defs.Assumptions]
  [rpc.Assumptions] [sync.Assumptions] in
/-- No sequential state: `sqOk` holds trivially. -/
theorem swift.sqOk_false (γ : sp.Names) (DR : Loc → IProp netDistGF)
    (MP : swift.CommandId → GoInterface → IProp netDistGF) :
    swift.sqOk γ DR (fun _ _ => iprop(False)) MP := by
  refine ⟨?_, ?_, ?_⟩
  · intro d y; iintro H; iexfalso; iexact H
  · intro d y; iintro H; iexfalso; iexact H
  · intro d y; iintro H; iexfalso; iexact H

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [replica.Assumptions] [replica.defs.Assumptions]
  [rpc.Assumptions] [sync.Assumptions] in
/-- `sqOk` of the concrete sequential state `sqC` with its store's element (`sqE`; round 27,
round 29). -/
theorem swift.sqOk_C (γ : sp.Names) (DR : Loc → IProp netDistGF) (g : swift.DescG) :
    swift.sqOk γ DR (swift.sqE g) g.mp := by
  refine ⟨?_, ?_, ?_⟩
  · intro d y
    iintro H
    iunfold swift.sqE at H
    icases H with ⟨%γe, %Hγe, He, H⟩
    iunfold swift.sqC at H
    icases H with ⟨Ha, Hs, Hm⟩
    iexists _
    iframe Ha
    iintro Ha
    iunfold swift.sqE
    iexists γe
    iframe He
    isplitr
    · ipureintro; exact Hγe
    iunfold swift.sqC
    iframe
  · intro d y
    iintro H
    iunfold swift.sqE at H
    icases H with ⟨%γe, %Hγe, -, H⟩
    iunfold swift.sqC at H
    icases H with ⟨-, Hs, -⟩
    iexists _
    iframe Hs
  · intro d y
    iintro H
    iunfold swift.sqE at H
    icases H with ⟨%γe, %Hγe, He, H⟩
    iunfold swift.sqC at H
    icases H with ⟨Ha, Hs, %m, Hm⟩
    iexists m, _
    iframe Hm
    iintro Hm
    iunfold swift.sqE
    iexists γe
    iframe He
    isplitr
    · ipureintro; exact Hγe
    iunfold swift.sqC
    iframe

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [replica.Assumptions] [replica.defs.Assumptions]
  [rpc.Assumptions] [sync.Assumptions] [swift.Assumptions] in
/-- A whole points-to of a location and another whole one: impossible (round 29). -/
theorem swift.loc_pt_excl (l : Loc) (a b : Loc) :
    typedPointsto l a (DFrac.own 1) ∗ typedPointsto l b (DFrac.own 1) ⊢ (False : IProp netDistGF) := by
  simp only [typedPointsto_unseal, typedPointstoWrap, typedPointstoDef_heap]
  iintro ⟨⟨N1', -⟩, ⟨N2', -⟩⟩
  icombine N1' N2' gives %Hv
  exfalso; have := DFrac.valid_own_op Hv.1; simp at this

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [replica.Assumptions] [replica.defs.Assumptions]
  [rpc.Assumptions] [sync.Assumptions] in
/-- A message set as `newDesc` left it is free (`msgSetFree`, round 27). -/
theorem swift.ownD_free (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF) (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (hd : GoFunc) :
    replica.mset.ownD ms q sz mem P A PL iprop(True) hd ⊢ swift.msgSetFree ms := by
  iintro H
  iunfold swift.msgSetFree
  iexists q, sz, mem, P, A, PL, iprop(True), hd
  iframe H
  try itrivial

/-- **The epoch's names with the sequential forms** (round 37; plan R8.2 (1)'s construction,
table rev 8b T29): from `g00` (any `sr`, `so`), `g0 := {g00 with sr := soRaw … g00}` and
`g := {g0 with so := soO … g0}`. `soRaw` reads `g.mp`, `g.γk`, `g.ev`; `seqInbox` reads `sr`;
`descInv`, `envK`, `kfK`, `slotK`, `ret` read neither `sr` nor `so`. -/
abbrev swift.gO (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g00 : swift.DescG) :
    swift.DescG :=
  let g0 : swift.DescG := { g00 with sr := swift.soRaw γ γc γm x rp (swift.RCh γ γc γm rp) g00 }
  { g0 with so := swift.soO γ γc γm x rp (swift.RCh γ γc γm rp) g0 }

end proofs

section defsDS
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- **The run loop's descriptor state** (see DescDS.lean's header; round 22: with the running epoch
whose pool's one loan is the descriptors' sub-pool, `epRunL`). It is also the running epoch
`EpR` of `handleSync` (`swift.epR_stop_ofD`): `runInv` holds it in place of `epRun ∗
descState`. Round 42 (table §3R11 gap 11-1, D49 (1)): with the epoch's construction
`g = gO … g00` (`descDS_alloc`), so the inline call can open and fold `g.so` (`gO_so`); moved here
from DescDS.lean because `gO` is above SeqPark. -/
def swift.descDS (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) : IProp netDistGF :=
  iprop(∃ (g : swift.DescG) (ev : swift.EpV) (γp : GName) (i : Nat),
    swift.epRunL γ γc γm rp x ev γp i g.Qd ∗
    swift.descStateR γ rp x (x.DR γ g.ev.b) (swift.descGo x.γn g x.str) g ∗
    swift.epochLoan γp i g.Qd ∗ ⌜g.ev = ev⌝ ∗ swift.descDSCtx rp x ∗
    ⌜swift.sqOk γ (x.DR γ g.ev.b) (swift.sqE g) g.mp⌝ ∗ ⌜swift.mpOk x γ γc γm rp g⌝ ∗
    ⌜swift.soOk γ (x.DR γ g.ev.b) (x.dc γ γc γm rp) (swift.RCh γ γc γm rp) g⌝ ∗
    ⌜∃ g00 : swift.DescG, g = swift.gO γ γc γm x rp g00⌝ ∗
    -- round 56 (D79 (1), 52-3): the epoch's registration in the epochs' map
    swift.cgG x g ∗
    -- round B1 (D82 (4)): the epoch's free permit (minted with the registration) and the node
    -- invariant (to spend it, `swift.freeP_spend`)
    swift.freeP x.γcg g.ev.b ∗ inv swift.nodeN (swift.nodeInvD γ x.γv x.γe x.γo x.sn x.k))

/-- **The descriptors' contexts at the run loop's names** (round 47, 45-b, D61 (1) option (b);
`descDSN`'s persistent part): the kind-free record's context, `proposeCtxB` and the history pair,
and the run loop's string function (`runLoopCtx_str`, for the linked core `wp_coreD`).
`handleSync.specIR`'s `PC` at the descriptor instance (`swift.Replica.wp_handleSyncD`); the run
loop has them (`runInv`'s `descCtxE`, `runLoopCtx_ownB`). -/
def swift.descPC (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) : IProp netDistGF :=
  iprop((x.dc γ γc γm rp).ctx ∗ swift.proposeCtxB (x.dc γ γc γm rp) ∗
    (∃ hsl : GoSlice, swift.fld rp go!"history" ↦□ hsl ∗
      sync.isMutex (swift.fld rp go!"historyL") (swift.historyLInv hsl)) ∗
    ⌜x.str = swift.cmdStr⌝)

instance swift.descPC_persistent (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) :
    Persistent (swift.descPC γ γc γm x rp) := by
  unfold swift.descPC swift.DC.ctx; infer_instance

/-- `handleSync`'s new epoch's state for its `getCmdDesc` loop (`getCmdDesc.syncSpecI`'s `EpS`):
the run loop's descriptors' state. Round 47 (45-b): with the descriptors' contexts (`descPC`,
from `handleSync.specIR`'s `PC` at `EpS_start`), so that the sync entries' `getCmdDesc` has
`descDSN`. -/
def swift.descEpS (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) :
    sp.SyncMsg → List sp.CmdId → IProp netDistGF :=
  fun _ _ => iprop(swift.descDS γ γc γm x rp ∗ swift.descPC γ γc γm x rp)

end defsDS

section proofs2
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- **The sequential forms of an epoch built by `gO`** (round 42, table §3R11 11-1, §3R11a N1):
`g.so` is `soO` at `gO`'s first stage, `g.sr` is `soRaw` at `g00`. -/
theorem swift.gO_so (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g g00 : swift.DescG)
    (h : g = swift.gO γ γc γm x rp g00) :
    g.so = swift.soO γ γc γm x rp (swift.RCh γ γc γm rp)
        { g00 with sr := swift.soRaw γ γc γm x rp (swift.RCh γ γc γm rp) g00 } ∧
      g.sr = swift.soRaw γ γc γm x rp (swift.RCh γ γc γm rp) g00 := by
  subst h; exact ⟨rfl, rfl⟩

/-- **`replyChan.stop.specI` at the descriptors' state** (`EpR := descDS`, `EpH := descDSH`; moved
here from DescDS.lean with `descDS`, round 42). -/
theorem swift.epR_stop_ofD (wp_stop : swift.replyChan.stop.specR (hG := hG)) (γ : sp.Names)
    (γc γm : GName) (x : swift.RunX) (rp : Loc) :
    swift.replyChan.stop.specI (hG := hG) (fun _ => swift.descDS γ γc γm x rp)
      (fun _ => swift.descDSH γ x rp) rp := by
  intro rc pM
  iintro %Φ ⟨-, Hd, Hrc⟩ HΦ
  iunfold swift.descDS at Hd
  icases Hd with ⟨%g, %ev, %γp, %i, Hr, Hs, Hl, %Hg, #Hc, %Hsq, -, %Hso, -, #Hcg, Hfp, #HnI⟩
  iapply (swift.epRunL_stop wp_stop γ γc γm rp x ev γp i g.Qd rc) $$ [Hr Hrc]
  · iframe
  inext
  iintro ⟨Hh, Hrc⟩
  iapply HΦ
  iframe Hrc
  iunfold swift.descDSH
  iexists g, ev, γp, i
  iframe Hh Hs Hl Hc
  isplitr
  · ipureintro; exact Hg
  isplitr
  · ipureintro; exact Hsq
  iframe Hcg Hfp HnI
  iexists (x.dc γ γc γm rp), (swift.RCh γ γc γm rp)
  ipureintro; exact Hso

/-- The resources of a tokenless parked owner state (round 37b): its frame `Do`. -/
theorem swift.descOwnFP_res (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (q : Qp) (Do : IProp netDistGF) :
    swift.descOwnFP c RC MP γd d x b q Do ⊢ Do ∗ True := by
  iintro H
  iunfold swift.descOwnFP at H
  icases H with ⟨H, -⟩
  iunfold swift.descOwnP at H
  icases H with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, -, -, -, H⟩
  iunfold swift.setRP at H
  iunfold swift.descStP at H
  icases H with ⟨%dv, %rv, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, Hd⟩⟩
  isplitl [Hd]
  · iexact Hd
  itrivial

/-- The resources of a token-out parked owner state (round 37b): its frame `Dr`. -/
theorem swift.descOwnFT_res (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (q : Qp) (Do Dr : IProp netDistGF) :
    swift.descOwnFT c RC MP γd d x b q Do Dr ⊢ Dr ∗ True := by
  iintro H
  iunfold swift.descOwnFT at H
  icases H with ⟨⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, -, -, -, H⟩, -⟩
  iunfold swift.descStT at H
  icases H with ⟨%dv, -, -, -, -, -, -, -, ⟨-, -, -, -, Hd⟩⟩
  isplitl [Hd]
  · iexact Hd
  itrivial

/-- **`stopChan` and `active`'s half in every sequential form** (round 37b; `soOk` clauses 1, 4):
raw (`soRaw`), free (`kfK`'s seq branch) and token out (`kfK0`). -/
theorem swift.soO_scA (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (RC : Loc → w32 → IProp netDistGF) (g00 g0 : swift.DescG)
    (hsr : g0.sr = swift.soRaw γ γc γm x rp RC g00) (d : Loc) (y : swift.CommandId) :
    swift.soO γ γc γm x rp RC g0 d y ⊢
      (∃ sc : Loc, swift.dfld d go!"stopChan" ↦ sc) ∗
      typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗ True := by
  iintro H
  iunfold swift.soO at H
  rw [hsr]
  icases H with (H | ⟨%γi, %γsg, %γmc, %q, -, -, -, (H | ⟨-, H⟩)⟩)
  · iunfold swift.soRaw at H
    icases H with ⟨%γi, %γsg, %γmc, %m, %sc, %q, %sqv, %fqv, %szS, %szF, %memS, %memF, -, -, -, -, Ha, -,
      Hsc, -⟩
    isplitl [Hsc]
    · iexists sc; iexact Hsc
    iframe Ha
  · ihave ⟨⟨-, Hkf⟩, -⟩ := swift.descOwnFP_res _ _ _ _ _ _ _ _ _ $$ H
    simp only [swift.RunX.dcK, swift.kfK, swift.OwnK.isSeq, swift.OwnK.γi, if_true]
    icases Hkf with ⟨Ha, -, -, %sc, Hsc⟩
    isplitl [Hsc]
    · iexists sc; iexact Hsc
    iframe Ha
  · ihave ⟨⟨-, Hk0⟩, -⟩ := swift.descOwnFT_res _ _ _ _ _ _ _ _ _ _ $$ H
    iunfold swift.kfK0 at Hk0
    icases Hk0 with ⟨Ha, -, %sc, Hsc⟩
    isplitl [Hsc]
    · iexists sc; iexact Hsc
    iframe Ha

/-- **`soOk` of the sequential forms** (round 37; table rev 8b K2/K7, plan R8b.1 (9)). Round 37b:
all clauses proved. The freeze (clause 2) of the parked owner states collects their fields from
`descOwnFP`/`descOwnFT`, `descCore`, `descRest`, `descOcf` and `kfK`/`kfK0`: the free form to
`descRestA`, the token-out form to `descRestS`'s stored disjunct (the claim, `descRestH`). Table
rev 8c's proposal P1 (GAP-37a) would change only `g.sq`'s `msgs` fraction here. -/
theorem swift.soOk_O (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g00 : swift.DescG) :
    swift.soOk γ (x.DR γ g00.ev.b) (x.dc γ γc γm rp) (swift.RCh γ γc γm rp) (swift.gO γ γc γm x rp g00) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- two owner states of one descriptor: each has `stopChan` whole
    intro d y y'
    iintro ⟨H1, H2⟩
    ihave ⟨⟨%sc1, Hs1⟩, -⟩ := swift.soO_scA γ γc γm x rp (swift.RCh γ γc γm rp) g00 _ rfl d y $$ H1
    ihave ⟨⟨%sc2, Hs2⟩, -⟩ := swift.soO_scA γ γc γm x rp (swift.RCh γ γc γm rp) g00 _ rfl d y' $$ H2
    iapply swift.loc_pt_excl _ sc1 sc2 $$ [Hs1 Hs2]
    iframe
  · -- the freeze (T20)
    intro d y
    iintro ⟨Hq, Ho⟩
    simp only [swift.gO]
    iunfold swift.sqC at Hq
    icases Hq with ⟨Ha1, Hs1, %m1, Hm1⟩
    iunfold swift.soO at Ho
    icases Ho with (Ho | Ho)
    · iunfold swift.soRaw at Ho
      icases Ho with ⟨%γi, %γsg, %γmc, %m, %sc, %q, %sqv, %fqv, %szS, %szF, %memS, %memF, #Hw, -, Hm2, #Hmb,
        Ha2, Hs2, Hsc, Hsh, Hraw⟩
      ihave ⟨%Hm, Hm⟩ := swift.pt_14_12 _ m1 m $$ [Hm1 Hm2]
      · iframe
      ihave ⟨-, Ha⟩ := typedPointsto_half_combine _ true true (1 : Qp) $$ [Ha1 Ha2]
      · iframe
      ihave ⟨-, Hs⟩ := typedPointsto_half_combine _ true true (1 : Qp).half $$ [Hs1 Hs2]
      · iframe
      iunfold swift.descRaw at Hraw
      icases Hraw with ⟨%cf, %sl, %fa, %cond, %df, %hd, %cc, %vs, %sn, #Hmx, Hcmd, #Hvs, %Hop, Hdep,
        Hhs, Hsn, Hph, Hslw, Hdf, -, Hsb, Hp, Hpd, Hwa, Hap, Hocf, -, Hsl, Hfa, Hsls, Hfas, -⟩
      iunfold swift.descHomeS
      iexists m, sc, sl, fa, true
      iframe Hm Hsc Hsl Hfa Ha Hs
      isplitr
      · iunfold swift.bagW
        iexists γmc, iprop(swift.incW g00 γi γsg)
        iframe Hmb Hw
      isplitl [Hsls]
      · iapply swift.ownD_free $$ Hsls
      isplitl [Hfas]
      · iapply swift.ownD_free $$ Hfas
      isplitr
      · ipureintro; intro _; rfl
      iapply swift.descRestT_S
      ihave Hoa : swift.ocfAny cf $$ [Hocf]
      · iunfold swift.ocfAny
        iright
        iunfold hook.ocf.ownOcf at Hocf
        icases Hocf with ⟨%osl, %oL, Hocf⟩
        iexists cond, [], osl, oL
        iexact Hocf
      iapply swift.descRestT_raw γ x.sn x.γsh _ d q (W64 0) sn cc vs slice.nil slice.nil cf null false
        df Hop
      iframe Hsh Hmx Hph Hcmd Hvs Hdep Hhs Hsn Hp Hpd Hap Hoa Hslw Hdf Hwa Hsb
    · icases Ho with ⟨%γi, %γsg, %γmc, %q, #Hw, #Hcg, #Hctx, (Ho | ⟨Hcl, Ho⟩)⟩
      · -- the free (tokenless) parked form: every field to `descRestA`
        iunfold swift.descOwnFP at Ho
        icases Ho with ⟨Ho, Hocf⟩
        iunfold swift.descOwnP at Ho
        icases Ho with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, -, -, HoS, Ho⟩
        iunfold swift.setRP at Ho
        iunfold swift.descStP at Ho
        icases Ho with ⟨%dv, %rv, Hsh1, HF, HtP, -, -, -, -, -, %Hrp, -, Hslp, Hfsp, HoF, Hcore,
          Hrest, Hkf⟩
        iunfold swift.rowTokP at HtP
        icases HtP with ⟨%Htp, -⟩
        have hseq : dv.seq = true := Hrp.2
        simp only [swift.RunX.dcK, swift.kfK, swift.OwnK.isSeq, swift.OwnK.γi, ↓reduceIte]
        icases Hkf with ⟨Ha2, ⟨%q', Hsh2⟩, Hgv, %sc, Hsc⟩
        iunfold swift.descOcf at Hocf
        icases Hocf with ⟨%cf, %cond, %fs, %v, Hocr, -, -, -⟩
        iunfold swift.ocfRes at Hocr
        icases Hocr with ⟨Hap, Hown, Hph2, %sb, %bs, Hsb, -⟩
        iunfold swift.proposeHalf at Hph2
        icases Hph2 with ⟨%p, Hp2, -⟩
        iunfold swift.descF at HF
        icases HF with ⟨Hph, Hcmd, #Hvs, Hdep, #HD, Hhs1, -, Hp1, Hs2, Hm2, #Hmb, #Hmx, %Hop⟩
        iunfold swift.descCore at Hcore
        icases Hcore with ⟨%wa, %sl, Hwa, Hslw, -⟩
        iunfold swift.descRest at Hrest
        icases Hrest with ⟨%pd, %hs0, %sn, %df, Hpd, Hsn, Hhs2, Hdf, #Hpdk⟩
        rw [hseq]
        ihave ⟨%Hm, Hm⟩ := swift.pt_14_12 _ m1 dv.msgs $$ [Hm1 Hm2]
        · iframe
        ihave ⟨-, Ha⟩ := typedPointsto_half_combine _ true true (1 : Qp) $$ [Ha1 Ha2]
        · iframe
        ihave ⟨-, Hs⟩ := typedPointsto_half_combine _ true true (1 : Qp).half $$ [Hs1 Hs2]
        · iframe
        ihave ⟨-, Hhs⟩ := typedPointsto_half_combine _ dv.hs hs0 (1 : Qp) $$ [Hhs1 Hhs2]
        · iframe
        ihave ⟨%Hpp0, Hp⟩ := typedPointsto_half_combine _ dv.propose p (1 : Qp) $$ [Hp1 Hp2]
        · iframe
        ihave ⟨-, Hsh⟩ := swift.sh_agree x.γsh d q q' $$ [Hsh1 Hsh2]
        · iframe
        iunfold swift.descHomeS
        iexists dv.msgs, sc, s, f, true
        iframe Hm Hsc Hslp Hfsp Ha Hs
        isplitr
        · iunfold swift.bagW
          iexists γmc, _
          iframe Hmb Hw
        isplitl [HoS]
        · iapply swift.ownD_free $$ HoS
        isplitl [HoF]
        · iapply swift.ownD_free $$ HoF
        isplitr
        · ipureintro; intro _; rfl
        iapply swift.descRestT_S
        iunfold swift.descRestT
        have hpn : p = null := by rw [← Hpp0]; exact Htp.2
        subst hpn
        iexists q, dv.phase, sn, dv.c, dv.vs, dv.dep, hs0, pd, sb, cf, wa, sl, df, dv.D
        iframe Hsh Hmx Hph Hcmd Hvs Hdep HD Hhs Hsn Hp Hpd Hap Hslw Hdf Hwa Hsb
        isplitr
        · ipureintro; exact Hop
        isplitl [Hgv]
        · iright
          iexists _, y, γi
          isplitl []
          · iexact Hpdk
          isplitr
          · ipureintro; exact ⟨rfl, rfl, rfl⟩
          iframe Hgv
          -- round 58 (D82 (1)): the commit witness by ballot (`soO`'s `cgG`)
          iunfold swift.cgW
          iunfold swift.cgG at Hcg
          iunfold swift.incW at Hw
          iexists _, γsg
          isplitl []
          · iexact Hcg
          iexact Hw
        iunfold swift.ocfAny
        iright
        iunfold hook.ocf.ownOcf at Hown
        icases Hown with ⟨%osl, %oL, Hown⟩
        iexists cond, fs, osl, oL
        iexact Hown
      · -- the token-out parked form: to `descRestS`'s stored disjunct (`descRestH`, the claim)
        iunfold swift.descOwnFT at Ho
        icases Ho with ⟨⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, -, -, HoS, Ho⟩, Hocf⟩
        iunfold swift.descStT at Ho
        icases Ho with ⟨%dv, Hsh1, HF, -, -, #HrP, %Hsq, -, Hslp, Hfsp, HoF, Hcore, Hrest, Hk0⟩
        have hseq : dv.seq = true := Hsq.1
        iunfold swift.kfK0 at Hk0
        icases Hk0 with ⟨Ha2, ⟨%q', Hsh2⟩, %sc, Hsc⟩
        iunfold swift.descOcf at Hocf
        icases Hocf with ⟨%cf, %cond, %fs, %v, Hocr, -, -, -⟩
        iunfold swift.ocfRes at Hocr
        icases Hocr with ⟨Hap, Hown, Hph2, %sb, %bs, Hsb, -⟩
        iunfold swift.proposeHalf at Hph2
        icases Hph2 with ⟨%p, Hp2, -⟩
        iunfold swift.descFT at HF
        icases HF with ⟨Hph, Hcmd, #Hvs, Hdep, #HD, Hhs1, -, Hp1, Hs2, Hm2, #Hmb, #Hmx, %Hop⟩
        iunfold swift.descCore at Hcore
        icases Hcore with ⟨%wa, %sl, Hwa, Hslw, -⟩
        iunfold swift.descRest at Hrest
        icases Hrest with ⟨%pd, %hs0, %sn, %df, Hpd, Hsn, Hhs2, Hdf, #Hpdk⟩
        rw [hseq]
        icombine Hp1 Hp2 gives %Hpp
        rw [Hpp]
        ihave ⟨%Hm, Hm⟩ := swift.pt_14_12 _ m1 dv.msgs $$ [Hm1 Hm2]
        · iframe
        ihave ⟨-, Ha⟩ := typedPointsto_half_combine _ true true (1 : Qp) $$ [Ha1 Ha2]
        · iframe
        ihave ⟨-, Hs⟩ := typedPointsto_half_combine _ true true (1 : Qp).half $$ [Hs1 Hs2]
        · iframe
        ihave ⟨-, Hhs⟩ := typedPointsto_half_combine _ dv.hs hs0 (1 : Qp) $$ [Hhs1 Hhs2]
        · iframe
        ihave ⟨-, Hsh⟩ := swift.sh_agree x.γsh d q q' $$ [Hsh1 Hsh2]
        · iframe
        iunfold swift.descHomeS
        iexists dv.msgs, sc, s, f, true
        iframe Hm Hsc Hslp Hfsp Ha Hs
        isplitr
        · iunfold swift.bagW
          iexists γmc, _
          iframe Hmb Hw
        isplitl [HoS]
        · iapply swift.ownD_free $$ HoS
        isplitl [HoF]
        · iapply swift.ownD_free $$ HoF
        isplitr
        · ipureintro; intro _; rfl
        simp only [swift.RunX.DR]
        iunfold swift.descRestS
        iright
        isplitr
        · iunfold swift.DC.ctx at Hctx
          iunfold swift.descCtxE at Hctx
          icases Hctx with ⟨%me, %fr, %l, %dm', %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, -, -,
            -, -, -, -, #Hninv, -⟩
          iexact Hninv
        iexists _, γi
        iframe Hcl
        iunfold swift.descRestH
        iexists q, dv.phase, sn, dv.c, dv.vs, dv.dep, hs0, pd, sb, p, cf, wa, sl, df
        iframe Hsh Hmx Hph Hcmd Hvs Hdep Hhs Hsn Hp1 Hp2 Hpd Hap Hslw Hdf Hwa Hsb
        isplitr
        · ipureintro; exact Hop
        isplitl [Hown]
        · iunfold swift.ocfAny
          iright
          iunfold hook.ocf.ownOcf at Hown
          icases Hown with ⟨%osl, %oL, Hown⟩
          iexists cond, fs, osl, oL
          iexact Hown
        -- round 58 (D82 (1)): the claim's key, `proposeDep`'s facts, `cmd`'s proposal
        iexists y, _
        isplitl []
        · iexact Hpdk
        isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
        ihave #HpP := swift.repPre_homeP _ _ _ _ _ _ $$ [HrP HD]
        · iframe HrP HD
        rw [← Hpp]
        iExactEq HpP; rfl
  · -- the creation (T3/T3'): `seqNew'` is the entry's state and the raw form
    intro γi γsg sqv fqv szS szF memS memF γm' m sc q d y
    have hw : ∀ γi' γsg', swift.incW (swift.gO γ γc γm x rp g00) γi' γsg' = swift.incW g00 γi' γsg' :=
      fun _ _ => rfl
    simp only [swift.seqNew, hw]
    dsimp only [swift.gO, swift.soRaw, swift.MPi]
    iintro H
    icases H with ⟨Hm, #Hmb, #Hw, Hγi, Ha, Hs, Hsc, Hsh, Hraw⟩
    icases (typedPointsto_frac_add _ _ _ _).1 $$ Hm with ⟨Hm2, Hm1⟩
    icases (typedPointsto_half_split _ _ _).1 $$ Ha with ⟨Ha1, Ha2⟩
    icases (typedPointsto_half_split _ _ _).1 $$ Hs with ⟨Hs1, Hs2⟩
    isplitl [Ha1 Hs1 Hm1]
    · iunfold swift.sqC
      iframe Ha1 Hs1
      iexists m; iexact Hm1
    iexists γi, γsg, γm', m, sc, q, sqv, fqv, szS, szF, memS, memF
    iframe Hw Hγi Hm2 Ha2 Hs2 Hsc Hsh
    isplitl [Hmb]
    · iexact Hmb
    iexact Hraw
  · -- a share of `active`
    intro d y
    simp only [swift.gO]
    iintro H
    iunfold swift.soO at H
    icases H with (H | H)
    · iunfold swift.soRaw at H
      icases H with ⟨%γi, %γsg, %γmc, %m, %sc, %q, %sqv, %fqv, %szS, %szF, %memS, %memF, -, -, -, -, Ha, -⟩
      iexists true, _
      iframe Ha
    · ihave ⟨-, Ha, -⟩ := swift.soO_scA γ γc γm x rp (swift.RCh γ γc γm rp) g00
          { g00 with sr := swift.soRaw γ γc γm x rp (swift.RCh γ γc γm rp) g00 } rfl d y $$ [H]
      · iunfold swift.soO; iright; iexact H
      iexists true, _
      iframe Ha
  · -- the inbox's raw form is an owner state
    intro d y
    iintro H
    simp only [swift.gO]
    iunfold swift.soO
    ileft
    iexact H
  · -- (round 40, P39-2 clause 6) a raw form holds the share map's element whole
    intro d y q
    iintro ⟨H, Hh⟩
    simp only [swift.gO]
    iunfold swift.soRaw at H
    icases H with ⟨%γi, %γsg, %γmc, %m, %sc, %q', %sqv, %fqv, %szS, %szF, %memS, %memF, -, -, -, -, -,
      -, -, Hsh, -⟩
    icombine Hsh Hh gives %Hc
    exfalso
    have := DFrac.valid_own_op Hc.1
    revert this
    have : (1 : Qp).val = 1 := rfl
    simp

/-- The node invariant from the record's context (round 56). -/
theorem swift.dcCtx_node (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) :
    (x.dc γ γc γm rp).ctx ⊢ inv swift.nodeN (swift.nodeInvD γ x.γv x.γe x.γo x.sn x.k) := by
  iintro #H
  iunfold swift.DC.ctx at H
  iunfold swift.descCtxE at H
  icases H with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc0, %γrc, -, -, -, -, -, -,
    -, -, #Hn, -⟩
  iexact Hn

/-- **The descriptors' state of a new epoch** (see the file header). -/
theorem swift.descDS_alloc (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (ev : swift.EpV) (γp : GName) (γl : swift.CellNames) :
    swift.epochPool (x.epN rp) ev (1 : Qp).half.half γp (1 : Qp).half.half ∅ ∗
      swift.epochRest (x.epN rp) ev ∗ swift.replyChanH γ γc γm rp γl ev.bw ev.rcp ∗
      swift.cellFilled γl ∗ swift.rmTok x.γrm none ∗ ⌜ev.st = swift.stNORMAL⌝ ∗
      swift.descsFresh x.γd rp ∗ swift.cntFrozen x.γn false ∗ swift.descDSCtx rp x ∗
      ghostMapAuth x.γout (1 : Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Qp)) ∗
      -- round 56 (D79 (1), 52-3): the ballot's reserved key in the epochs' map, and its authority
      ghostMapElem x.γcg (ev.b, false) (DFrac.own 1) (none : Option GName) ∗
      inv swift.nodeN (swift.nodeInvD γ x.γv x.γe x.γo x.sn x.k) ⊢
    |={⊤}=> swift.descDS γ γc γm x rp := by
  iintro ⟨Hpool, Hrest, #HrcH, #Hfil, Hrm, %Hst, Hfr, Hfz, #Hctx, Hout, Hres, #HnI⟩
  imod (swift.epochPool_lend (x.epN rp) ev _ γp _ ∅ 0 (GMap.lookup_empty 0)) $$ Hpool
    with ⟨Hpool, Hsh, Hloan⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat) (V := Qp) with ⟨%γq, Hγq⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := GoString)
    (V := github_com.orcaman.concurrent_map.CmapLock × swift.LendK × GoInterface) with ⟨%γw, HW⟩
  imod (ghostVar_alloc (GF := netDistGF) false) with ⟨%γst, Hst⟩
  icases (ghostVar_split_half γst _ _).1 $$ Hst with ⟨Hst1, Hst2⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := GoString) (V := Bool) with ⟨%γs, Hs⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := GName) (V := GName) with ⟨%γk, Hk⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Loc) (V := swift.CommandId) with ⟨%γS, HSq⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Loc) (V := swift.CommandId) with ⟨%γS2, HSq2⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := GName) (V := Nat × Qp) with ⟨%γj, HJ⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat) (V := Nat × Qp) with ⟨%γlj, HLJ⟩
  imod (ghostVar_alloc (GF := netDistGF) (none : Option github_com.orcaman.concurrent_map.PinD))
    with ⟨%γb, Hb⟩
  iunfold swift.descsFresh at Hfr
  icases Hfr with ⟨%dm1, %γdc, Hcd, #Hdm, Hview, Hrds⟩
  ihave ⟨-, Hrd⟩ := swift.bundles_split _ 0 (by omega) $$ Hrds
  let g00 : swift.DescG := ⟨γdc, γst, γs, γb, γk, γq, ev, (1 : Qp).half.half.half,
    fun y => swift.descMP (x.dc γ γc γm rp) ev.b y (swift.slotMP x.γxm ev.b y)
      (swift.syncMP γ x.γcl x.r (sp.leaderOf x.N ev.b) ev.b y),
    γS, fun _ _ => iprop(False), γS2, fun _ _ => iprop(False), γj, γlj, γw⟩
  let g : swift.DescG := swift.gO γ γc γm x rp g00
  icases (typedPointsto_half_split _ _ _).1 $$ Hcd with ⟨Hcd, Hcd2⟩
  -- round 38 (table rev 9 T29, R9-1): the sub-pool's whole `Qd` carries `cmdDescs` ½
  ihave Hsub : swift.epochPoolX (x.epN rp) ev (swift.descX rp x.γd g dm1) (1 : Qp).half.half.half γq
      (1 : Qp).half.half.half ∅ $$ [Hγq Hsh Hcd2]
  · iapply swift.poolS_init_at
    iframe Hγq
    iunfold swift.epochShareX
    iframe Hsh
    iapply (swift.descX_Qd rp x.γd g dm1).2
    iframe Hcd2 Hdm
  imod inv_alloc swift.seqN ⊤ (swift.seqInbox g) $$ [HSq2] with #HSI
  · inext
    iunfold swift.seqInbox
    iexists ∅
    iframe HSq2
    iapply BigSepM.bigSepM_empty.2; itrivial
  imod inv_alloc swift.descN ⊤ (swift.descInv γ x.γd x.γn x.γout g (x.epN rp) (x.DR γ g.ev.b)
      (swift.descGo x.γn g x.str) x.str) $$ [Hst2 Hview Hk Hsub Hout HLJ HJ HW] with #HI
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists ∅, (1 : Qp).half.half.half, ∅, dm1, ∅
    iframe Hview HW
    isplitr
    · ipureintro; intro k hk; simp at hk
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitl [Hk]
    · iunfold swift.incInv
      iexists ∅, (fun _ => (default, default, false))
      iframe Hk
      isplitr
      · iapply BigSepM.bigSepM_empty.2; itrivial
      ipureintro; intro i j hi; simp at hi
    isplitl [Hsub]
    · rw [show g.Qd = (1 : Qp).half.half.half from rfl, show g.γq = γq from rfl,
        show g.ev = ev from rfl, show (x.epN rp).rp = rp from rfl]
      iexact Hsub
    isplitr
    · iunfold swift.loanRec
      iapply BigSepM.bigSepM_empty.2; itrivial
    isplitl [Hout]
    · iunfold swift.ledgerD
      iexists ∅
      iframe Hout
      iapply BigSepM.bigSepM_empty.2; itrivial
    iunfold swift.rcptAuth
    iexists ∅
    iframe HLJ
    isplitr
    · ipureintro; intro i hi; simp at hi
    iexists ∅
    iframe HJ
  -- round 56 (D79 (1), 52-3): register the epoch: `ev.b ↦ some γk` in the epochs' map; round B1
  -- (D82 (4)): and mint its free permit (`(ev.b, true)`, fresh: no permit before the registration)
  ihave Hcg : |={⊤}=> swift.cgG x g ∗ swift.freeP x.γcg g.ev.b $$ [Hres]
  · iinv HnI with Hi Hclose
    iunfold swift.nodeInvD at Hi
    imod Hi
    icases Hi with ⟨%st, %O, Hst0, Hw0, He0, HO0, HS0, HX0, %Hacc0⟩
    iunfold swift.nodeX at HX0
    icases HX0 with ⟨HXT, HXs, HXb, HXcg⟩
    iunfold swift.cgAuth at HXcg
    icases HXcg with ⟨%G, HGa, %hG⟩
    ihave %hGl := ghost_map_lookup $$ HGa Hres
    have hGt : G.lookup (ev.b, true) = none := by
      cases h : G.lookup (ev.b, true) with
      | none => rfl
      | some _ =>
        obtain ⟨γk', hk'⟩ := hG.2 ev.b (by rw [h]; rfl)
        rw [hGl] at hk'; cases hk'
    imod ghost_map_update (γ := x.γcg) (some γk : Option GName) $$ HGa Hres with ⟨HGa, Hres⟩
    imod (ghostMapElem_persist _ _ _ _) $$ Hres with #Hres
    have hGt' : (G.insert (ev.b, false) (some γk)).lookup (ev.b, true) = none := by
      rw [GMap.lookup_insert_eq_iff, if_neg (by simp)]; exact hGt
    imod ghost_map_insert (γ := x.γcg) (ev.b, true) (none : Option GName) hGt' $$ HGa
      with ⟨HGa, Hfp⟩
    imod Hclose $$ [Hst0 Hw0 He0 HO0 HS0 HXT HXs HXb HGa] with -
    · inext
      iunfold swift.nodeInvD
      iexists st, O
      iframe Hst0 Hw0 He0 HO0 HS0
      isplitl [HXT HXs HXb HGa]
      · iunfold swift.nodeX
        iframe HXT HXs HXb
        iunfold swift.cgAuth
        iexists (G.insert (ev.b, false) (some γk)).insert (ev.b, true) none
        iframe HGa
        ipureintro
        constructor
        · intro k h
          rw [GMap.lookup_insert_eq_iff] at h
          by_cases e1 : (ev.b, true) = k
          · subst e1; exact hG.1 (ev.b, false) (by rw [hGl]; rfl)
          · rw [if_neg e1, GMap.lookup_insert_eq_iff] at h
            by_cases e2 : (ev.b, false) = k
            · subst e2; exact hG.1 _ (by rw [hGl]; rfl)
            · rw [if_neg e2] at h; exact hG.1 k h
        · intro b h
          by_cases e : ev.b = b
          · subst e
            exact ⟨γk, by rw [GMap.lookup_insert_eq_iff, if_neg (by simp),
              GMap.lookup_insert_eq_iff, if_pos rfl]⟩
          · rw [GMap.lookup_insert_eq_iff, if_neg (by simp [e]), GMap.lookup_insert_eq_iff,
              if_neg (by simp)] at h
            obtain ⟨γk', hk'⟩ := hG.2 b h
            refine ⟨γk', ?_⟩
            rw [GMap.lookup_insert_eq_iff, if_neg (by simp), GMap.lookup_insert_eq_iff,
              if_neg (by simp [e])]
            exact hk'
      ipureintro; exact Hacc0
    imodintro
    isplitr
    · iunfold swift.cgG
      iExactEq Hres; rfl
    iunfold swift.freeP
    iExactEq Hfp; rfl
  imod Hcg with ⟨#Hcg, Hfp⟩
  imodintro
  iunfold swift.descDS
  iexists g, ev, γp, 0
  iframe Hloan Hctx Hcg Hfp HnI
  isplitl [Hpool Hrest Hrm]
  · iunfold swift.epRunL
    iexists γl, (1 : Qp).half.half.half
    iframe Hpool Hrest HrcH Hfil Hrm
    ipureintro; exact Hst
  isplitl [Hcd Hrd Hst1 Hfz Hs Hb HSq]
  · iunfold swift.descStateR
    iexists dm1
    iframe Hcd Hdm Hrd HI Hst1 Hfz Hs Hb HSI
    iunfold swift.seqStore
    iexists ∅
    iframe HSq
    iapply BigSepM.bigSepM_empty.2; itrivial
  ipureintro
  exact ⟨rfl, swift.sqOk_C γ _ g, rfl, swift.soOk_O γ γc γm x rp g00, g00, rfl⟩

/-- **The run loop has the descriptors' contexts** (round 47, 45-b): `runLoopCtx` with `syncCtx`
(the quorum of `SQ`) and the record's context give `descPC` (as `runLoopCtx_ownB`,
GetDescWithEnts.lean). For `handleSync.specIR`'s `PC` at the run loop's callers. -/
theorem swift.descPC_of (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (N r : Nat) :
    swift.runLoopCtx rp γ γc γm x ⊢
      □ (swift.syncCtx γ N r x.syncN rp -∗ (x.dc γ γc γm rp).ctx -∗ swift.descPC γ γc γm x rp) := by
  iintro Hrl
  iunfold swift.runLoopCtx at Hrl
  icases Hrl with ⟨%s, %b, %γs, %sq, %hsl, %fr, %pl, %sam, %csv, %n, -, #Fsnd, #Hsbag, #Fbt, #Hbh,
    -, #Fhist, -, -, #Ffr, -, -, #Fsam, #Hsam, -, -, #Fufp, -, #Fcs, %Hcs, -, -, #HhL, -, -, -, %Hstr,
    %lg, #Hcfg⟩
  imodintro
  iintro #Hsc #Hd
  iunfold swift.syncCtx at Hsc
  icases Hsc with ⟨%dm, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨%sqA, %szA, #FSQA, #HqA⟩⟩
  iunfold swift.descPC
  iframe Hd
  isplitr
  · iunfold swift.proposeCtxB
    isplitr
    · iunfold swift.ackCtx
      iexists sqA, szA, (fun _ => True), b, s, γs, csv
      iframe FSQA HqA Fbt Hbh Fsnd Hsbag Fcs
      isplitr
      · ipureintro; intro _; trivial
      isplitr
      · ipureintro; exact Hcs
      iexists _; iexact Fufp
    iexists sam, fr, lg, _
    iframe Fsam Hsam Ffr Hcfg Fufp
  isplitr
  · iexists hsl
    iframe Fhist HhL
  ipureintro; exact Hstr

/-- **`handleSync`'s `EpS_start` at the descriptors' state** (task 3, round 23): the new epoch
(`epFresh`, `epRun_fresh`'s steps) with the descriptors' context from `syncCtx`
(`descDSCtx`, round 23's conjuncts) gives `descDS` (`descDS_alloc`). -/
theorem swift.descEpS_of (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) :
    ∀ (N r b' : Nat) (M : sp.SyncMsg), 0 < b' →
      swift.syncCtx γ N r x.syncN rp ∗ □ swift.descPC γ γc γm x rp ∗
        swift.epFresh γ γc γm x.syncN x.γe x.γd rp x.rr b' ⊢
        |={⊤}=> swift.descEpS γ γc γm x rp M [] := by
  intro N r b' M hb
  simp only [swift.RunX.syncN]
  iintro ⟨#Hsc, #HPC, Hf⟩
  ihave #Hctx : swift.descDSCtx rp x $$ []
  · iunfold swift.syncCtx at Hsc
    icases Hsc with ⟨%dm, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hm, #Hp, #Hsh, #Hmx, -, #Hdel,
      ⟨%sqA, %szA, #FSQA, #HqA⟩⟩
    iunfold swift.descDSCtx
    iframe Hm Hp Hsh Hmx Hdel
    iexists sqA, szA, (fun _ => True)
    iframe FSQA HqA
    ipureintro; intro _; trivial
  iunfold swift.epFresh at Hf
  icases Hf with ⟨%bw, %stp', %rc, %γl, Hb, Hst, HS, Hrc, #HrcH, Hfill, He, Hxp, Hxe, Hrm, Hds,
    Hout, Hhs, %Hbw, Hfz, Hres, %fq, %szF, %memF, FQ1, FQ2, #HqF, %HmF⟩
  have hbw : 0 ≤ sint.Z bw := by
    unfold sp.bal at Hbw; show (0 : Int) ≤ bw.toInt; omega
  icases (typedPointsto_half_split _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Hst with ⟨Hs1, Hs2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ HS with ⟨HS1, HS2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ HS2 with ⟨HS2, HS3⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Hrc with ⟨Hr1, Hr2⟩
  iunfold swift.epochTok at He
  icases (ghostVar_split_half _ _ _).1 $$ He with ⟨He1, He2⟩
  icases (ghostVar_split_half _ _ _).1 $$ Hxe with ⟨Hxe1, Hxe2⟩
  icases (ghostVar_split_half _ _ _).1 $$ Hxp with ⟨Hxp1, Hxp2⟩
  ihave #HrcH2 := HrcH
  iunfold swift.replyChanH at HrcH2
  icases HrcH2 with ⟨%rep, %ok, %ex, %ar, %γok, %γex, %γa, -, -, -, -, #Hcell⟩
  imod swift.cell_fill swift.replyCellN ⊤ (by simp) γl (swift.replyCellRes rp bw)
    $$ [$Hcell $Hfill Hb2 Hhs] with #Hfilled
  · unfold swift.replyCellRes swift.replyRes; iframe Hb2; iexists _; iframe Hhs
    ipureintro; decide
  ihave Hsh : swift.epochShare ⟨x.γe, x.γxe, x.γxp, rp, x.rr, x.N⟩
      ⟨b', bw, stp', rc, swift.stNORMAL, fq, szF, memF⟩
      (1 : Qp).half.half $$ [Hb1 HS2 Hr1 He1 Hxe1 Hxp1 Hs1 FQ2]
  · unfold swift.epochShare swift.epochRd swift.epochTok swift.fqShare
    iframe
    isplitr
    · ipureintro; exact ⟨Hbw, hbw⟩
    iframe HqF
    ipureintro; exact HmF
  imod swift.epochPool_init _ _ _ $$ Hsh with ⟨%γp, Hpool0⟩
  ihave #HnI : inv swift.nodeN (swift.nodeInvD γ x.γv x.γe x.γo x.sn x.k) $$ []
  · iapply swift.dcCtx_node γ γc γm x rp
    ihave #HPC2 := HPC
    iunfold swift.descPC at HPC2
    icases HPC2 with ⟨#Hdc, -⟩
    iexact Hdc
  iunfold swift.descEpS
  iframe HPC
  iapply (swift.descDS_alloc γ γc γm x rp ⟨b', bw, stp', rc, swift.stNORMAL, fq, szF, memF⟩ γp γl)
  simp only [swift.RunX.epN]
  iframe Hpool0 HrcH Hfilled Hrm Hds Hfz Hctx Hout Hres HnI
  unfold swift.epochRest swift.epochTok; iframe

end proofs2

end Perennial.github_com.imdea_software.swiftpaxos
