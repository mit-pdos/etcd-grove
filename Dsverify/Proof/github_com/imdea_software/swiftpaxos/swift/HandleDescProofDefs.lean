/-
The definitions, specs and lemmas of `HandleDescProof.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HdInv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DrainStopsDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescInit

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- **`r.handleMsg(m, desc, cmdId)` by a goroutine** (see the file header): from `hdInv`'s owner form
(R2b/R3) and a message of the bag, the owner form again (`false`) or the slot case's tail (`true`). -/
abbrev swift.Replica.handleMsg.specG (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (RC : Loc → Loc → w32 → IProp netDistGF) : Prop :=
  ∀ (rp : Loc) (g : swift.DescG) (j iL : Nat) (γi γsg : GName) (γmc : ChanNames) (d : Loc)
    (y : swift.CommandId) (m : GoInterface),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.goPreP γ0 γc γm x rp g ∗
      (x.dcK γ0 γc γm rp g (.go j iL γi)).ctx ∗ □ swift.proposeCtx (x.dcK γ0 γc γm rp g (.go j iL γi)) ∗
      swift.depSpecR (x.dcK γ0 γc γm rp g (.go j iL γi)) ∗
      swift.descOwnF (x.dcK γ0 γc γm rp g (.go j iL γi)) (RC rp) (swift.MPi g y γi γsg) γmc d y g.ev.b
        iprop(swift.descRest (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.go j iL γi)).kf d y) ∗
      swift.MPi g y γi γsg m }}
    (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleMsg"))
      (Val #m)) (Val #d)) (Val #y))
  {{ (v : Bool), RET #v;
      (⌜v = false⌝ ∗ swift.descOwnF (x.dcK γ0 γc γm rp g (.go j iL γi)) (RC rp) (swift.MPi g y γi γsg) γmc d y
          g.ev.b iprop(swift.descRest (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y d ∗
            (x.dcK γ0 γc γm rp g (.go j iL γi)).kf d y)) ∨
      (⌜v = true⌝ ∗ swift.tailG x g d y) }}

/-- **`r.handleMsg(&syncEntry{…}, desc, cmdId)`, `handleSyncEntry`** (plan R8.2 (5), table T24; stated
round 43, D51 (c): no pin): from the owner state and a sync entry of the epoch (`syncMP`, with its
`.sync` claim for `install_sync`), the owner state back or retired. -/
abbrev swift.Replica.handleMsg.syncSpecIc (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (c : swift.DC) : Prop :=
  ∀ (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF)
    (m : GoInterface),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ □ swift.proposeCtx c ∗ swift.depSpecR c ∗
      swift.descOwnF c RC MP γd d x b iprop(swift.descRest c b x d ∗ Do) ∗
      swift.syncMP c.γ c.γcl c.r (sp.leaderOf c.N b) b x m }}
    (App (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleMsg"))
      (Val #m)) (Val #d)) (Val #x))
  {{ RET #false; swift.descOwnF c RC MP γd d x b iprop(swift.descRest c b x d ∗ Do) ∨
      swift.descDone c b x d }}

/-- `swift.Replica.handleMsg.syncSpecI` at every record (round 44, D53 (1): the per-record form `swift.Replica.handleMsg.syncSpecIc`). -/
abbrev swift.Replica.handleMsg.syncSpecI (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) : Prop :=
  ∀ c : swift.DC, swift.Replica.handleMsg.syncSpecIc RC MP c

end specs

section stopDefs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- **The stop arm's capability** (round 44; table §3R11 T19a.g-T19x, T19Ra/T19Rh): from the received
request (at the stop bag's names `γsg'`, `W`) and `active`'s loop half, T19a.g (`active` whole, the
request's signal token and `Done`, the element's half), and a wand for after the store and the drains
(T19h, T19x): the element whole and the registry slot for `cntL`. `hd_open` gives it for both forms of
`hdInv`. -/
def swift.hdStopW (x : swift.RunX) (g : swift.DescG) (d : Loc) (y : swift.CommandId) (sc m : Loc)
    (γsg' : GName) (W : IProp netDistGF) : IProp netDistGF :=
  iprop(∀ wg : Loc, £ 1 -∗ swift.stopMP g.γs γsg' (x.str y) d sc wg -∗ □ W -∗
    typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) -∗
    |={⊤}=> swift.dfld d go!"active" ↦ true ∗ swift.sgTok γsg' ∗
      sync.join.ownDone wg (ghostMapElem g.γs (x.str y) (DFrac.own 1) true) ∗
      ghostMapElem g.γs (x.str y) (DFrac.own (1 : Qp).half) true ∗
      (£ 1 -∗ £ 1 -∗ £ 1 -∗ swift.dfld d go!"active" ↦ false -∗
        typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half) -∗
        typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half) -∗
        ghostMapElem g.γs (x.str y) (DFrac.own (1 : Qp).half) true -∗
        |={⊤}=> ghostMapElem g.γs (x.str y) (DFrac.own 1) true ∗
          ∃ j : Nat, ghostMapElem x.γn j (DFrac.own 1) false ∗ swift.delReader x.dm x.γdl))

/-- **A goroutine's owner state without the loop's halves** (round 44): `descOwnF`'s parts at the
goroutine record `c` with frame `descRest ∗ kfK`, but for `active`'s and `stopChan`'s `kfK` halves and
`descF`'s half of `msgs` (`m`), which the loop holds (`hd_open`); `kfK`'s stop bag at `(sc, γsc,
γsg')`. What the stop arm's owner steps (T19a.g, T19h, T19x) start from (`hd_stopOwn`). -/
def swift.hdOwnRes (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) (d : Loc) (y : swift.CommandId) (γi γsg : GName)
    (j iL : Nat) (γmc : ChanNames) (sc m : Loc) (γsc : ChanNames) (γsg' : GName) : IProp netDistGF :=
  iprop(∃ (s f : Loc) (qS qF : GoInterface) (szS szF : Nat) (memS memF : w32 → Prop) (hd : GoFunc)
      (q : Qp) (bw : w32) (stp rcp : Loc) (dv : swift.DescV) (rv : swift.RowV),
    ⌜dv.msgs = m⌝ ∗
    swift.acksHdOk (x.dcK γ0 γc γm rp g (.go j iL γi)) RC (swift.MPi g y γi γsg) γmc d y g.ev.b hd ∗
    swift.slotCap (x.dcK γ0 γc γm rp g (.go j iL γi)) (swift.MPi g y γi γsg) γmc d y g.ev.b
      iprop(swift.descCore (x.dcK γ0 γc γm rp g (.go j iL γi)) d y g.ev.b ∗
        (swift.descRest (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.go j iL γi)).kf d y)) ∗
    replica.mset.ownD s qS szS memS (swift.ackP y) swift.ackA
      (swift.leadAckP (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y) iprop(True) hd ∗
    swift.epochRd (x.dcK γ0 γc γm rp g (.go j iL γi)).γe (x.dcK γ0 γc γm rp g (.go j iL γi)).γxe (x.dcK γ0 γc γm rp g (.go j iL γi)).rp (x.dcK γ0 γc γm rp g (.go j iL γi)).rr q g.ev.b bw stp rcp ∗
    swift.shOwn (x.dcK γ0 γc γm rp g (.go j iL γi)) d g.ev.b q ∗ RC rcp bw ∗
    -- `descF` but its `msgs` half
    swift.dfld d go!"phase" ↦ dv.phase ∗
    swift.dfld d go!"cmd" ↦ state.Command.mk dv.c.op dv.c.key dv.vs ∗ dv.vs ↦*□ dv.c.val ∗
    swift.dfld d go!"dep" ↦ dv.dep ∗ dv.dep ↦*□ dv.D ∗
    typedPointsto (swift.dfld d go!"hs") dv.hs (DFrac.own (1 : Qp).half) ∗ dv.hs ↦*□ dv.Hs ∗
    typedPointsto (swift.dfld d go!"propose") dv.propose (DFrac.own (1 : Qp).half) ∗
    typedPointsto (swift.dfld d go!"seq") dv.seq (DFrac.own (1 : Qp).half.half) ∗
    isChanBag γmc dv.msgs (swift.MPi g y γi γsg) ∗
    sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d) ∗ ⌜dv.c.op ≠ W8 3⌝ ∗
    swift.rowTokO (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y dv rv ∗
    (⌜rv.2.2.2 = false⌝ ∨ sp.committed (x.dcK γ0 γc γm rp g (.go j iL γi)).γ (x.dcK γ0 γc γm rp g (.go j iL γi)).r g.ev.b (toCmdId y)) ∗
    (swift.rowAcc (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y dv rv ∗
      swift.repPre (x.dcK γ0 γc γm rp g (.go j iL γi)).γ (x.dcK γ0 γc γm rp g (.go j iL γi)).N
        (x.dcK γ0 γc γm rp g (.go j iL γi)).r g.ev.b y dv) ∗
    ⌜dv.phase = swift.phCOMMIT → rv.2.2.2 = true ∨ dv.propose = null⌝ ∗
    swift.phaseWhy (x.dcK γ0 γc γm rp g (.go j iL γi)).γ (x.dcK γ0 γc γm rp g (.go j iL γi)).N (x.dcK γ0 γc γm rp g (.go j iL γi)).r g.ev.b y dv ∗
    swift.depWhy (x.dcK γ0 γc γm rp g (.go j iL γi)).γ (x.dcK γ0 γc γm rp g (.go j iL γi)).γxm (x.dcK γ0 γc γm rp g (.go j iL γi)).N (x.dcK γ0 γc γm rp g (.go j iL γi)).r g.ev.b y dv ∗
    ⌜swift.rowPhaseOk (x.dcK γ0 γc γm rp g (.go j iL γi)).N (x.dcK γ0 γc γm rp g (.go j iL γi)).r g.ev.b dv rv ∧ dv.seq = (x.dcK γ0 γc γm rp g (.go j iL γi)).sq⌝ ∗
    □ swift.slotB (swift.MPi g y γi γsg) (x.dcK γ0 γc γm rp g (.go j iL γi)).γxm g.ev.b y ∗
    swift.dfld d go!"slowPathH" ↦ s ∗ swift.dfld d go!"fastPathH" ↦ f ∗
    replica.mset.ownD f qF szF memF (swift.ackP y) swift.ackA
      (swift.leadAckP (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y) iprop(True) hd ∗
    swift.descCore (x.dcK γ0 γc γm rp g (.go j iL γi)) d y g.ev.b ∗
    swift.descRest (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y d ∗
    -- `kfK` but its `active` and `stopChan` halves
    (∃ q' : Qp, ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q') ∗
    ghostVar γi (1 : Qp).half.half (x.str y, d) ∗
    ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ∗
    swift.stopBag γsc sc (swift.stopMP g.γs γsg' (x.str y) d sc) ∗ □ swift.incW g γi γsg' ∗
    swift.descOcf (x.dcK γ0 γc γm rp g (.go j iL γi)) RC (swift.MPi g y γi γsg) γmc d y g.ev.b
      iprop(swift.descRest (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y d ∗
        (x.dcK γ0 γc γm rp g (.go j iL γi)).kf d y))

/-- **`depSpecR` at every owner record of `x`** (round 44; the Löb bundle's first part, plan R8.2 (10),
D53 (3)): what T8 (`hd_toOwn`) and T7s (`seq_open`) give the owner state. Proved in DescBundle.lean
from the bundle (`wp_coreO`, TD). -/
def swift.depAll (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) : IProp netDistGF :=
  iprop(□ ∀ (rp : Loc) (g : swift.DescG) (k : swift.OwnK), swift.depSpecR (x.dcK γ0 γc γm rp g k))

instance swift.depAll_persistent (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) :
    Persistent (swift.depAll γ0 γc γm x) := by
  unfold swift.depAll; infer_instance

end stopDefs

section specsD
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- **`handleDesc.specD` with `depAll` in the pre** (round 44, D53 (3)): what the top-down proof gives;
the Löb bundle (DescBundle.lean) turns it into `handleDesc.specD`. -/
abbrev swift.Replica.handleDesc.specDD (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (RC : Loc → Loc → w32 → IProp netDistGF) : Prop :=
  ∀ (rp : Loc) (g : swift.DescG) (d : Loc) (y : swift.CommandId) (γi γsg : GName),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.goPre γ0 γc γm x rp (RC rp) g d y γi γsg ∗ swift.depAll γ0 γc γm x }}
    (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleDesc")) (Val #d))
      (Val #y))
  {{ RET #(); True }}

end specsD

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- **The stop arm on a raw goroutine** (T19Ra, T19Rh, T19x; table §3R10.21, §3R11): `goPreRaw`'s
parts but the loop's halves give `hdStopW` at `goPre`'s signal name. -/
theorem swift.hd_stopRaw (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) (d : Loc) (y : swift.CommandId) (γi γsg : GName)
    (m sc : Loc) (γmc : ChanNames) (sqv : GoInterface) (szS : Nat) (memS : w32 → Prop) (j iL : Nat)
    (q : Qp) :
    swift.goPreP γ0 γc γm x rp g ∗
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
      ghostMapElem x.γsh d (DFrac.own 1) q ∗
      swift.descRaw (x.dc γ0 γc γm rp) RC (fun v => iprop(g.mp y v ∗ □ swift.incW g γi γsg)) y g.ev.b
        sqv g.ev.fq szS g.ev.szF memS g.ev.memF γmc d ∗
      swift.epochShare (x.epN rp) g.ev q ∗ (∃ dm : GoSlice, swift.descX rp x.γd g dm q) ∗
      swift.epochLoan g.γq iL q ∗
      ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ∗
      ⌜j ≠ 0⌝ ∗ ghostMapElem x.γn j (DFrac.own (1 : Qp).half) false ∗ swift.delReader x.dm x.γdl ∗
      ghostVar γi (1 : Qp).half.half (x.str y, d) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ⊢
    swift.hdStopW x g d y sc m γsg (swift.incW g γi γsg) := by
  iintro ⟨#HP, Hseq, Hsh, Hraw, Hes, ⟨%dm, HX⟩, Hloan, Hlj, %-, Hn, Hrdr, Hv, Hr⟩
  ihave #HP2 := HP
  iunfold swift.goPreP at HP2
  icases HP2 with ⟨-, -, -, #HI, -⟩
  iunfold swift.hdStopW
  iintro %wg Hlc Hreq #Hw Ha
  iunfold swift.stopMP at Hreq
  icases Hreq with ⟨Hdone, Hsg, Hel⟩
  imod swift.descInv_stopTake γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b) x.str iL q d y γi γsg j
    $$ [Hlc Hloan Hv Hr Hseq Ha Hsg Hel] with ⟨Hloan, Hv, Hr, Hseq, Ha, Hsg, Hel⟩
  · iframe HI Hlc Hloan Hw Hv Hr Hseq Ha Hsg Hel
  imodintro
  iframe Ha Hsg Hdone Hel
  iintro Hlc1 Hlc2 - Ha Hsc Hm Hel
  imod swift.descInv_stopHomeR γ0 x.γv x.γe x.γo x.sn x.k x.γsh x.γd x.γn x.γout g (x.epN rp) x.str
      iL q d y γi γsg j m sc (x.dc γ0 γc γm rp) rfl RC _ g.ev.b sqv g.ev.fq szS g.ev.szF memS
      g.ev.memF γmc q
    $$ [Hlc1 Hloan Hv Hr Hel Hseq Hm Hsc Ha Hraw Hsh] with ⟨Hloan, Hn2, Hel1, Hel2⟩
  · iframe HI Hlc1 Hloan Hw Hv Hr Hel Hseq Hm Hsc Ha Hraw Hsh
  imod swift.descInv_returnLoan γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b) (swift.descGo x.γn g x.str)
      x.str iL q j (1 : Qp).half.half dm
    $$ [Hlc2 Hes HX Hloan Hlj] with Hn3
  · iframe HI Hlc2 Hes Hloan Hlj
    iExactEq HX; rfl
  imodintro
  isplitl [Hel1 Hel2]
  · iapply (ghostMapElem_halves g.γs (x.str y) true).2
    iframe
  iexists j
  iframe Hrdr
  ihave Hq := (swift.elem_quarters x.γn j false).2 $$ [Hn2 Hn3]
  · iframe
  iapply (ghostMapElem_halves x.γn j false).2
  iframe

/-- **The stop arm on a goroutine at its owner form** (T19a.g, T19h, T19x; table §3R11 T19a.g-T19x):
T19a.g `descInv_stopTake` with `envK`'s loan; T19h `descInv_stopHome` over the token path
(`stopHome_restTok`, the rest record `retWhy (rest d γi)` from `descSt`'s facts) or the tokenless
`descRestA`; T19x `descInv_returnLoanO` with `shOwnR`'s pin; `ownRdr` → `delReader x.dm` by
`descDSCtx`'s `delivered ↦□ x.dm` (11-2). -/
theorem swift.hd_stopOwn (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) (d : Loc) (y : swift.CommandId) (γi γsg : GName)
    (j iL : Nat) (γmc : ChanNames) (sc m : Loc) (γsc : ChanNames) (γsg' : GName) (W : IProp netDistGF) :
    swift.goPreP γ0 γc γm x rp g ∗
      swift.hdOwnRes γ0 γc γm x rp RC g d y γi γsg j iL γmc sc m γsc γsg' ⊢
    swift.hdStopW x g d y sc m γsg' W := by
  iintro ⟨#HP, H⟩
  ihave #HP2 := HP
  iunfold swift.goPreP at HP2
  icases HP2 with ⟨#Hctx, #Hdsc, -, #HI, -⟩
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm', %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, -, -, -, -, -,
    -, #HN, -⟩
  iunfold swift.hdOwnRes at H
  icases H with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, %q, %bw, %stp, %rcp, %dv, %rv,
    %Hmm, -, -, HdS, Hrd, Hsh, -, Hph', Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hprop, Hseq, -, #HsL, %Hop,
    Htok, Hcom, ⟨#Hra, #HrP⟩, %Hph, #Hpw, #Hdw, %Hrp, -, HsF, HfF, HdF, Hcore, Hrest, ⟨%q', Hshk⟩, Hv, Hjr,
    -, #Hw, Hocf⟩
  have hsq : dv.seq = false := Hrp.2
  isimp only [hsq] at Hseq
  -- the epoch fields and the loan environment
  iunfold swift.shOwn at Hsh
  icases Hsh with ⟨Hshe, HshR⟩
  iunfold swift.shOwnR at HshR
  icases HshR with ⟨⟨%st, Hst⟩, ⟨%fq, %szF', %memF', Hfq, -⟩, Hrdr, Henv, Hpin⟩
  ihave Henv : swift.envK γ0 γc γm x rp g (.go j iL γi) d q $$ [Henv]
  · iExactEq Henv; rfl
  iunfold swift.envK at Henv
  icases Henv with ⟨Hloan, Hlj, Hnj, ⟨%dm, HX⟩, #HE⟩
  -- round 56 (D79 (1), 52-3): the epoch's registration, for the rest record's `cgW`
  iunfold swift.epInvs at HE
  icases HE with ⟨-, -, #HoC⟩
  iunfold swift.ownCtx at HoC
  icases HoC with ⟨-, -, -, -, -, #Hcg⟩
  ihave Hshe : ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q $$ [Hshe]
  · iExactEq Hshe; rfl
  icombine Hshe Hshk gives %Hqq
  obtain ⟨-, Hqq⟩ := Hqq
  subst Hqq
  ihave Hshw := (ghostMapElem_halves x.γsh d q).2 $$ [Hshe Hshk]
  · iframe
  -- `afterPropagate`, `propose`'s other half, `storedBallots`
  iunfold swift.descOcf at Hocf
  icases Hocf with ⟨%cf, %cond, %fs, %v, Hocfr, -, -, -⟩
  iunfold swift.ocfRes at Hocfr
  icases Hocfr with ⟨Hapf, Hown, Hpv, %sb, %bs, Hsb, -, -, -⟩
  iunfold swift.proposeHalf at Hpv
  icases Hpv with ⟨%p, Hp2, -⟩
  icombine Hprop Hp2 gives %Hpe
  subst Hpe
  ihave Hoa : swift.ocfAny cf $$ [Hown]
  · iunfold swift.ocfAny
    iright
    iunfold hook.ocf.ownOcf at Hown
    icases Hown with ⟨%osl, %oL, Hown⟩
    iexists cond, fs, osl, oL
    iexact Hown
  -- `descRest`, `descCore`
  iunfold swift.descRest at Hrest
  icases Hrest with ⟨%pd, %hs0, %sqn, %df, Hpd, Hsqn, Hhs0, Hdf, #Hpdk⟩
  icombine Hhs Hhs0 gives %Hhe
  subst Hhe
  ihave Hhsw := (swift.pt_halves (swift.dfld d go!"hs") dv.hs).2 $$ [Hhs Hhs0]
  · iframe
  iunfold swift.descCore at Hcore
  icases Hcore with ⟨%wa, %slp, Hwa, Hslp, -⟩
  ihave HfS := swift.ownD_free _ _ _ _ _ _ _ _ $$ HdS
  ihave HfF' := swift.ownD_free _ _ _ _ _ _ _ _ $$ HdF
  ihave #Hra2 := Hra
  iunfold swift.rowAcc at Hra2
  icases Hra2 with ⟨#Hacc, %Hsome, #Hpp⟩
  -- the stop arm
  iunfold swift.hdStopW
  iintro %wg Hlc Hreq #HW Ha
  iunfold swift.stopMP at Hreq
  icases Hreq with ⟨Hdone, Hsg, Hel⟩
  -- T19a.g
  imod swift.descInv_stopTake γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b) x.str iL q d y γi γsg' j
    $$ [Hlc Hloan Hv Hjr Hseq Ha Hsg Hel] with ⟨Hloan, Hv, Hjr, Hseq, Ha, Hsg, Hel⟩
  · iframe HI Hlc Hloan Hw Hv Hjr Hseq Ha Hsg Hel
  imodintro
  iframe Ha Hsg Hdone Hel
  iintro Hlc1 Hlc2 Hlc3 Ha Hsc Hm Hel
  subst Hmm
  iunfold swift.rowTokO at Htok
  icases Htok with (⟨Htk, Hsx⟩ | ⟨%Hemp, -, Hslot⟩)
  · -- T19h, the token path (`stopHome_restTok`)
    iunfold swift.slotT at Hsx
    icases Hsx with ⟨Hslot, Htx⟩
    ihave Hslot : swift.outRcpt x.sn.γout (g.ev.b, toCmdId y) (j, (1 : Qp).half.half) $$ [Hslot]
    · iExactEq Hslot; rfl
    ihave Htx : swift.tixOr x.sn.γxu x.sn.γxm (g.ev.b, toCmdId y) $$ [Htx]
    · iExactEq Htx; rfl
    ihave Htk : swift.rowTok x.γo (g.ev.b, toCmdId y).1 (g.ev.b, toCmdId y).2 rv $$ [Htk]
    · iExactEq Htk; rfl
    icases (swift.pt_halves (swift.dfld d go!"phase") dv.phase).1 $$ Hph' with ⟨Hph1, Hph2⟩
    icases (swift.pt_halves (swift.dfld d go!"dep") dv.dep).1 $$ Hdep with ⟨Hdep1, Hdep2⟩
    icases (swift.pt_quarters (swift.dfld d go!"propose") dv.propose).1 $$ Hp2 with ⟨Hp3, Hp4⟩
    ihave HRH : swift.descRestH γ0 x.sn x.γsh g.ev.b (g.ev.b, toCmdId y) d $$ [Hshw Hph1 Hcmd Hdep1
        Hhsw Hsqn Hprop Hp3 Hpd Hapf Hoa Hslp Hdf Hwa Hsb]
    · iunfold swift.descRestH
      iexists q, dv.phase, sqn, dv.c, dv.vs, dv.dep, dv.hs, pd, sb, dv.propose, cf, wa, slp, df
      iframe Hshw HsL Hph1 Hcmd Hvs Hdep1 Hhsw Hsqn Hprop Hp3 Hpd Hapf Hoa Hslp Hdf Hwa Hsb
      isplitr
      · ipureintro; exact Hop
      -- round 58 (D82 (1)): the claim's key, `proposeDep`'s facts, `cmd`'s proposal
      iexists y, _
      isplitl []
      · iexact Hpdk
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      ihave #HhP := swift.repPre_homeP _ _ _ _ _ _ $$ [HrP HD]
      · iframe HrP HD
      iExactEq HhP; rfl
    ihave Hwhy : (ghostVar γi (1 : Qp).half (x.sn.str y, d) -∗
        swift.retWhy γ0 x.sn.γxm x.sn.γcg x.sn.str x.sn.N x.sn.r (g.ev.b, toCmdId y) rv
          (swift.recOf (.rest d γi))) $$ [Hph2 Hdep2 Hp4 Hcom]
    · iintro Hvh
      isimp only [swift.recOf]
      iunfold swift.retWhy
      iexists y, dv
      iframe Hvh Hph2 Hdep2 Hp4
      isplitr
      · ipureintro; exact ⟨rfl, Hrp.1⟩
      isplitr
      · iunfold swift.stopFacts
        icases Hpp with (%Hn | ⟨%gv, #Hgv⟩)
        · ileft; ipureintro; exact Hn
        · iright
          iframe HD
          isplitr
          · iexists gv; iexact Hgv
          isplitr
          · iExactEq Hpw; rfl
          isplitr
          · iExactEq Hdw; rfl
          -- round 52 (51-5): the proposal's `propIs`, from the owner's `repPre` (T19)
          ihave #HpP := swift.repPre_propIs _ _ _ _ _ _ $$ HrP
          icases HpP with (%Hn' | #HpI)
          · ihave %hnn := typedPointsto_not_null _ _ _ $$ Hgv
            exfalso; exact hnn Hn'
          iExactEq HpI; rfl
      isplitl [Hcom]
      · iunfold swift.rowFacts
        isplitl [Hcom]
        · iExactEq Hcom; rfl
        isplitr
        · iExactEq Hacc; rfl
        isplitr
        · ipureintro; exact Hsome
        isplitr
        · iexact Hpp
        ipureintro; exact Hph
      -- round 56 (D79 (1), 52-3): the incarnation's commit witness by ballot
      iapply swift.cgW_of x g γi γsg'
      iframe Hcg Hw
    imod swift.descInv_stopHome γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b) x.str iL q d y γi γsg' j
        dv.msgs sc s f
        iprop(inv swift.nodeN (swift.nodeInvD γ0 x.γv x.γe x.γo x.sn x.k) ∗
          swift.rowTok x.γo (g.ev.b, toCmdId y).1 (g.ev.b, toCmdId y).2 rv ∗
          swift.tixOr x.sn.γxu x.sn.γxm (g.ev.b, toCmdId y) ∗
          swift.outRcpt x.sn.γout (g.ev.b, toCmdId y) (j, (1 : Qp).half.half) ∗
          (ghostVar γi (1 : Qp).half (x.sn.str y, d) -∗
            swift.retWhy γ0 x.sn.γxm x.sn.γcg x.sn.str x.sn.N x.sn.r (g.ev.b, toCmdId y) rv
              (swift.recOf (.rest d γi))) ∗
          swift.descRestH γ0 x.sn x.γsh g.ev.b (g.ev.b, toCmdId y) d)
        (ghostMapElem x.γn (j, (1 : Qp).half.half).1 (DFrac.own (j, (1 : Qp).half.half).2) false)
        (swift.stopHome_restTok γ0 x.γv x.γe x.γo x.sn x.k x.γsh x.γn d y γi (g.ev.b, toCmdId y) rv
          (j, (1 : Qp).half.half) g.ev.b)
      $$ [Hlc1 Hloan Hv Hjr Hel Hseq Hm Hsc Ha HsF HfF HfS HfF' Htk Htx Hslot Hwhy HRH]
      with ⟨Hloan, Hn2, Hel1, Hel2, Hn3⟩
    · iframe HI Hlc1 Hloan Hw Hv Hjr Hel Hseq Hm Hsc Ha HsF HfF HfS HfF' Htk Htx Hslot Hwhy HRH
      iExactEq HN; rfl
    -- T19x
    imod swift.descInv_returnLoanO γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b) (swift.descGo x.γn g x.str)
        x.str iL q j (1 : Qp).half.half dm g.ev.b bw stp rcp st fq
      $$ [Hlc2 Hlc3 Hrd Hpin Hst Hfq HX Hloan Hlj] with Hn4
    · iframe HI Hlc2 Hlc3 Hloan Hlj
      isplitl [Hrd]
      · iExactEq Hrd; rfl
      isplitl [Hpin]
      · iExactEq Hpin; rfl
      isplitl [Hst]
      · iExactEq Hst; rfl
      isplitl [Hfq]
      · iExactEq Hfq; rfl
      iExactEq HX; rfl
    imodintro
    isplitl [Hel1 Hel2]
    · iapply (ghostMapElem_halves g.γs (x.str y) true).2
      iframe
    iexists j
    isplitl [Hnj Hn2 Hn3 Hn4]
    · ihave Hnj : ghostMapElem x.γn j (DFrac.own (1 : Qp).half.half) false $$ [Hnj]
      · iExactEq Hnj; rfl
      ihave Hq1 := (swift.elem_quarters x.γn j false).2 $$ [Hnj Hn3]
      · iframe
      ihave Hq2 := (swift.elem_quarters x.γn j false).2 $$ [Hn2 Hn4]
      · iframe
      iapply (ghostMapElem_halves x.γn j false).2
      iframe
    iunfold swift.ownRdr at Hrdr
    icases Hrdr with ⟨%dm2, #Hdl, Hrv⟩
    ihave #Hdsc2 := Hdsc
    iunfold swift.descDSCtx at Hdsc2
    icases Hdsc2 with ⟨-, -, -, -, -, #Hdl2⟩
    ihave #Hdl : swift.fld rp go!"delivered" ↦□ dm2 $$ [Hdl]
    · iExactEq Hdl; rfl
    icombine Hdl Hdl2 gives %Hdeq
    subst Hdeq
    iExactEq Hrv; rfl
  · -- T19h, tokenless (`descRestA`)
    obtain ⟨Hrv, Hpn⟩ := Hemp
    ihave Hslot : ghostMapElem x.γn j (DFrac.own (1 : Qp).half.half) false $$ [Hslot]
    · iExactEq Hslot; rfl
    ihave Hpw2 := (swift.pt_halves (swift.dfld d go!"propose") dv.propose).2 $$ [Hprop Hp2]
    · iframe
    ihave Hpw2 : swift.dfld d go!"propose" ↦ (null : Loc) $$ [Hpw2]
    · iExactEq Hpw2; rw [Hpn]
    -- round 58 (D82 (1)): the home keeps the incarnation's half and its commit witness by ballot
    -- (the stopped view's key of `proposeDep`'s command, for `desc`)
    ihave #HcgW := swift.cgW_of x g γi γsg' $$ [Hcg Hw]
    · iframe Hcg Hw
    ihave HRA : ghostVar γi (1 : Qp).half (x.str y, d) -∗ swift.descRestT γ0 x.sn x.γsh g.ev.b d $$
        [Hshw Hph' Hcmd Hdep Hhsw Hsqn Hpw2 Hpd Hapf Hoa Hslp Hdf Hwa Hsb]
    · iintro Hgv
      iunfold swift.descRestT
      iexists q, dv.phase, sqn, dv.c, dv.vs, dv.dep, dv.hs, pd, sb, cf, wa, slp, df, dv.D
      iframe Hshw HsL Hph' Hcmd Hvs Hdep HD Hhsw Hsqn Hpw2 Hpd Hapf Hoa Hslp Hdf Hwa Hsb
      isplitr
      · ipureintro; exact Hop
      iright
      iexists _, y, γi
      isplitl []
      · iexact Hpdk
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iframe Hgv HcgW
    have hDR : swift.ledgerD x.γn x.γout ∗ ghostVar γi (1 : Qp).half (x.str y, d) ∗
        (ghostVar γi (1 : Qp).half (x.str y, d) -∗ swift.descRestT γ0 x.sn x.γsh g.ev.b d) ⊢
        |={⊤ \ ↑swift.descN}=> swift.ledgerD x.γn x.γout ∗ x.DR γ0 g.ev.b d ∗ iprop(True) := by
      iintro ⟨Hled, Hgv, HRA⟩
      imodintro
      iframe Hled
      isplitl [HRA Hgv]
      · iapply swift.descRestT_S
        iapply HRA $$ Hgv
      itrivial
    imod swift.descInv_stopHome γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b) x.str iL q d y γi γsg' j
        dv.msgs sc s f iprop(ghostVar γi (1 : Qp).half (x.str y, d) -∗
          swift.descRestT γ0 x.sn x.γsh g.ev.b d) iprop(True) hDR
      $$ [Hlc1 Hloan Hv Hjr Hel Hseq Hm Hsc Ha HsF HfF HfS HfF' HRA]
      with ⟨Hloan, Hn2, Hel1, Hel2, -⟩
    · iframe HI Hlc1 Hloan Hw Hv Hjr Hel Hseq Hm Hsc Ha HsF HfF HfS HfF' HRA
    imod swift.descInv_returnLoanO γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b) (swift.descGo x.γn g x.str)
        x.str iL q j (1 : Qp).half.half dm g.ev.b bw stp rcp st fq
      $$ [Hlc2 Hlc3 Hrd Hpin Hst Hfq HX Hloan Hlj] with Hn4
    · iframe HI Hlc2 Hlc3 Hloan Hlj
      isplitl [Hrd]
      · iExactEq Hrd; rfl
      isplitl [Hpin]
      · iExactEq Hpin; rfl
      isplitl [Hst]
      · iExactEq Hst; rfl
      isplitl [Hfq]
      · iExactEq Hfq; rfl
      iExactEq HX; rfl
    imodintro
    isplitl [Hel1 Hel2]
    · iapply (ghostMapElem_halves g.γs (x.str y) true).2
      iframe
    iexists j
    isplitl [Hnj Hn2 Hslot Hn4]
    · ihave Hnj : ghostMapElem x.γn j (DFrac.own (1 : Qp).half.half) false $$ [Hnj]
      · iExactEq Hnj; rfl
      ihave Hq1 := (swift.elem_quarters x.γn j false).2 $$ [Hnj Hslot]
      · iframe
      ihave Hq2 := (swift.elem_quarters x.γn j false).2 $$ [Hn2 Hn4]
      · iframe
      iapply (ghostMapElem_halves x.γn j false).2
      iframe
    iunfold swift.ownRdr at Hrdr
    icases Hrdr with ⟨%dm2, #Hdl, Hrv⟩
    ihave #Hdsc2 := Hdsc
    iunfold swift.descDSCtx at Hdsc2
    icases Hdsc2 with ⟨-, -, -, -, -, #Hdl2⟩
    ihave #Hdl : swift.fld rp go!"delivered" ↦□ dm2 $$ [Hdl]
    · iExactEq Hdl; rfl
    icombine Hdl Hdl2 gives %Hdeq
    subst Hdeq
    iExactEq Hrv; rfl

/-- **The loop's fields out of `hdInv`, and back** (both forms): half of `active` (at `true`), half
of `stopChan` and of `msgs`, the two channels' bags (the stop bag at its own signal name `γsg'`:
`goPre`'s at `γsg`, `kfK`'s at its `∃ γsg`, A12). Round 44: with the stop arm's capability
`hdStopW` (T19, `hd_stopRaw`/`hd_stopOwn`) as the other side of a conjunction. -/
theorem swift.hd_open (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) (d : Loc) (y : swift.CommandId) (γi γsg : GName) :
    swift.goPreP γ0 γc γm x rp g ∗ swift.hdInv γ0 γc γm x rp RC g d y γi γsg ⊢
      ∃ (sc m : Loc) (γsc γmc : ChanNames) (γsg' : GName) (W : IProp netDistGF),
        typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗
        typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half) ∗
        typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half) ∗
        isChanBag γmc m (swift.MPi g y γi γsg) ∗
        isChanBag γsc sc (fun wg => iprop(swift.stopMP g.γs γsg' (x.str y) d sc wg ∗ □ W)) ∗
        ((typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) -∗
          typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half) -∗
          typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half) -∗
          swift.hdInv γ0 γc γm x rp RC g d y γi γsg) ∧
         swift.hdStopW x g d y sc m γsg' W) := by
  iintro ⟨#HP, H⟩
  iunfold swift.hdInv at H
  icases H with (Hr | ⟨%j, %iL, %γmc, #Hc, #Hpc, #Hdr, Hown⟩)
  · -- the raw form
    iunfold swift.goPreRaw at Hr
    icases Hr with ⟨%m, %sc, %γmc, %γsc, %sqv, %szS, %memS, %j, %iL, %q, Hm, #Hbm, Ha, Hseq, Hsc, #Hbs,
      Hrest⟩
    iexists sc, m, γsc, γmc, γsg, iprop(swift.incW g γi γsg)
    iframe Ha Hsc Hm Hbm Hbs
    isplit
    · iintro Ha Hsc Hm
      iunfold swift.hdInv
      ileft
      iunfold swift.goPreRaw
      iexists m, sc, γmc, γsc, sqv, szS, memS, j, iL, q
      iframe
      iframe Hbm Hbs
    · icases Hrest with ⟨Hsh, Hraw, Hes, HX, Hloan, Hlj, %Hj0, Hn, Hrdr, Hv, Hr, -⟩
      iapply swift.hd_stopRaw γ0 γc γm x rp RC g d y γi γsg m sc γmc sqv szS memS j iL q
      iframe HP Hseq Hsh Hraw Hes HX Hloan Hlj Hn Hrdr Hv Hr
      ipureintro; exact Hj0
  · -- the owner form
    iunfold swift.descOwnF at Hown
    icases Hown with ⟨Ho, Hocf⟩
    iunfold swift.descOwn at Ho
    icases Ho with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #Hhd, #Hcap, HdS, HR⟩
    iunfold swift.setR at HR
    iunfold swift.descSt at HR
    icases HR with ⟨%q, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, ⟨#Hra, #HrP⟩, %Hph, #Hpw,
      #Hdw, %Hrp, #HsB, ⟨HsF, HfF, HdF, Hcore, Hrest, Hkf⟩⟩
    iunfold swift.descF at Hd
    icases Hd with ⟨Hph', Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hprop, Hseq, Hm, #Hbm, #HsL, %Hop⟩
    ihave Hkf : swift.kfK x g (.go j iL γi) d y $$ [Hkf]
    · iExactEq Hkf; rfl
    iunfold swift.kfK at Hkf
    isimp only [swift.OwnK.isSeq, Bool.false_eq_true, ↓reduceIte] at Hkf
    icases Hkf with ⟨Ha, Hshk, Hv, Hjr, %sc, %γsc, %γsg', Hsc, #Hbs, #Hw⟩
    iunfold swift.stopBag at Hbs
    icases Hbs with ⟨%W, #Hbs, #HW⟩
    iexists sc, dv.msgs, γsc, γmc, γsg', W
    iframe Ha Hsc Hm Hbs
    isplitr
    · iExactEq Hbm; rfl
    isplit
    · iintro Ha Hsc Hm
      ihave Hkf : swift.kfK x g (.go j iL γi) d y $$ [Ha Hshk Hv Hjr Hsc]
      · iunfold swift.kfK
        isimp only [swift.OwnK.isSeq, Bool.false_eq_true, ↓reduceIte]
        iframe Ha Hshk Hv Hjr
        iexists sc, γsc, γsg'
        iframe Hsc Hw
        iunfold swift.stopBag
        iexists W
        iframe Hbs HW
      iunfold swift.hdInv
      iright
      iexists j, iL, γmc
      iframe Hc Hpc Hdr
      iunfold swift.descOwnF
      iframe Hocf
      iunfold swift.descOwn
      iexists s, f, qS, qF, szS, szF, memS, memF, hd
      iframe Hhd Hcap HdS
      iunfold swift.setR
      iunfold swift.descSt
      iexists q, bw, stp, rcp, dv, rv
      iframe Hrd Hsh HRC Htok Hcom Hra HrP Hpw Hdw HsB HsF HfF HdF Hcore Hrest
      isplitl [Hph' Hcmd Hdep Hhs Hprop Hseq Hm]
      · iunfold swift.descF
        iframe Hph' Hcmd Hvs Hdep HD Hhs HHs Hprop Hseq Hm Hbm HsL
        ipureintro; exact Hop
      isplitr
      · ipureintro; exact Hph
      isplitr
      · ipureintro; exact Hrp
      iExactEq Hkf; rfl
    · isimp only [↓reduceIte] at HdF
      isimp only [swift.OwnK.γi, swift.OwnK.jq] at Hv Hjr Hw
      iapply swift.hd_stopOwn γ0 γc γm x rp RC g d y γi γsg j iL γmc sc dv.msgs γsc γsg' W
      iframe HP
      iunfold swift.hdOwnRes
      iexists s, f, qS, qF, szS, szF, memS, memF, hd, q, bw, stp, rcp, dv, rv
      iframe Hhd Hcap HdS Hrd Hsh HRC Hph' Hcmd Hvs Hdep HD Hhs HHs Hprop Hseq HsL Htok Hcom Hra HrP
        Hpw Hdw HsB HsF HfF HdF Hcore Hrest Hshk Hv Hjr Hw Hocf
      isplitr
      · ipureintro; rfl
      isplitr
      · iExactEq Hbm; rfl
      isplitr
      · ipureintro; exact Hop
      isplitr
      · ipureintro; exact Hph
      isplitr
      · ipureintro; exact Hrp
      iunfold swift.stopBag
      iexists W
      iframe Hbs HW

/-- The epoch's message predicate at an owner record (`mpOk`, `descMP_dcK`). -/
theorem swift.mp_dcK (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) (g : swift.DescG)
    (k : swift.OwnK) (y : swift.CommandId) (m : GoInterface) (h : swift.mpOk x γ γc γm rp g) :
    g.mp y m ⊢ swift.descMP (x.dcK γ γc γm rp g k) g.ev.b y (swift.slotMP x.γxm g.ev.b y)
      (swift.syncMP γ x.γcl x.r (sp.leaderOf x.N g.ev.b) g.ev.b y) m := by
  rw [h]; exact .rfl

/-- A history slot's message is of the epoch's predicate (`mpOk`). -/
theorem swift.mp_of_slot (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) (g : swift.DescG)
    (y : swift.CommandId) (m : GoInterface) (h : swift.mpOk x γ γc γm rp g) :
    swift.slotMP x.γxm g.ev.b y m ⊢ g.mp y m := by
  rw [h]
  iintro H
  iunfold swift.descMP
  iright; iright; ileft; iexact H

/-- **T8: the first message makes the raw form the owner form** (`descRaw_own` with `slotCap`, the
record's `ctx`/`proposeCtx`/`depSpecR`; the owner form is unchanged). -/
theorem swift.hd_toOwn (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) (d : Loc) (y : swift.CommandId) (γi γsg : GName)
    (m : GoInterface) :
    swift.goPreP γ0 γc γm x rp g ∗ swift.depAll γ0 γc γm x ∗ swift.hdInv γ0 γc γm x rp RC g d y γi γsg ∗
      swift.MPi g y γi γsg m ⊢
    |={⊤}=> swift.MPi g y γi γsg m ∗ ∃ (j iL : Nat) (γmc : ChanNames),
      (x.dcK γ0 γc γm rp g (.go j iL γi)).ctx ∗ □ swift.proposeCtx (x.dcK γ0 γc γm rp g (.go j iL γi)) ∗
      swift.depSpecR (x.dcK γ0 γc γm rp g (.go j iL γi)) ∗
      swift.descOwnF (x.dcK γ0 γc γm rp g (.go j iL γi)) RC (swift.MPi g y γi γsg) γmc d y g.ev.b
        iprop(swift.descRest (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.go j iL γi)).kf d y) := by
  iintro ⟨#HP, #Hdep, H, Hm⟩
  iunfold swift.hdInv at H
  icases H with (Hr | ⟨%j, %iL, %γmc, #Hc, #Hpc, #Hdr, Hown⟩)
  rotate_left
  · imodintro
    iframe Hm
    iexists j, iL, γmc
    iframe Hc Hpc Hdr Hown
  ihave #HP2 := HP
  iunfold swift.goPreP at HP2
  icases HP2 with ⟨#Hctx, #Hdsc, #Hown, #HI, %Hmp⟩
  ihave #Hown2 := Hown
  iunfold swift.ownCtx at Hown2
  icases Hown2 with ⟨-, #HpB, -, -, -, -⟩
  iunfold swift.goPreRaw at Hr
  icases Hr with ⟨%m', %sc, %γmc, %γsc, %sqv, %szS, %memS, %j, %iL, %q, Hmsg, #Hbm, Ha, Hseq, Hsc,
    #Hbs, Hsh, Hraw, Hes, ⟨%dm, HX⟩, Hloan, Hlj, %Hj0, Hn, Hrdr, Hv, Hjr, #HSI, #HRCe⟩
  icases Hm with ⟨Hmp, #Hw⟩
  iunfold swift.epochShare at Hes
  icases Hes with ⟨Hrd, Hpin, Hst, Hfq⟩
  iunfold swift.fqShare at Hfq
  icases Hfq with ⟨Hfq, #Hqi, %Hfqf⟩
  icases (ghostMapElem_halves x.γsh d q).1 $$ Hsh with ⟨Hsh1, Hsh2⟩
  icases (swift.elem_quarters x.γn j false).1 $$ Hn with ⟨Hn1, Hn2⟩
  ihave #Hdsc2 := Hdsc
  iunfold swift.descDSCtx at Hdsc2
  icases Hdsc2 with ⟨-, -, -, -, -, #Hdl⟩
  ihave Hrdr := swift.ownRdr_of rp x.γdl x.dm $$ [Hrdr]
  · iframe Hdl Hrdr
  imodintro
  isplitl [Hmp]
  · isimp only [swift.MPi]
    iframe Hmp Hw
  iexists j, iL, γmc
  isplitr
  · iExactEq Hctx; rfl
  isplitr
  · imodintro
    iapply swift.proposeCtx_ofB
    isplitr
    · iExactEq HpB; rfl
    iapply swift.takeLaw_dcK
    iExactEq Hctx; rfl
  isplitr
  · iunfold swift.depAll at Hdep
    iapply Hdep
  iapply swift.descRaw_own (x.dcK γ0 γc γm rp g (.go j iL γi)) RC (swift.MPi g y γi γsg) y g.ev.b sqv
    g.ev.fq szS g.ev.szF memS g.ev.memF γmc d m' false q g.ev.bw g.ev.stp g.ev.rcp
    ((x.dcK γ0 γc γm rp g (.go j iL γi)).kf d y) rfl (x.dc γ0 γc γm rp) rfl
  isplitl [Hraw]
  · iExactEq Hraw; rfl
  isplitr
  · iunfold swift.slotCap; ileft; ipureintro; rfl
  isplitl [Hmsg]
  · iexact Hmsg
  isplitr
  · iexact Hbm
  isplitl [Hseq]
  · iexact Hseq
  isplitl [Hrd]
  · iExactEq Hrd; rfl
  isplitl [Hsh1 Hst Hfq Hrdr Hloan Hlj Hn1 HX Hpin]
  · iunfold swift.shOwn
    isplitl [Hsh1]
    · iExactEq Hsh1; rfl
    iunfold swift.shOwnR
    isplitl [Hst]
    · iexists g.ev.st; iExactEq Hst; rfl
    isplitl [Hfq]
    · iexists g.ev.fq, g.ev.szF, g.ev.memF
      isplitl [Hfq]
      · iExactEq Hfq; rfl
      iframe Hqi
      ipureintro; exact Hfqf
    isplitl [Hrdr]
    · iExactEq Hrdr; rfl
    isplitl [Hloan Hlj Hn1 HX]
    · ihave Henv : swift.envK γ0 γc γm x rp g (.go j iL γi) d q $$ [Hloan Hlj Hn1 HX]
      · simp only [swift.envK]
        iframe Hloan Hlj Hn1
        isplitl [HX]
        · iexists dm; iexact HX
        iunfold swift.epInvs
        iframe HI HSI Hown
      iExactEq Henv; rfl
    iExactEq Hpin; rfl
  isplitr
  · iexact HRCe
  isplitl [Ha Hsh2 Hv Hjr Hsc]
  · ihave Hkf : swift.kfK x g (.go j iL γi) d y $$ [Ha Hsh2 Hv Hjr Hsc]
    · iunfold swift.kfK
      isimp only [swift.OwnK.isSeq, Bool.false_eq_true, ↓reduceIte, swift.OwnK.γi, swift.OwnK.jq]
      iframe Ha Hv Hjr
      isplitl [Hsh2]
      · iexists q; iexact Hsh2
      iexists sc, γsc, γsg
      iframe Hsc Hw
      iunfold swift.stopBag
      iexists iprop(swift.incW g γi γsg)
      iframe Hbs Hw
    iExactEq Hkf; rfl
  isplitl [Hn2]
  · iExactEq Hn2; rfl
  isplitr
  · iunfold swift.depAll at Hdep
    iapply Hdep
  imodintro
  iunfold swift.slotB
  iintro %s %Hs #Hex
  isplitr
  · iapply swift.mp_of_slot x γ0 γc γm rp g y _ Hmp
    iunfold swift.slotMP
    iexists s
    isplitr
    · ipureintro; exact ⟨rfl, Hs⟩
    iExactEq Hex; rfl
  iexact Hw

/-- **The owner state opened for the slot case by a goroutine** (T16aG's pre, `slotSpecG`): the
fields, the row token, the `γsh` half, the sets as `msetF` (D48 (3)), `descCore`, the frame
(`descRest`, `kfK`), the `OptCondF` part, the epoch share and `shOwnR` (with the pin, D51 (c));
`dv.seq = false` (`descSt`'s `dv.seq = c.sq`). -/
theorem swift.descOwnF_slotG (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) (j iL : Nat) (γi γsg : GName) (γmc : ChanNames)
    (d : Loc) (y : swift.CommandId) :
    swift.descOwnF (x.dcK γ0 γc γm rp g (.go j iL γi)) RC (swift.MPi g y γi γsg) γmc d y g.ev.b
        iprop(swift.descRest (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.go j iL γi)).kf d y) ⊢
      ∃ (dv : swift.DescV) (rv : swift.RowV) (q : Qp) (sl fa cf : Loc) (cond : GoFunc)
        (fs : List GoFunc) (v : Bool) (bw : w32) (stp rcp : Loc),
        ⌜dv.seq = false⌝ ∗ swift.descF d γmc (swift.MPi g y γi γsg) dv ∗
        swift.rowTokO (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y dv rv ∗
        ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q ∗
        swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
        swift.msetF sl ∗ swift.msetF fa ∗
        swift.descCore (x.dcK γ0 γc γm rp g (.go j iL γi)) d y g.ev.b ∗
        swift.descRest (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y d ∗ swift.ocfRes d cf cond fs v ∗
        (x.dcK γ0 γc γm rp g (.go j iL γi)).kf d y ∗
        swift.epochRd x.γe x.γxe rp x.rr q g.ev.b bw stp rcp ∗
        swift.shOwnR (x.dcK γ0 γc γm rp g (.go j iL γi)) d g.ev.b q := by
  iintro H
  iunfold swift.descOwnF at H
  icases H with ⟨Ho, Hocf⟩
  iunfold swift.descOwn at Ho
  icases Ho with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, -, -, HdS, HR⟩
  iunfold swift.setR at HR
  iunfold swift.descSt at HR
  icases HR with ⟨%q, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, -, Hd, Htok, -, -, -, -, -, %Hrp, -,
    ⟨HsF, HfF, HdF, Hcore, Hrest, Hkf⟩⟩
  iunfold swift.shOwn at Hsh
  icases Hsh with ⟨Hshe, HshR⟩
  iunfold swift.descOcf at Hocf
  icases Hocf with ⟨%cf, %cond, %fs, %v, Hocf, -, -, -⟩
  ihave Hms := swift.msetF_of _ _ _ _ _ _ _ _ $$ HdS
  ihave Hmf : swift.msetF f $$ [HdF]
  · iapply swift.msetF_of; iExactEq HdF; rfl
  iexists dv, rv, q, s, f, cf, cond, fs, v, bw, stp, rcp
  iframe
  ipureintro; exact Hrp.2

end lemmas

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

set_option goose.wp.extras true

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
