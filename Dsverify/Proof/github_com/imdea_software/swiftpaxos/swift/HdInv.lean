/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HdInv.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`handleDesc`'s loop invariant `hdInv`** (round 43, sv-swb; table §3R11a 11a.3, §3R11b 11b.4; plan
"Revision 11a" R11a.1 (6), "Revision 11b" 2).

* `swift.goPreP`: `goPre`'s persistent part (the replica's and descriptors' contexts, `ownCtx`, the
  descriptors' invariant, `mpOk`, the inbox's invariant), which the goroutine keeps across its loop.
* `swift.goPreRaw`: `goPre`'s raw part (the `∃ …` body that `newDesc` and the spawn hand over).
* `swift.goPre_split`: `goPre ⊣⊢ goPreP ∗ goPreRaw`.
* `swift.hdInv`: between two iterations of `for desc.active`, either still raw (no message read
  yet, T8 not done: R2a) or the owner state at the goroutine record `x.dcK … (.go j iL γi)` (R2b/R3)
  with its frame `descRest ∗ kfK`. **No pin and no `q`** (D51 (c)): the loan's pin is in
  `descOwnF`'s `descSt`'s `shOwnR`, at that `descSt`'s `q`.

`hdInv` sits here, above HandleProposeProof (where `proposeCtx` is) and GetDescWith (where `goPre`
is); GetDescWith imports neither this module nor HandleProposeProof.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GetDescWithDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleProposeProof

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
variable [sync.Assumptions] [hook.Assumptions]

/-- **`goPre`'s persistent part** (see the file header). -/
def swift.goPreP (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g : swift.DescG) :
    IProp netDistGF :=
  iprop((x.dc γ0 γc γm rp).ctx ∗ swift.descDSCtx rp x ∗ swift.ownCtx γ0 γc γm x rp g ∗
    inv swift.descN (swift.descInv γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b)
      (swift.descGo x.γn g x.str) x.str) ∗
    ⌜swift.mpOk x γ0 γc γm rp g⌝)

instance swift.goPreP_persistent (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (g : swift.DescG) : Persistent (swift.goPreP γ0 γc γm x rp g) := by
  unfold swift.goPreP; infer_instance

/-- **`goPre`'s raw part** (see the file header): its `∃ …` body. -/
def swift.goPreRaw (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) (d : Loc) (y : swift.CommandId)
    (γi γsg : GName) : IProp netDistGF :=
  iprop(∃ (m sc : Loc) (γmc γsc : ChanNames) (sqv : GoInterface) (szS : Nat) (memS : w32 → Prop)
      (j iL : Nat) (q : Qp),
      typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half) ∗
      isChanBag γmc m (fun v => iprop(g.mp y v ∗ □ swift.incW g γi γsg)) ∗
      typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
      typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half) ∗
      isChanBag γsc sc (fun wg => iprop(swift.stopMP g.γs γsg (x.str y) d sc wg ∗
        □ swift.incW g γi γsg)) ∗
      ghostMapElem x.γsh d (DFrac.own 1) q ∗
      swift.descRaw (x.dc γ0 γc γm rp) RC (fun v => iprop(g.mp y v ∗ □ swift.incW g γi γsg)) y g.ev.b
        sqv g.ev.fq szS g.ev.szF memS g.ev.memF γmc d ∗
      swift.epochShare (x.epN rp) g.ev q ∗ (∃ dm : GoSlice, swift.descX rp x.γd g dm q) ∗
      swift.epochLoan g.γq iL q ∗
      ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ∗
      ⌜j ≠ 0⌝ ∗ ghostMapElem x.γn j (DFrac.own (1 : Qp).half) false ∗ swift.delReader x.dm x.γdl ∗
      ghostVar γi (1 : Qp).half.half (x.str y, d) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ∗
      inv swift.seqN (swift.seqInbox g) ∗ □ RC g.ev.rcp g.ev.bw)

/-- **`handleDesc`'s loop invariant** (table §3R11a 11a.3 as restated by §3R11b 11b.4; see the file
header). Its `∃`s: `j iL` (A14: agreed by `envK`'s `γlj iL ½ (j, ¼)` with `loanRec`), `γmc` (A20:
none needed). Held together with `goPreP`. -/
def swift.hdInv (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) (d : Loc) (y : swift.CommandId)
    (γi γsg : GName) : IProp netDistGF :=
  iprop(swift.goPreRaw γ0 γc γm x rp RC g d y γi γsg ∨
    ∃ (j iL : Nat) (γmc : ChanNames),
      (x.dcK γ0 γc γm rp g (.go j iL γi)).ctx ∗ □ swift.proposeCtx (x.dcK γ0 γc γm rp g (.go j iL γi)) ∗
      swift.depSpecR (x.dcK γ0 γc γm rp g (.go j iL γi)) ∗
      swift.descOwnF (x.dcK γ0 γc γm rp g (.go j iL γi)) RC (swift.MPi g y γi γsg) γmc d y g.ev.b
        iprop(swift.descRest (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.go j iL γi)).kf d y))

end defs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- `goPre` is its persistent part and its raw part. -/
theorem swift.goPre_split (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) (d : Loc) (y : swift.CommandId)
    (γi γsg : GName) :
    swift.goPre γ0 γc γm x rp RC g d y γi γsg ⊣⊢
      swift.goPreP γ0 γc γm x rp g ∗ swift.goPreRaw γ0 γc γm x rp RC g d y γi γsg := by
  constructor
  · iintro H
    iunfold swift.goPre at H
    icases H with ⟨#Hc, #Hds, #Ho, #Hi, %Hmp, Hr⟩
    iunfold swift.goPreP
    iunfold swift.goPreRaw
    iframe Hc Hds Ho Hi Hr
    ipureintro; exact Hmp
  · iintro ⟨HP, Hr⟩
    iunfold swift.goPreP at HP
    icases HP with ⟨#Hc, #Hds, #Ho, #Hi, %Hmp⟩
    iunfold swift.goPre
    iunfold swift.goPreRaw at Hr
    iframe Hc Hds Ho Hi Hr
    ipureintro; exact Hmp

/-- `hdInv` at the start: `goPre`'s raw part. -/
theorem swift.hdInv_init (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) (d : Loc) (y : swift.CommandId)
    (γi γsg : GName) :
    swift.goPre γ0 γc γm x rp RC g d y γi γsg ⊢
      swift.goPreP γ0 γc γm x rp g ∗ swift.hdInv γ0 γc γm x rp RC g d y γi γsg := by
  iintro H
  ihave ⟨#HP, HR⟩ := (swift.goPre_split γ0 γc γm x rp RC g d y γi γsg).1 $$ H
  iframe HP
  iunfold swift.hdInv
  ileft; iexact HR

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
