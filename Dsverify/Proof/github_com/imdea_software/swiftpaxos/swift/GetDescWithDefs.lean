/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/GetDescWithDefs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**GetDescWithDefs** (round 43, D52 (4): GetDescWith.lean split by phase): the definitions
(`descDSN`, `descDSNo`, `descStateB`, `descDSB`, `goPre`) and the specs (`seqSpecD`, `coreSpecD`,
`handleDesc.specD`). The lemmas are in GetDescWithLoan/GetDescWithEnts; `wp_coreD` in GetDescWith.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescFresh
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleProposal
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.StopRound
public import Dsverify.Proof.github_com.orcaman.concurrent_map.UpsertL

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

/-- **`propSpecIN`'s `DS` at the descriptors' state** (round 24): `descDS` of the run loop's
names `γ0 γc γm x`, the proposal's protocol names, `delivered`'s view (the reader's), replica
count and id the replica's, and the
descriptors' context (persistent; `runInv` has it). Round 37b (table rev 8c §3.17, GAP-37b/37d):
with `proposeCtxB` and the history pair, which a spawned goroutine's `ownCtx` needs (T4); the
arms take them from `runLoopCtx` (`swift.runLoopCtx_ownB`). -/
def swift.descDSN (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (γ : sp.Names) (γdl : GName)
    (N r : Nat) (rp : Loc) : IProp netDistGF :=
  iprop(swift.descDS γ0 γc γm x rp ∗ ⌜γ = γ0 ∧ γdl = x.γdl ∧ N = x.N ∧ r = x.r⌝ ∗
    (x.dc γ0 γc γm rp).ctx ∗ swift.proposeCtxB (x.dc γ0 γc γm rp) ∗
    (∃ hsl : GoSlice, swift.fld rp go!"history" ↦□ hsl ∗
      sync.isMutex (swift.fld rp go!"historyL") (swift.historyLInv hsl)))

/-- **`propSpecIN`'s `DS`** (round 28, G7): `descDSN` and the row tokens' name the run loop's
(the proposal's fresh token is at it). -/
def swift.descDSNo (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (γ : sp.Names) (γcl γdl : GName)
    (N r : Nat) (rp : Loc) : IProp netDistGF :=
  iprop(swift.descDSN γ0 γc γm x γ γdl N r rp ∗ ⌜γcl = x.γcl⌝)

/-- `descStateR` without the run loop's sequential store (round 26, G9): what the inline
`handleMsg` of a sequential descriptor is lent (`swift.descDSB`). -/
def swift.descStateB (γ : sp.Names) (rp : Loc) (x : swift.RunX) (DR : Loc → IProp netDistGF)
    (Run : Loc → swift.CommandId → IProp netDistGF) (g : swift.DescG) : IProp netDistGF :=
  iprop(∃ dm1 : GoSlice,
    typedPointsto (swift.fld rp go!"cmdDescs") dm1 (DFrac.own (1 : Qp).half) ∗
    github_com.orcaman.concurrent_map.isCMapV dm1 g.γdc (swift.descR x.γd) ∗
    github_com.orcaman.concurrent_map.readerV dm1 g.γdc (swift.descR x.γd) ∗
    inv swift.descN (swift.descInv γ x.γd x.γn x.γout g (x.epN rp) DR Run x.str) ∗
    ghostVar g.γst (1 : Qp).half false ∗ swift.cntFrozen x.γn false ∗
    ghostMapAuth g.γs 1 (∅ : GMap GoString Bool) ∗ ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗
    inv swift.seqN (swift.seqInbox g))

/-- **`descDS` at its epoch `g ev γp i` without the sequential store** (round 26, G9): the run
loop's descriptor state while one sequential descriptor's state (`g.so d y`) is out of the
store for an inline `handleMsg`. -/
def swift.descDSB (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g : swift.DescG)
    (ev : swift.EpV) (γp : GName) (i : Nat) : IProp netDistGF :=
  iprop(swift.epRunL γ γc γm rp x ev γp i g.Qd ∗
    swift.descStateB γ rp x (x.DR γ g.ev.b) (swift.descGo x.γn g x.str) g ∗
    swift.epochLoan γp i g.Qd ∗ ⌜g.ev = ev⌝ ∗ swift.descDSCtx rp x ∗
    ⌜swift.sqOk γ (x.DR γ g.ev.b) (swift.sqE g) g.mp⌝ ∗ ⌜swift.mpOk x γ γc γm rp g⌝ ∗
    ⌜swift.soOk γ (x.DR γ g.ev.b) (x.dc γ γc γm rp) (swift.RCh γ γc γm rp) g⌝ ∗
    -- round 42 (table §3R11 gap 11-1, D49 (1)): the epoch's construction, for `seqSpecD`'s T7s.o/T7e
    ⌜∃ g00 : swift.DescG, g = swift.gO γ γc γm x rp g00⌝ ∗
    -- round 56 (D79 (1), 52-3): the epoch's registration
    swift.cgG x g)

/-- **A spawned descriptor goroutine's precondition** (round 27, D23 G8; `go r.handleDesc(desc,
cmdId)` in `getCmdDescWith`'s Upsert callback, before the entry is committed): the replica's and
the descriptors' contexts, the descriptors' invariant, and the raw descriptor `newDesc` made: its
halves of `msgs`/`active`/`stopChan` and a quarter of `seq` (`false`; the entry's `descGo` holds the
rest), the two channels' bags with the incarnation `γi`'s commit witness (`swift.incW`: every
message, a stop request included, carries it, so the goroutine learns its entry is committed), the
share map's element at the loan's `q`, `descRaw` (the rest, at the epoch's `FQ`), the loan from the
descriptors' sub-pool (`epochShare q`, token `iL`), the `cntL` slot `j` (half of its registry
element: the entry's `descGo` and the loan's record have a quarter each; the reader bundle), and
a quarter of `γi` (the incarnation's owner's half, less the quarter the entry's `descGo` holds;
`descInv`'s `incInv` gets the other half at the commit) and the goroutine's half of its entry's
receipt `γj γi` (round 35, table rev 7 §3.11, D36). Round 38 (table rev 9 R9-1): with the loan's
fraction of `cmdDescs` (`descX … q`, for `envK`). Round 45 (D54, D55 (1)): with the epoch's
reply channel object `□ RC g.ev.rcp g.ev.bw` (`RC := swift.RCh …` at the link). -/
def swift.goPre (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) (d : Loc) (y : swift.CommandId)
    (γi γsg : GName) : IProp netDistGF :=
  iprop((x.dc γ0 γc γm rp).ctx ∗ swift.descDSCtx rp x ∗ swift.ownCtx γ0 γc γm x rp g ∗
    inv swift.descN (swift.descInv γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b)
      (swift.descGo x.γn g x.str) x.str) ∗
    ⌜swift.mpOk x γ0 γc γm rp g⌝ ∗
    ∃ (m sc : Loc) (γmc γsc : ChanNames) (sqv : GoInterface) (szS : Nat) (memS : w32 → Prop)
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

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- **The run loop's inline `r.handleMsg(m, desc, cmdId)` on a sequential descriptor**
(round 26, D23 G9; swift.go:886; a hypothesis of `getCmdDescWith.wp_proofDS`, to be proved from
`handleMsg`'s cases, notes/prove-swift.md §32): from the descriptor's state between two inline
calls (`g.so d y`, out of the run loop's `seqStore`) and a message of the epoch's predicate, with
the run loop's descriptor state lent (`descDSB`), its reader and `ballot` share: the state again,
or retired (the slot case removed the entry: its state `sqC d y` and its element, which round 29
fixes at the run loop's store `γS` (the entry's element was moved there by `seqTake`; an inbox
element is refuted by `soOk`'s clause 1 with the owner state the call holds; `swift.sqE_toS`), the
run loop's store takes it back). Round 38 (table rev 9 R9-3, D41): with the owner's context
`ownCtx` (□), which the inline owner's `envK` needs (`proposeCtxB`, the history). -/
abbrev swift.Replica.handleMsg.seqSpecD (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) : Prop :=
  ∀ (rp : Loc) (g : swift.DescG) (ev : swift.EpV) (γp : GName) (i : Nat) (d : Loc)
    (y : swift.CommandId) (m : GoInterface) (bw : w32) (qb : Qp),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      (x.dc γ0 γc γm rp).ctx ∗ swift.ownCtx γ0 γc γm x rp g ∗
      swift.descDSB γ0 γc γm x rp g ev γp i ∗ swift.runReader rp x.γdl ∗
      typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own qb) ∗ g.so d y ∗ g.mp y m ∗
      -- round 44 (gap 44-2): the ghost steps around the call (T7s.l, T7e/T7r) open `descN`
      £ 1 ∗ £ 1 ∗ £ 1 ∗ £ 1 }}
    (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleMsg"))
      (Val #m)) (Val #d)) (Val #y))
  {{ (v : Bool), RET #v; swift.descDSB γ0 γc γm x rp g ev γp i ∗ swift.runReader rp x.γdl ∗
      typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own qb) ∗
      (g.so d y ∨ ghostMapElem g.γS d (DFrac.own 1) y) }}

/-- **`r.getCmdDescWith(x, m, seq)` for any message** (round 27; the descriptor arms' and
`handleProposal`'s): `m` (not nil) is of `x`'s descriptor's predicate in the epoch whose ballot is
the run loop's (`Pm`, turned into `g.mp x m` once the epoch `g` is known). -/
abbrev swift.Replica.getCmdDescWith.coreSpecD (DS : sp.Names → GName → Nat → Nat → Loc → IProp netDistGF)
    (x : swift.RunX) (γ0 : sp.Names) (γc γm : GName) : Prop :=
  ∀ (γ : sp.Names) (γdl : GName) (rp : Loc) (xid : swift.CommandId) (m : GoInterface) (sqb : Bool)
    (N r b : Nat) (Pm : IProp netDistGF) (bw : w32) (qb : Qp),
  m ≠ interface.nil →
  (∀ g : swift.DescG, swift.mpOk x γ0 γc γm rp g → g.ev.b = b → Pm ⊢ g.mp xid m) →
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      DS γ γdl N r rp ∗ swift.runReader rp γdl ∗ Pm ∗
      typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own qb) ∗ ⌜sp.bal bw = b⌝ }}
    (App (App (App
      (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDescWith")) (Val #xid))
      (Val #m)) (Val #sqb))
  {{ (d : Loc), RET #d; DS γ γdl N r rp ∗ swift.runReader rp γdl ∗
      typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own qb) }}

/-- **`go r.handleDesc(desc, cmdId)`** (round 27; a hypothesis of `getCmdDescWith.wp_proofDS`, to be
proved from `handleMsg`'s cases, notes/prove-swift.md §33): from the raw spawn state `goPre`. Round 45:
`RC` is the replica-indexed family of reply channel objects (`swift.RCh γ γc γm` at the link), used
at `RC rp`. -/
abbrev swift.Replica.handleDesc.specD (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (RC : Loc → Loc → w32 → IProp netDistGF) : Prop :=
  ∀ (rp : Loc) (g : swift.DescG) (d : Loc) (y : swift.CommandId) (γi γsg : GName),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.goPre γ0 γc γm x rp (RC rp) g d y γi γsg }}
    (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleDesc")) (Val #d))
      (Val #y))
  {{ RET #(); True }}

end specs


end Perennial.github_com.imdea_software.swiftpaxos
