/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DescKind.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The descriptors' records per owner** (round 34, sv-swb; D35; notes/lifecycle-table.md revision
5/5b §3.0 and revision 6 §3.10 (G-slot); plan R.0.3, R5.2): the concrete `DC.sq/env/ret/kf/slot`
of an epoch `g` for one owner, replacing round 33's `PHASE2(dc)` placeholders.

* `swift.OwnK`: the owner: a descriptor goroutine (its registry index `j ≠ 0`, its loan `iL` of
  the epoch's sub-pool, its incarnation `γi`), or the run loop's inline calls on a sequential
  descriptor (the descriptor's incarnation `γi`).
* `swift.RunX.dcK x γ γc γm rp g k`: `x.dc` (the kind-free record of the messages' predicates,
  DescDS.lean) with the owner's fields:
  - goroutine `go j iL γi`: `env d q` = the loan token `epochLoan g.γq iL q`, the loan's receipt
    `γlj iL ½ (j, ¼)`, `γn j ↦{¼} false`, the epoch's `descInv` and the sequential inbox;
    `ret` = `True`; `kf d y` = `active` ½ (true), `stopChan` ½ with its bag, `γi` ¼ and the entry
    receipt's half `γj γi ½ (j, ¼)` (round 35, table rev 7 §3.11, D36: the entry's `descGo` holds
    the other quarter of `γi` and the other receipt half), the `γsh` half;
    `slot none = γn j ↦{¼} false`, `slot (some K) = outRcpt K (j, ¼)`;
  - inline `seq γi`: `env d q` = some inline loan `iL`'s token and receipt `γlj iL ½ (0, ¼)` (round
    35, table rev 7b §3.12 G-hrec: `iL` existential, one record for all inline calls), the
    invariants; `ret d y` = the `γS` element (C4); `kf d y` = `active` ½ (true), `stopChan` whole,
    `γi` ½, the `γsh` half; `slot` with `j = 0` at ⅛.
* `swift.takeLaw_dcK`: the record's `takeLaw` (from `store_take`, Store.lean), what the install
  steps (`install_tok`, `install_sync`) use.
* `swift.descMP_dcK`, `swift.ctx_dcK`: the owner records give the messages' predicates and the
  context of `x.dc`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Store
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescDS
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The owner of a descriptor's record (see the file header). -/
inductive swift.OwnK where
  | go (j iL : Nat) (γi : GName)
  | seq (γi : GName)

/-- The owner's registry index and the slot's fraction (goroutine `j`, ¼; inline `0`, ⅛). -/
def swift.OwnK.jq : swift.OwnK → Nat × Qp
  | .go j _ _ => (j, (1 : Qp).half.half)
  | .seq _ => (0, (1 : Qp).half.half.half)


def swift.OwnK.γi : swift.OwnK → GName
  | .go _ _ γi => γi
  | .seq γi => γi

def swift.OwnK.isSeq : swift.OwnK → Bool
  | .go _ _ _ => false
  | .seq _ => true

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- `soOk`'s clause 6 at the replica's share map (round 40, table rev 10a §3R10.21 C4/40-2): a raw
inbox form and an owner's half of the share map's element exclude each other. Reads `g.sr`, never
`g.so` (G-circ), so an owner's context can hold it; `sqE_toSI` uses it. -/
def swift.shSr (x : swift.RunX) (g : swift.DescG) : Prop :=
  ∀ (d : Loc) (y : swift.CommandId) (q : Qp),
    g.sr d y ∗ ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q ⊢ (False : IProp netDistGF)

/-- A raw inbox form has a share of `active` (round 40, table rev 10a §3R10.21 gap 40-3; `soOk`'s
clauses 5 then 4): what a goroutine's or the inline owner's sequential creation (T3'c,
`seqInbox_add`) needs to refute a reused key's raw form. Reads `g.sr` only (G-circ). -/
def swift.srA (g : swift.DescG) : Prop :=
  ∀ (d : Loc) (y : swift.CommandId), g.sr d y ⊢
    ∃ (a : Bool) (qa : Qp), typedPointsto (swift.dfld d go!"active") a (DFrac.own qa) ∗ True

/-- **An owner's persistent context** (round 37; table rev 8 §3.14 G-ctx, rev 8b K2; plan R8.1):
what the cases and a creator need beyond `c.ctx`: the descriptors' context (`cntL`, the pool, the
share map, `MaxDescRoutines`, `SQ`), the proposal's base context (`proposeCtxB`, with `ackCtx`),
the history and its lock, and the epoch's pure facts: its message predicates (`mpOk`), what
`stopDescs` needs of a sequential state (`sqOk`) and the creation of a sequential descriptor
(`srOk`: reads `g.sr`, never `g.so`, so the parked forms' records are `rfl`-equal, G-circ). -/
def swift.ownCtx (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g : swift.DescG) :
    IProp netDistGF :=
  iprop(swift.descDSCtx rp x ∗ swift.proposeCtxB (x.dc γ γc γm rp) ∗
    (∃ hsl : GoSlice, swift.fld rp go!"history" ↦□ hsl ∗
      sync.isMutex (swift.fld rp go!"historyL") (swift.historyLInv hsl)) ∗
    -- round 46 (D60, O1-b): the epoch's reply channel object, for a created goroutine's `goPre`
    swift.RCh γ γc γm rp g.ev.rcp g.ev.bw ∗
    ⌜swift.mpOk x γ γc γm rp g ∧ swift.sqOk γ (x.DR γ g.ev.b) (swift.sqE g) g.mp ∧
      swift.srOk (x.dc γ γc γm rp) (swift.RCh γ γc γm rp) g ∧ swift.shSr x g ∧ swift.srA g⌝ ∗
    -- round 56 (D79 (1), 52-3): the epoch's registration (the rest records' `cgW`)
    swift.cgG x g)

instance swift.ownCtx_persistent (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (g : swift.DescG) : Persistent (swift.ownCtx γ γc γm x rp g) := by
  unfold swift.ownCtx; infer_instance

/-- The epoch's invariants an owner holds (`descInv` at the run loop's `DR`/`Run`, the inbox) and
(round 37, G-ctx) its persistent context. -/
def swift.epInvs (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g : swift.DescG) :
    IProp netDistGF :=
  iprop(inv swift.descN (swift.descInv γ x.γd x.γn x.γout g (x.epN rp) (x.DR γ g.ev.b)
      (swift.descGo x.γn g x.str) x.str) ∗
    inv swift.seqN (swift.seqInbox g) ∗ swift.ownCtx γ γc γm x rp g)

instance swift.epInvs_persistent (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (g : swift.DescG) : Persistent (swift.epInvs γ γc γm x rp g) := by
  unfold swift.epInvs; infer_instance

/-- **The owner's loan environment** (table rev 5/6 §3.0, D35; round 35, table rev 7b §3.12
G-hrec: the inline kind's loan index is existential, so one record serves all its inline calls).
Round 38 (table rev 9 R9-1, D-R9-1): with the loan's fraction of `cmdDescs` (`descX … q`), for the
owner's non-atomic `r.cmdDescs` loads (swift.go:861 in `depSpecR`, :1054 at T16a). -/
def swift.envK (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g : swift.DescG) (k : swift.OwnK)
    (_d : Loc) (q : Qp) : IProp netDistGF :=
  match k with
  | .go j iL _ => iprop(swift.epochLoan g.γq iL q ∗
      ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ∗
      ghostMapElem x.γn j (DFrac.own (1 : Qp).half.half) false ∗
      (∃ dm : GoSlice, swift.descX rp x.γd g dm q) ∗ swift.epInvs γ γc γm x rp g)
  | .seq _ => iprop((∃ iL : Nat, swift.epochLoan g.γq iL q ∗
      ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) ((0 : Nat), (1 : Qp).half.half)) ∗
      (∃ dm : GoSlice, swift.descX rp x.γd g dm q) ∗ swift.epInvs γ γc γm x rp g)

/-- **The owner kind's frame** (table rev 5 §3.0's `c.kf`; C6). Round 40 (table rev 10a §3R10.21,
40-1): a goroutine's frame holds its incarnation's commit witness at its stop bag's name `γsg`, so a
request it receives is at the name its entry's `descGo` holds (`incW_agree`). -/
def swift.kfK (x : swift.RunX) (g : swift.DescG) (k : swift.OwnK) (d : Loc) (y : swift.CommandId) :
    IProp netDistGF :=
  iprop(typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗
    (∃ q : Qp, ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q) ∗
    if k.isSeq then iprop(ghostVar k.γi (1 : Qp).half (x.str y, d) ∗
      ∃ sc : Loc, swift.dfld d go!"stopChan" ↦ sc) else
      iprop(ghostVar k.γi (1 : Qp).half.half (x.str y, d) ∗
        ghostMapElem g.γj k.γi (DFrac.own (1 : Qp).half) k.jq ∗
        ∃ (sc : Loc) (γsc : ChanNames) (γsg : GName),
        typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half) ∗
        swift.stopBag γsc sc (swift.stopMP g.γs γsg (x.str y) d sc) ∗
        □ swift.incW g k.γi γsg))

/-- **The inline kind's frame without its incarnation half** (round 37; table rev 8 G-pslot, plan
R8.1): what a sequential descriptor parked with its token in the store keeps of `kfK` (the rest
record holds the `γi` half). -/
def swift.kfK0 (x : swift.RunX) (d : Loc) : IProp netDistGF :=
  iprop(typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗
    (∃ q : Qp, ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q) ∗
    ∃ sc : Loc, swift.dfld d go!"stopChan" ↦ sc)

/-- **The ledger's slot** (table rev 6, G-slot). -/
def swift.slotK (x : swift.RunX) (k : swift.OwnK) : Option (Nat × sp.CmdId) → IProp netDistGF
  | none => ghostMapElem x.γn k.jq.1 (DFrac.own k.jq.2) false
  | some K => swift.outRcpt x.γout K k.jq

/-- **The record of an owner** (see the file header). -/
def swift.RunX.dcK (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) (g : swift.DescG)
    (k : swift.OwnK) : swift.DC :=
  { x.dc γ γc γm rp with
    sq := k.isSeq
    env := swift.envK γ γc γm x rp g k
    -- round 37 (table rev 8 G-ret): a sequential retirement gives the run loop's slot share back
    ret := fun d y => if k.isSeq then iprop(ghostMapElem g.γS d (DFrac.own 1) y ∗ swift.slotK x k none)
      else iprop(True)
    kf := swift.kfK x g k
    slot := swift.slotK x k }

end defs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- The owner records give `x.dc`'s message predicates (`descMP` reads no owner field). -/
theorem swift.descMP_dcK (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc)
    (g : swift.DescG) (k : swift.OwnK) (b : Nat) (y : swift.CommandId)
    (SL SE : GoInterface → IProp netDistGF) :
    swift.descMP (x.dcK γ γc γm rp g k) b y SL SE = swift.descMP (x.dc γ γc γm rp) b y SL SE := rfl

/-- The owner records have `x.dc`'s context. -/
theorem swift.ctx_dcK (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc)
    (g : swift.DescG) (k : swift.OwnK) :
    (x.dcK γ γc γm rp g k).ctx = (x.dc γ γc γm rp).ctx := rfl

/-- **The take law of an owner record** (table rev 6 G-slot; T11 :512, T24). -/
theorem swift.takeLaw_dcK (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc)
    (g : swift.DescG) (k : swift.OwnK) :
    (x.dcK γ γc γm rp g k).ctx ⊢ swift.takeLaw (x.dcK γ γc γm rp g k) := by
  iintro #Hctx
  iunfold swift.takeLaw
  imodintro
  iintro %d %q %K %ck Henv Hsl Hcl
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, %Hids, -, -,
    -, -, -, #Hninv, -⟩
  cases k with
  | go j iL γi =>
    simp only [swift.RunX.dcK, swift.envK, swift.slotK, swift.epInvs, swift.slotT]
    icases Henv with ⟨Hloan, Hlr, Hj, HX, #HD, #HSI, #HO⟩
    imod (swift.store_take γ x.γv x.γe x.γo ⟨x.γxm, x.γout, x.γcl, x.str, x.N, x.r, x.γxu, x.γrp, x.γcg⟩ x.k x.γd x.γn g
        (x.epN rp) (x.DR γ g.ev.b) (swift.descGo x.γn g x.str) x.str iL q K ck
        (swift.OwnK.go j iL γi).jq.1 (swift.OwnK.go j iL γi).jq.2) $$ [Hloan Hsl Hcl]
      with ⟨%rv, Htok, Hw, Htx, Hloan, Hrc⟩
    · iframe Hninv HD Hloan Hsl Hcl
    imodintro
    iexists rv
    iframe Htok Hw Hrc Htx
    iframe Hloan Hlr Hj HX HD HSI HO
  | seq γi =>
    simp only [swift.RunX.dcK, swift.envK, swift.slotK, swift.epInvs, swift.slotT]
    icases Henv with ⟨⟨%iL, Hloan, Hlr⟩, HX, #HD, #HSI, #HO⟩
    imod (swift.store_take γ x.γv x.γe x.γo ⟨x.γxm, x.γout, x.γcl, x.str, x.N, x.r, x.γxu, x.γrp, x.γcg⟩ x.k x.γd x.γn g
        (x.epN rp) (x.DR γ g.ev.b) (swift.descGo x.γn g x.str) x.str iL q K ck
        (swift.OwnK.seq γi).jq.1 (swift.OwnK.seq γi).jq.2) $$ [Hloan Hsl Hcl]
      with ⟨%rv, Htok, Hw, Htx, Hloan, Hrc⟩
    · iframe Hninv HD Hloan Hsl Hcl
    imodintro
    iexists rv
    iframe Htok Hw Hrc Htx
    iframe HX HD HSI HO
    iexists iL
    iframe Hloan Hlr

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
