/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SlotSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The history slot's case per owner kind: statements only** (round 41, sv-swb; table rev 10/10a
T16aG/T16aI, T16b, T16c, T17; plan R8.2 (3)/(4) with R8b.2 (3)/(4); notes/prove-swift.md §49).

Round 41 states these specs and checks them against the table's rows before any proof. The check
met two gaps (table §3R10.22), booked and awaiting the main session's decision (converge rule):

* **41-1** (carrier source): T16c's `desc.slowPathH.Free()` / `desc.fastPathH.Free()` call the
  sets' `freeMsg`, so the slot specs must take each set with its closures' specs (`msetF`, an
  `ownD` at handler resource `True`), not `ownAny` as `slotSpecD`/`slotCap`/`slotCapR`
  (AcksSpecs.lean) and plan R8.2 (4) have it. The statements below use `msetF` (the proposed
  repair); `slotSpecD`, `slotCap`, `slotCapR` and `acksHdOk` (`∀ RA` → `True`) are not changed yet.
* **41-2** (name-value agreement): T16c by the inline owner needs `g.sq = sqC` to make `active`,
  `seq` and `msgs` whole for `freeDesc`; no holder carries that fact. `slotSpecS`'s statement does
  not mention it; its proof would take it from `ownCtx` once the repair (table §3R10.22, (a) or (b))
  is decided.

No proof is given here and no sorry is added.

* `swift.msetF`: a message set with its closures' specs at handler resource `True`.
* `swift.tailG`: what a goroutine holds after its slot case (T16c → T17): the fields for
  `descPooled (descDFA x.γsh)` but `stopChan`'s bag, and the stop element's half or the signal
  token (plan R8.2 (3)).
* `swift.Replica.drainStops.specT`: `drainStops` with the stop bag and the half or the token
  (T17, T19d; plan R8.2 (3), R8b.2 (3)).
* `swift.Replica.handleMsg.slotSpecG` / `slotSpecS`: the slot case at the goroutine record
  `x.dcK … (.go j iL γi)` / the inline record `x.dcK … (.seq γi)`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RemoveStep
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FreeDesc

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
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- **A goroutine's tail after its slot case** (T16c → T17; plan R8.2 (3)): every field for
`descPooled (descDFA x.γsh)` but `stopChan`'s bag, which `drainStops` reads with the stop
element's half (`descGo`'s, signalled) or the signal token (unsignalled). -/
def swift.tailG (x : swift.RunX) (g : swift.DescG) (d : Loc) (y : swift.CommandId) : IProp netDistGF :=
  iprop(∃ (m sl fa sc : Loc) (γsc : ChanNames) (γsg : GName),
    swift.dfld d go!"msgs" ↦ m ∗ swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
    swift.msetAny sl ∗ swift.msetAny fa ∗ swift.descDFA x.γsh d ∗ swift.dfld d go!"stopChan" ↦ sc ∗
    swift.stopBag γsc sc (swift.stopMP g.γs γsg (x.str y) d sc) ∗
    (swift.sgTok γsg ∨ ghostMapElem g.γs (x.str y) (DFrac.own (1 : Qp).half) true))

end defs

section ptLemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [swift.Assumptions]

/-- Half a points-to as two quarters (round 44). -/
theorem swift.pt_quarters {V : Type} [TypedPointsto (GF := netDistGF) V] (l : Loc) (v : V) :
    (typedPointsto (V := V) l v (DFrac.own (1 : Qp).half) : IProp netDistGF) ⊣⊢
      (typedPointsto (V := V) l v (DFrac.own (1 : Qp).half.half) ∗
        typedPointsto (V := V) l v (DFrac.own (1 : Qp).half.half)) := by
  have h : (DFrac.own (1 : Qp).half : DFrac) =
      DFrac.own (1 : Qp).half.half • DFrac.own (1 : Qp).half.half := by
    rw [DFrac.op_own, Qp.half_add_half]
  rw [h]
  exact (typedPointsto_dfractional (GF := netDistGF) l v).dfractional _ _

/-- A whole points-to as two halves (round 44; `swift.pt_halves` of HandleProposeProof, which
this module does not import). -/
theorem swift.pt_halvesW {V : Type} [TypedPointsto (GF := netDistGF) V] (l : Loc) (v : V) :
    (typedPointsto (V := V) l v (DFrac.own 1) : IProp netDistGF) ⊣⊢
      (typedPointsto (V := V) l v (DFrac.own (1 : Qp).half) ∗
        typedPointsto (V := V) l v (DFrac.own (1 : Qp).half)) := by
  have h : (DFrac.own 1 : DFrac) = DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half := by
    rw [DFrac.op_own, Qp.half_add_half]
  rw [h]
  exact (typedPointsto_dfractional (GF := netDistGF) l v).dfractional _ _

/-- A registry slot held whole is not the freeze flag's key (round 44; table §3R11 T16b/T19x's
`⌜j ≠ 0⌝`, inside `cntL`). -/
theorem swift.cntLGhost_ne0 (γn : GName) (dm : GoSlice) (γdl : GName) (d c : w64) (T : List Nat)
    (j : Nat) :
    swift.cntLGhost γn dm γdl d c T ∗ ghostMapElem γn j (DFrac.own 1) false ⊢
      swift.cntLGhost γn dm γdl d c T ∗ ghostMapElem γn j (DFrac.own 1) false ∗ ⌜j ≠ 0⌝ := by
  iintro ⟨HG, Hj⟩
  by_cases h : j = 0
  · subst h
    iunfold swift.cntLGhost at HG
    icases HG with ⟨%L, %f, -, H0, -⟩
    icombine Hj H0 gives %Hc
    exfalso
    have := DFrac.valid_own_op Hc.1
    revert this
    have : (1 : Qp).val = 1 := rfl
    simp
  · iframe
    ipureintro; exact h

end ptLemmas

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- **`r.drainStops(desc)`** (T17, T19d; plan R8.2 (3)): every queued request is answered. A
request with `sgTok` in hand is refuted (the request carries the token too); with the element's
half in hand, the two halves make `Done`'s `P`. -/
abbrev swift.Replica.drainStops.specT : Prop :=
  ∀ (rp d sc : Loc) (γsc : ChanNames) (γs γsg : GName) (k : GoString) (qc : Qp),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own qc) ∗
      swift.stopBag γsc sc (swift.stopMP γs γsg k d sc) ∗
      (swift.sgTok γsg ∨ ghostMapElem γs k (DFrac.own (1 : Qp).half) true) }}
    (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"drainStops")) (Val #d))
  {{ RET #(); typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own qc) }}

/-- **The slot case by a goroutine** (T16aG, T16b, T16c; table rev 10/10a, §3R10.22). The pre is
`slotSpecD`'s at the goroutine record `cG` at `b = g.ev.b`, with the message at the incarnation's
bag predicate (`MPi`; its `g.mp` gives `slotMP`'s `exIn` and `slotIn` through `ownCtx`'s `mpOk`), the
sets as `msetF` (41-1) and no `⌜dv.propose ≠ null⌝` (R8b.2 (4)). The post is the tail (R7b): the loan
went back to the sub-pool (T16b, `descInv_returnLoanO`), the registry slot to `cntL`
(`cntLGhost_exit`), the token to the store (`store_put`), `γi` to `incInv` (T16aG). -/
abbrev swift.Replica.handleMsg.slotSpecG (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) : Prop :=
  ∀ (rp : Loc) (g : swift.DescG) (j iL : Nat) (γi γsg : GName) (γd : ChanNames) (d : Loc)
    (y : swift.CommandId) (dv : swift.DescV) (rv : swift.RowV) (s : w64) (q : Qp) (sl fa cf : Loc)
    (cond : GoFunc) (fs : List GoFunc) (v : Bool) (bw : w32) (stp rcp : Loc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      (x.dcK γ0 γc γm rp g (.go j iL γi)).ctx ∗
      swift.MPi g y γi γsg (interface.mkOk go.int #s) ∗ ⌜dv.seq = false⌝ ∗
      swift.descF d γd (swift.MPi g y γi γsg) dv ∗
      swift.rowTokO (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y dv rv ∗
      ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q ∗
      swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
      swift.msetF sl ∗ swift.msetF fa ∗
      swift.descCore (x.dcK γ0 γc γm rp g (.go j iL γi)) d y g.ev.b ∗
      swift.descRest (x.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y d ∗ swift.ocfRes d cf cond fs v ∗
      (x.dcK γ0 γc γm rp g (.go j iL γi)).kf d y ∗
      swift.epochRd x.γe x.γxe rp x.rr q g.ev.b bw stp rcp ∗
      -- round 43 (table §3R11b, D51 (c)): the pin is `shOwnR`'s, at `q`
      swift.shOwnR (x.dcK γ0 γc γm rp g (.go j iL γi)) d g.ev.b q }}
    (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleMsg"))
      (Val #(interface.mkOk go.int #s))) (Val #d)) (Val #y))
  {{ RET #true; swift.tailG x g d y }}

/-- **The slot case by the inline owner** (T16aI, T16c with `freeDesc`; table rev 10/10a,
§3R10.22). `slotSpecD`'s pre at the inline record `cI` (with `exIn`, as `slotCap` passes it), the
sets as `msetF` (41-1); the post `cI.ret` (the `γS` element and the slot's `γn 0 ↦{⅛}`) and the
loan environment. Its proof needs `g.sq = sqC` (41-2), not yet carried by any holder. -/
abbrev swift.Replica.handleMsg.slotSpecS (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) : Prop :=
  ∀ (rp : Loc) (g : swift.DescG) (γi γsg : GName) (γd : ChanNames) (d : Loc) (y : swift.CommandId)
    (dv : swift.DescV) (rv : swift.RowV) (s : w64) (q : Qp) (sl fa cf : Loc) (cond : GoFunc)
    (fs : List GoFunc) (v : Bool),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      (x.dcK γ0 γc γm rp g (.seq γi)).ctx ∗
      swift.MPi g y γi γsg (interface.mkOk go.int #s) ∗ swift.exIn x.γxm g.ev.b y ∗
      ⌜dv.seq = true⌝ ∗ swift.descF d γd (swift.MPi g y γi γsg) dv ∗
      swift.rowTokO (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y dv rv ∗
      ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q ∗
      swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
      swift.msetF sl ∗ swift.msetF fa ∗ swift.ocfRes d cf cond fs v ∗
      swift.descCore (x.dcK γ0 γc γm rp g (.seq γi)) d y g.ev.b ∗
      swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
      (x.dcK γ0 γc γm rp g (.seq γi)).kf d y ∗ (x.dcK γ0 γc γm rp g (.seq γi)).env d q }}
    (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleMsg"))
      (Val #(interface.mkOk go.int #s))) (Val #d)) (Val #y))
  {{ RET #true; (x.dcK γ0 γc γm rp g (.seq γi)).ret d y ∗ (x.dcK γ0 γc γm rp g (.seq γi)).env d q }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos
