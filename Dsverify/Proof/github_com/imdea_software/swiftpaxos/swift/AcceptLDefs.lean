/-
The definitions, specs and lemmas of `AcceptL.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcksSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

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
variable [swift.Assumptions]

/-- N2's facts of the dependencies `D` of `x` (all but `x`) in `b`. -/
def swift.depsOk (c : swift.DC) (b : Nat) (D : List swift.CommandId) (x : swift.CommandId) :
    IProp netDistGF :=
  iprop([∗list] d ∈ D, ⌜d = x⌝ ∨ sp.accepted c.γ c.r b (toCmdId d) ∨
    sp.committed c.γ c.r b (toCmdId d))

instance swift.depsOk_persistent (c : swift.DC) (b : Nat) (D : List swift.CommandId)
    (x : swift.CommandId) : Persistent (swift.depsOk c b D x) := by
  unfold swift.depsOk; infer_instance

/-- `r.depsAccepted(deps, cmdId)` (see the file header). -/
abbrev swift.Replica.depsAccepted.specIc (c : swift.DC) : Prop :=
  ∀ (b : Nat) (dsl : GoSlice) (D : List swift.CommandId) (x : swift.CommandId)
    (q : Qp),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ swift.epochPinQ c.γxp q b ∗ swift.ownRdr c.rp c.γdl ∗ dsl ↦*□ D ∗
      ⌜c.r ≠ sp.leaderOf c.N b⌝ }}
    (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"depsAccepted"))
      (Val #dsl)) (Val #x))
  {{ (ok : Bool), RET #ok; swift.epochPinQ c.γxp q b ∗ swift.ownRdr c.rp c.γdl ∗
      (⌜ok = false⌝ ∨ swift.depsOk c b D x) }}

/-- `swift.Replica.depsAccepted.specI` at every record (round 44, D53 (1): the per-record form `swift.Replica.depsAccepted.specIc`). -/
abbrev swift.Replica.depsAccepted.specI : Prop :=
  ∀ c : swift.DC, swift.Replica.depsAccepted.specIc c

/-- `r.markAccepted(x)` (see the file header). -/
abbrev swift.Replica.markAccepted.specI : Prop :=
  ∀ (c : swift.DC) (b : Nat) (x : swift.CommandId) (inLoop : Bool) (q : Qp),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ swift.epochPinQ c.γxp q b ∗ sp.accepted c.γ c.r b (toCmdId x) }}
    (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"markAccepted"))
      (Val #x)) (Val #inLoop))
  {{ RET #(); swift.epochPinQ c.γxp q b }}

end specs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- The accepted map's epoch is the pin's: `delivInv` links `γa` to the record's epoch, which
the pin fixes. -/
theorem swift.acceptEpoch (γ : sp.Names) (N r : Nat) (γdl γx γxp γxm γa γxe γrm : GName)
    (str : swift.CommandId → GoString) (q : Qp) (b bA : Nat) :
    inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str) ∗ swift.epochPinQ γxp q b ∗
      ghostVar γa (1 : Qp).half bA ⊢
    |={⊤}=> swift.epochPinQ γxp q b ∗ ghostVar γa (1 : Qp).half bA ∗ ⌜bA = b⌝ := by
  iintro ⟨#HdI, Hpin, Ha⟩
  iinv HdI with Hi Hclose
  iunfold swift.delivInv at Hi
  icases Hi with ⟨%M, %bX, %X, %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
  icases HXx with ⟨HXx, HFz⟩
  ihave ⟨Hpin, HXeD, %Hag⟩ := swift.epochPinQ_agree γxp q b bX rm $$ [Hpin HXeD]
  · iframe Hpin HXeD
  iunfold swift.delivX at HXx
  icases HXx with ⟨%bA', Ha', HXok, %HbA, HRm⟩
  ihave %Hag2 := ghostVar_agree γa bA (1 : Qp).half bA' (1 : Qp).half $$ Ha Ha'
  imod Hclose $$ [HV HXi HXeD HMx Ha' HXok HRm HFz] with -
  · inext; iunfold swift.delivInv; iexists M, bX, X, Mx, rm; iframe
    isplitl
    · iunfold swift.delivX; iexists bA'; iframe; ipureintro; exact HbA
    · ipureintro; exact HM
  imodintro
  iframe
  ipureintro
  rw [Hag2, HbA Hag.1, Hag.2]

end lemmas

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

set_option goose.wp.extras true

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
