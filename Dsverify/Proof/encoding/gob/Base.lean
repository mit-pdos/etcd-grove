/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/gob/Base.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The package-level state of the lab's `encoding/gob` model (`SwiftNetPkgState.gob`, this run's
choice, `Proof/swiftnet/PkgState.lean`): `errTooBig` holds its `errors.New` error, and `codecMu`
is a mutex whose invariant keeps `codec` nil or a codec with the kit's functions for good
(`codecSet`), as `net/rpc`'s `codecInv` does.
-/
module

public import Dsverify.Spec.encoding.gob.Defs
public import Dsverify.GeneratedProof.encoding.gob
public import Perennial.Proof.sync.Mutex__Lock
public import Perennial.Proof.sync.Mutex__Unlock
public import Perennial.Proof.errors.NewVar

@[expose] public section

noncomputable section

namespace Perennial.encoding.gob

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section base
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [net.rpc.RpcKit]

/-- The invariant of `codecMu`: `codec` is nil, or a codec with the kit's functions, for good. -/
def codecInv : IProp GF :=
  iprop(globalAddr encoding.gob.codec ↦ (null : Loc) ∨ codecSet)

/-- The model's package-level state (`SwiftNetPkgState.gob`). -/
def isInit : IProp GF :=
  iprop("#HerrTooBig" ∷ errors.newVar encoding.gob.errTooBig go!"gob: decoder: message too big" ∗
    "#HcodecMu" ∷ sync.isMutex (globalAddr encoding.gob.codecMu) codecInv)

instance isInit_persistent : Persistent (isInit (GF := GF)) := by
  unfold isInit; infer_instance

end base

end Perennial.encoding.gob

namespace Perennial.encoding.gob

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section access
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [pkgState : github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]
variable [net.rpc.RpcKit]

/-- The model's package-level state, when the run's choice is `isInit`. -/
theorem isInit_access (hst : pkgState.gob = isInit) :
    isPkgInit (PROP := IProp GF) pkg_id.encoding.gob ⊢ isInit (GF := GF) := by
  rw [← hst]
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.encoding.gob

/-- The packages `encoding/gob` imports are initialized. -/
theorem deps_of_pkg :
    isPkgInit (PROP := IProp GF) pkg_id.encoding.gob ⊢
      isPkgInit (PROP := IProp GF) pkg_id.errors ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
      isPkgInit (PROP := IProp GF) pkg_id.sync := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.encoding.gob).trans ?_
  show iprop(isPkgInit (PROP := IProp GF) pkg_id.errors ∗
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ True) ⊢ _
  iintro ⟨H1, H2, H3, -⟩
  iframe

end access

end Perennial.encoding.gob
