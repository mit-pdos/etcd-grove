/-
Lean-first (no Rocq counterpart).

# k8setcd3: what `call` and `errOut` are stated with (stage 6f)

- `errIs err y`: `errOut(err)` is `y`: a `*StorageError` "not found" or "key exists" (its key and
  resource version), a callback's sentinel (`errDeleteRejected`, `errUpdateRejected`:
  `ERejected`), or any other error (`EOther`: not a `*StorageError` and neither sentinel).
- `unkErr_errIs`: an error of the store whose outcome is unknown (`unkErr`) is the last kind. For
  the client's errors that is a marked `sorry` (D30n): the client proof does not yet say its errors
  are not the driver's sentinels nor `*StorageError`s ("From the etcd client proof", item 5 of
  `notes/k8s-etcd3-plan.md`); an `InternalError` and the driver codec's (none) are proved.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.InvSteps

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item)
open go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The `*StorageError` type. -/
abbrev seTy : go.GoType :=
  go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty

/-- **An error `errOut` cannot place** (`EOther`): not a `*StorageError`, and neither of the
callbacks' sentinels (`eD`, `eU`, the variables' values); a `*errorString` (the sentinels' type,
compared by pointer) holds a pointer. -/
def ErrOther (eD eU err : GoInterface) : Prop :=
  err ≠ eD ∧ err ≠ eU ∧ ∃ ii : GoInterfaceOk, err = .ok ii ∧ ii.ty ≠ seTy ∧
    (ii.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty → ∃ l : Loc, ii.v = #l)

/-- **`errOut(err)` is `y`** (see the file header). -/
def errIs (err : GoInterface) (y : Output) : IProp GF :=
  iprop((∃ k rv, storageErrIs err (W64 1) k rv ∗ ⌜y = ⟨W64 1, k, rv, [], [], 0⟩⌝) ∨
    (∃ k rv, storageErrIs err (W64 2) k rv ∗ ⌜y = ⟨W64 2, k, rv, [], [], 0⟩⌝) ∨
    ((globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errDeleteRejected ↦□ err ∨
        globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errUpdateRejected ↦□ err) ∗
      ⌜y = rejectedL⌝) ∨
    (⌜y = errOutL⌝ ∗ ∃ eD eU : GoInterface,
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errDeleteRejected ↦□ eD ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errUpdateRejected ↦□ eU ∗
      ⌜ErrOther eD eU err⌝))

/-- **A client's error is not the driver's** (see the file header): a marked `sorry` (D30n) until
the client proof says what its errors are. -/
theorem clientErr_other (err eD eU : GoInterface) (_h : clientErr err) :
    globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errDeleteRejected ↦□ eD ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errUpdateRejected ↦□ eU ⊢
      (⌜ErrOther eD eU err⌝ : IProp GF) := by
  sorry

/-- **An error of the store whose outcome is unknown is `EOther`** (see the file header). -/
theorem unkErr_errIs (c : StoreCfg GF DObj) (hc : c.S = driverSpec) (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗
      unkErr c err ⊢ errIs err errOutL := by
  iintro ⟨#Hpkg, #Hu⟩
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8setcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, ⟨%lD, #HD, -⟩, ⟨%lU, #HU, -⟩⟩
  iunfold errIs
  iright; iright; iright
  isplitr
  · ipureintro; rfl
  iexists _, _
  iframe HD HU
  iunfold unkErr at Hu
  icases Hu with ⟨%Hne, (⟨%Hc, -⟩ | %Hie)⟩
  · iapply clientErr_other err _ _ Hc
    iframe HD HU
  · ipureintro
    rcases Hie with ⟨ie, rfl⟩ | he
    · have hne : ∀ t : go.GoType,
          k8s_io.apiserver.pkg.storage.InternalError.ty ≠ go.GoType.PointerType t := by
        intro t h
        rw [k8s_io.apiserver.pkg.storage.InternalError.ty] at h
        cases h
      refine ⟨fun h => ?_, fun h => ?_, _, rfl, hne _, fun h => absurd h (hne _)⟩
      · simp only [interface.mkOk, GoInterface.ok.injEq] at h
        exact hne _ (congrArg GoInterfaceOk.ty h)
      · simp only [interface.mkOk, GoInterface.ok.injEq] at h
        exact hne _ (congrArg GoInterfaceOk.ty h)
    · rw [hc] at he
      exact he.elim

end defs

end k8setcd3
end EtcdGrove
end Perennial
