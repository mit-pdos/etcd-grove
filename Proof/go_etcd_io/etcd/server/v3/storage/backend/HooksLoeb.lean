/-
The backend's contract with its hooks' contract derived (2026-10-13, unit 8). Lean-first (no
Rocq counterpart); see `notes/decisions.md`, "The server's backend hook (unit 8)".

`isBackend γ P W Pk b` holds the hooks' contract (`hooksSpec`) of the backend's `hooks` field,
and a hook's own proof needs the backend's contract (its puts are the batch transaction's,
whose specs take `isBackend`): a cycle. `isBackendNH γ P W Pk b h` is `isBackend` without the
hooks' contract, the `hooks` field `h`; `isBackend_of_hooks` closes the cycle by Löb induction,
for a hook whose contract needs the backend only later (`▷ isBackend`: after the call's first
step, as `BackendHooks.OnPreCommitUnsafe`'s spec states it).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`isBackend` without the hooks' contract**: every fact of `isBackend γ P W Pk b`, the
`hooks` field holding `h`, but `hooksSpec` (persistent). What the backend's creator makes before
the hooks' contract is known. -/
def isBackendNH (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (h : GoInterface) :
    IProp GF :=
  iprop(□ ∃ (t rt tm db lg : Loc),
    bF go!"batchTx" b ↦□ t ∗ bF go!"readTx" b ↦□ rt ∗ bF go!"batchLimit" b ↦□ P.limit ∗
    bF go!"lg" b ↦□ lg ∗ ⌜lg ≠ Loc.null⌝ ∗ bF go!"hooks" b ↦□ h ∗ beOf t ↦□ b ∗
    rtmuOf (baseOf rt) ↦□ tm ∗
    sync.isMutex (muOf t) (batchFree γ P W Pk b t) ∗
    sync.isRWMutexGuard (rmuOf (baseOf rt)) (rtRes γ P rt) ∗
    sync.isRWMutexGuard tm (fun q => tmTok γ q) ∗
    sync.isMutex (cmuOf b) (cacheRes γ P b) ∗ cacheInv γ ∗ metricsInv b ∗
    sync.isRWMutexGuard (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
    isDB db ∗ ⌜P.Wf⌝)

instance isBackendNH_persistent (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc)
    (h : GoInterface) : Persistent (isBackendNH γ P W Pk b h) := by
  unfold isBackendNH; infer_instance

/-- **The backend with its hooks' contract derived**: from `isBackendNH` and the hooks'
contract of `h` given the backend later (`▷ isBackend`), by Löb induction. -/
theorem isBackend_of_hooks (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc)
    (h : GoInterface) :
    isBackendNH γ P W Pk b h ∗
      □ (▷ isBackend γ P W Pk b -∗ ∀ t : Loc, bF go!"batchTx" b ↦□ t -∗ hooksSpec γ P Pk b t h) ⊢
      isBackend γ P W Pk b := by
  iintro ⟨#Hnh, #Hhs⟩
  iloeb as IH
  iunfold isBackendNH at Hnh
  icases Hnh with ⟨%t, %rt, %tm, %db, %lg, #Ht, #Hrt, #Hl, #Hlg, %Hlgn, #Hh, #Hbe, #Htm, #Hm,
    #Hrm, #Htmg, #Hcm, #Hci, #Hmi, #Hmu, #Hdb, %HP⟩
  ihave #Hs := Hhs $$ IH %t Ht
  iunfold isBackend
  iintro !>
  iexists t, rt, tm, db, lg, h
  iframe #
  ipureintro
  exact ⟨Hlgn, HP⟩

end defs

end backend
end EtcdGrove
end Perennial
