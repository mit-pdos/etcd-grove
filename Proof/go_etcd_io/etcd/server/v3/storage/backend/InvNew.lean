/-
What the backend's constructor (`New`, `newBackend`) takes and gives. Lean-first (no Rocq
counterpart); 2026-10-17, branch `construct`.

- `hooksOk P W Pk h`: the hooks' contract of the configuration's hooks `h`, for every backend
  made with the parameters `P` and the batch lock's resources `W γ`, `Pk γ` (functions of the
  backend's ghost names: the server's hooks' resource names the backend's `hkOwn`), given the
  backend later (`▷ isBackend`, as `isBackend_of_hooks` takes it). A nil `h` meets it
  (`hooksOk_nil`).
- `newPost γ P W Pk b D`: what the constructor gives: the backend (`isBackend`), its stop
  channels (`isStopChans`, for `Close`), the clients' whole open token, the clients' half of the
  readers' view (of bbolt's data `D`, no buffered writes), the post-lock hook's clients' half
  (nil), the write-back tokens (`wbInit`: all the model provides) and a reader's token for each
  of `readTx.mu`'s reader slots.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvStop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-- The write-back tokens a new backend provides: the batch lock's budget bounds the read
buffer's version plus the tokens out below `2 ^ 40` (`bgOk`; the version starts at 0). -/
def wbInit : Nat := 2 ^ 40 - 1

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The hooks' contract of `h` for every backend made with `P`, `W`, `Pk`, given the backend
later (persistent). -/
def hooksOk (P : BParams) (W Pk : BNames → IProp GF) (h : GoInterface) : IProp GF :=
  iprop(□ ∀ (γ : BNames) (b t : Loc), ▷ isBackend γ P (W γ) (Pk γ) b -∗
    bF go!"batchTx" b ↦□ t -∗ hooksSpec γ P (Pk γ) b t h)

instance hooksOk_persistent (P : BParams) (W Pk : BNames → IProp GF) (h : GoInterface) :
    Persistent (hooksOk P W Pk h) := by
  unfold hooksOk; infer_instance

/-- **What the constructor gives** for the backend `b` over bbolt's data `D`, its ghost names
`γ`. -/
def newPost (γ : BNames) (P : BParams) (W Pk : BNames → IProp GF) (b : Loc) (D : Data) :
    IProp GF :=
  iprop(isBackend γ P (W γ) (Pk γ) b ∗ isStopChans γ b ∗ bOpen γ 1 ∗
    bView γ 1 (vData P (D, ⟨∅, W64 0⟩)) ∗ plHook γ func.nil ∗ ownToks γ.wb wbInit ∗
    [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), rdTok γ P b)

end preds

end backend
end EtcdGrove
end Perennial
