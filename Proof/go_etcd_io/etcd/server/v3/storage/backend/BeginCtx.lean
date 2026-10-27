/-
What `backend.begin` and `backend.unsafeBegin` read of the backend (`beginCtx`): its logger
(not nil) and its metrics' invariant. Their specs took the whole `isBackend` until the
constructor's proof (2026-10-17, branch `construct`): `newBatchTxBuffered`'s first commit begins
bbolt's transactions before the backend's invariants exist, so the specs take only this.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- What `begin`/`unsafeBegin` read of the backend `b`: its logger (not nil: `unsafeBegin`'s
`Fatal`) and its metrics (`begin` stores the sizes) (persistent). -/
def beginCtx (b : Loc) : IProp GF :=
  iprop(∃ lg : Loc, bF go!"lg" b ↦□ lg ∗ ⌜lg ≠ Loc.null⌝ ∗ metricsInv b)

instance beginCtx_persistent (b : Loc) : Persistent (beginCtx (GF := GF) b) := by
  unfold beginCtx; infer_instance

/-- A backend has its `begin` context. -/
theorem isBackend_beginCtx (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) :
    isBackend γ P W Pk b ⊢ beginCtx b := by
  iintro #Hb
  icases isBackend_b γ P W Pk b $$ Hb with ⟨%t, %rt, %db, %lg, #-, #-, #Hlg, %Hlgn, #Hmi, #-⟩
  unfold beginCtx
  iexists lg
  iframe #
  ipureintro; exact Hlgn

end preds

end backend
end EtcdGrove
end Perennial
