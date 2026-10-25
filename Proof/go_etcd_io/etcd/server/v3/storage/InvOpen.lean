/-
**Opening the backend's database file** (`server/storage/backend.go`: `OpenBackend`,
`OpenSnapshotBackend`; D22 S-f, 2026-10-19; `notes/decisions.md`, "D22 S-f carried out"): what
their specs share. Lean-first (no Rocq counterpart).

* `dbOpensOk` (opaque `Prop`, a named premise about the program's environment, D19a's first
  kind, as `apply.backendUnderQuota`): bbolt's `Open` succeeds on the database files the server
  opens after its start (the file system, the disk and the file lock cooperate: no other process
  holds the file's lock, no I/O error). `OpenBackend` runs `newBackend` on a goroutine, whose
  panic on a failed `Open` (`lg.Panic`) kills the process; a goroutine's panic is a verification
  failure (`wp_fork`'s `forkPost`), so `OpenBackend`'s axiom holds only where it does not happen.
  True of the runs covered (one process per data directory, a local disk); nothing in the model
  proves or refutes it.
* `openLimit cfg`: the batch limit `newBackend` configures (`cfg.BackendBatchLimit`, or the
  backend's default `10000` if it is 0).
* `openPre cfg h P D W Pk`: what opening a file holding bbolt's data `D` needs besides the file:
  `dbOpensOk`, the configuration's logger (its `Info` at the end), its feature gate (nil, or one
  that answers `NonBlockingDefrag`), the parameters `P` (`P.Wf`, the batch limit `openLimit`),
  and, as `backend.New`'s spec, the hooks' contract of `h` and the creator's batch-lock resources
  `W γ ∗ Pk γ` from the hook's own keys of `D` and (D22 receiver epochs, S8a, 2026-10-24) the fresh
  backend's payment rights (`bFresh`), traded for `K γ` (`newPostK`; `openPre_keep`: kept).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvNew
public import Proof.go_etcd_io.etcd.server.v3.features.Defs
public import Proof.go_etcd_io.etcd.server.v3.config.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace storage

open Iris Iris.BI backend

/-- **bbolt opens the server's database files** (opaque; see the file header). -/
opaque dbOpensOk : Prop

/-- The batch limit `newBackend(cfg, hooks)` configures (`DefaultBackendConfig`'s
`defaultBatchLimit`, unless the configuration sets one). -/
def openLimit [FfiSyntax] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : w64 :=
  if cfg.BackendBatchLimit' = W64 0 then W64 10000 else cfg.BackendBatchLimit'

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **What opening a database file holding `D` needs besides the file** (see the file header). -/
def openPre (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (h : GoInterface) (P : BParams)
    (D : Data) (W Pk K : BNames → IProp GF) : IProp GF :=
  iprop(⌜dbOpensOk ∧ cfg.Logger' ≠ Loc.null ∧ P.Wf ∧ P.limit = openLimit cfg⌝ ∗
    (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
    hooksOk P W Pk h ∗ (∀ γ : BNames, hkOwn γ (hkData P D) ∗ bFresh γ ={⊤}=∗ W γ ∗ Pk γ ∗ K γ))

/-- A creator that keeps the fresh backend's payment rights (`K := bFresh`, `newPost_of_K`). -/
theorem openPre_keep (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (h : GoInterface)
    (P : BParams) (D : Data) (W Pk : BNames → IProp GF) :
    iprop(⌜dbOpensOk ∧ cfg.Logger' ≠ Loc.null ∧ P.Wf ∧ P.limit = openLimit cfg⌝ ∗
      (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
      hooksOk P W Pk h ∗ (∀ γ : BNames, hkOwn γ (hkData P D) ={⊤}=∗ W γ ∗ Pk γ)) ⊢
      openPre (GF := GF) cfg h P D W Pk bFresh := by
  iintro ⟨%Hc, Hg, #Hh, Hmk⟩
  iunfold openPre
  iframe Hg Hh
  isplitr
  · ipureintro; exact Hc
  iintro %γ ⟨Hk, Hf⟩
  imod Hmk $$ %γ Hk with ⟨HW, HPk⟩
  imodintro
  iframe HW HPk Hf

end preds

end storage
end EtcdGrove
end Perennial
