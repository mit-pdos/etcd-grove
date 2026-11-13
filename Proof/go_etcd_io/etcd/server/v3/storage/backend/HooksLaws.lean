/-
**The constructor's hooks premise, for clients** (mvccfull's F1 repair round 2, 2026-11-10): what a
client of `backend.New` with no hooks used to get by unfolding `hooksOk` and `hooksSpec`
(`examples/mvccfull`'s `runner.openBackend`). In a module of its own, so that adding it leaves the
backend's other modules (and their importers) as they were.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvNew

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section hooks
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **No hooks meet the constructor's premise** (`BackendConfig.Hooks` nil, as
`DefaultBackendConfig` leaves it), at any parameters, write and commit resources. -/
theorem hooksOk_nil (P : BParams) (W Pk : BNames → IProp GF) :
    ⊢ hooksOk (GF := GF) P W Pk GoInterface.nil := by
  iunfold hooksOk
  iintro !> %γ %b %t _ _
  iunfold hooksSpec
  ileft; ipureintro; rfl

end hooks

end backend
end EtcdGrove
end Perennial
