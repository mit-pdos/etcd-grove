/-
`(*BackendHooks).OnPreCommitUnsafe(tx)` (`server/storage/hooks.go`). Lean-first (no Rocq
counterpart); see `Proof/go_etcd_io/etcd/server/v3/storage/InvHooks.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvHooks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage backend storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **The server's pre-commit hook** `bh.OnPreCommitUnsafe(tx)`, on the backend's batch
transaction `t` held in the hook's window (`hookPre`), with the hooks' resource `Pk`: if the
indexer's save is a hook step leaving room for one put (`saveSpec`), the whole hook is a hook
step (the `confState` save, when dirty, is one put into `Meta`). The backend is needed only
after the call's first step (`▷ isBackend`, and so the indexer's save, `▷ saveSpec`): the
backend's own contract (`hooksSpec`, inside `isBackend`) is then derivable by Löb induction
(`isBackend_of_hooks`). -/
abbrev storage.BackendHooks.OnPreCommitUnsafe.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t bh : Loc) (ix : GoInterfaceOk) (lg : Loc)
    (st : BSess),
  hooksParams P →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackendHooks bh ix lg ∗ ▷ saveSpec γ P Pk b t ix ∗ ▷ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ Pk ∗ ⌜hookPre P st⌝ }}
    (App (Val (bh @!! go.GoType.PointerType BackendHooks.ty @!! go!"OnPreCommitUnsafe"))
      (Val #(interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) #t)))
  {{ RET #(); ∃ st' : BSess, batchLocked γ P b st' ∗ Pk ∗ ⌜hookStep P st st'⌝ }}

end spec

end EtcdGrove
end Perennial
