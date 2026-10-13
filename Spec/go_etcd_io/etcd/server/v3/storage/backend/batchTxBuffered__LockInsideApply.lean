/-
`LockInsideApply` (the backend). `t.LockInsideApply()`: the batch lock, free state (`freeOk`) and the lock holder's resource `W`,
then the post-lock hook `f` (the client's share `dq` of it: `plHookRO γ f` once set for good) run
on the hooks' resource `Pk` and the caller's `Pre` (`{Pk ∗ Pre} f() {Q}`, as mvcc's contract
states it), or, with no hook set, `Q` made of `Pk ∗ Pre` by the caller.
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `t.LockInsideApply()`: the batch lock, free state (`freeOk`) and the lock holder's resource `W`,
then the post-lock hook `f` (the client's share `dq` of it: `plHookRO γ f` once set for good) run
on the hooks' resource `Pk` and the caller's `Pre` (`{Pk ∗ Pre} f() {Q}`, as mvcc's contract
states it), or, with no hook set, `Q` made of `Pk ∗ Pre` by the caller. -/
abbrev backend.batchTxBuffered.LockInsideApply.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (qo : Qp) (dq : DFrac) (f : GoFunc)
    (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ bOpen γ qo ∗ plHookAt γ dq f ∗ Pre ∗
      ((⌜f = func.nil⌝ ∗ (Pk ∗ Pre -∗ Q)) ∨
       (⌜f ≠ func.nil⌝ ∗ □ ({{ Pk ∗ Pre }} (App (Val #f) (Val #())) {{ RET #(); Q }}))) }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"LockInsideApply")) (Val #()))
  {{ RET #(); ∃ st : BSess, batchLocked γ P b st ∗ ⌜freeOk P st⌝ ∗ W ∗ Q ∗ bOpen γ qo ∗
      plHookAt γ dq f }}

end spec

end EtcdGrove
end Perennial
