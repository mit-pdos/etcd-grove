/-
`New` (`backend.go`). `New(bcfg)`: `newBackend(bcfg)` as a `Backend`. Lean-first (no Rocq
counterpart); 2026-10-17, branch `construct` (`notes/STATUS.md`, "Item 6"). The pre and post are
`newBackend`'s (`Spec/go_etcd_io/etcd/server/v3/storage/backend/newBackend.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvNew
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BboltOptions

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `New(bcfg)`: the backend `newBackend` makes, as a `Backend`, or a panic. (D22 receiver epochs,
S8a, 2026-10-24) The creator's batch-lock step takes the fresh backend's payment rights (`bFresh`)
and gives `K` in their place (`newPostK`). -/
abbrev backend.New.spec : Prop :=
  ∀ (cfg : BackendConfig) (P : BParams) (D : Data) (W Pk K : BNames → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      fileHolds cfg.Path' D ∗ ⌜P.Wf ∧ P.limit = cfg.BatchLimit'⌝ ∗
      hooksOk P W Pk cfg.Hooks' ∗
      (∀ γ : BNames, hkOwn γ (hkData P D) ∗ bFresh γ ={⊤}=∗ W γ ∗ Pk γ ∗ K γ) }}
    (App (Val (@! New)) (Val #cfg))
  {{ (r : val), RET r;
      (∃ (b : Loc) (γ : BNames),
        ⌜r = #(interface.mkOk (go.GoType.PointerType backend.ty) #b)⌝ ∗ newPostK γ P W Pk K b D) ∨
      ⌜∃ p : val, r = PanicV p⌝ }}

end spec

end EtcdGrove
end Perennial
