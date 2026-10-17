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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `New(bcfg)`: the backend `newBackend` makes, as a `Backend`, or a panic. -/
abbrev backend.New.spec : Prop :=
  ∀ (cfg : BackendConfig) (P : BParams) (D : Data) (W Pk : BNames → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      boltOpenOptionsOk ∗ fileHolds cfg.Path' D ∗ ⌜P.Wf ∧ P.limit = cfg.BatchLimit'⌝ ∗
      hooksOk P W Pk cfg.Hooks' ∗ (∀ γ : BNames, hkOwn γ (hkData P D) ={⊤}=∗ W γ ∗ Pk γ) }}
    (App (Val (@! New)) (Val #cfg))
  {{ (r : val), RET r;
      (∃ (b : Loc) (γ : BNames),
        ⌜r = #(interface.mkOk (go.GoType.PointerType backend.ty) #b)⌝ ∗ newPost γ P W Pk b D) ∨
      ⌜∃ p : val, r = PanicV p⌝ }}

end spec

end EtcdGrove
end Perennial
