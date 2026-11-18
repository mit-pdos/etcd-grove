/-
`apierrors.NewResourceExpired` (`k8s.io/apimachinery/pkg/api/errors/errors.go`): a 410: the status `Failure`, reason `Expired`, code 410, no details (k8s etcd3 7e-2, D3). Lean-first (no Rocq counterpart).

(apierrors-fix, 2026-11-17; HasStatusCause fix (a), `notes/hasstatuscause-later-view.md`) The
post also gives the details, read-only, with no causes (`statusDetailsAt st []`): Go leaves `Details` `nil`.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs
public import Proof.k8s_io.apimachinery.pkg.api.errors.View

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

/-- `apierrors.NewResourceExpired(...)`: a 410: the status `Failure`, reason `Expired`, code 410, no details (k8s etcd3 7e-2, D3). -/
abbrev NewResourceExpired.spec : Prop :=
  ∀ (message : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.errors.NewResourceExpired)) (Val #message))
  {{ (p : Loc), RET #p; ∃ st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status, p ↦ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st ∗
      statusDetailsAt st [] ∗
      ⌜st.Status' = go!"Failure" ∧ st.Reason' = go!"Expired" ∧ st.Code' = W32 410 ∧
        st.Details' = null⌝ }}

end spec

end apierrors
end EtcdGrove
end Perennial
