/-
`(*bootstrappedBackend).Close()` (`bootstrap.go:180-182`): `s.be.Close()`, its error dropped.
Lean-first (no Rocq counterpart); stage R-D1 (2026-11-04), for `bootstrappedStorage.Close`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvStop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.Close()` (`bootstrap.go:180-182`: `s.be.Close()`, its error dropped), with the record's pointer
read-only, its backend `*backend` and the backend's whole open token (`backend.backend.Close.spec`'s):
once. -/
abbrev bootstrappedBackend.Close.spec : Prop :=
  ∀ (s : Loc) (bk : bootstrappedBackend)
    (γ : backend.BNames) (P : backend.BParams) (W Pk : IProp GF) (be : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      s ↦□ bk ∗
      ⌜bk.be' = interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #be⌝ ∗
      backend.isBackend γ P W Pk be ∗ backend.isStopChans γ be ∗ backend.bOpen γ 1 }}
    (App (Val (s @!! go.GoType.PointerType bootstrappedBackend.ty @!! go!"Close")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
