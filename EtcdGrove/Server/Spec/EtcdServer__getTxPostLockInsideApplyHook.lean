/-
`(*EtcdServer).getTxPostLockInsideApplyHook()` (server.go): the backend's post-lock hook.
Lean-first (no Rocq counterpart); see `InvServer.lean`, `InvApply.lean`.
-/
import EtcdGrove.Server.InvServer

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.getTxPostLockInsideApplyHook()` returns the hook
`func() { applyingIdx, applyingTerm := ci.ConsistentApplyingIndex(); if applyingIdx >
ci.UnsafeConsistentIndex() { ci.SetConsistentIndex(applyingIdx, applyingTerm) } }`, which
meets the protocol's `hookSpec` (for any batch transaction meta-keys resource `TM`): under the
batch lock, it sets the consistent index to the entry being applied. -/
abbrev EtcdServer.getTxPostLockInsideApplyHook.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerCI s γ ci }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"getTxPostLockInsideApplyHook"))
      (Val #()))
  {{ (f : val), RET f; hookSpec γ ci TM f }}

end spec

end EtcdGrove
end Perennial
