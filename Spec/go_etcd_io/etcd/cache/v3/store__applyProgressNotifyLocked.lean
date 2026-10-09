/-
`store.applyProgressNotifyLocked(revision)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `s.applyProgressNotifyLocked(revision)`, under the write lock: `latest.rev` becomes
`revision` unless it is `0`. -/
abbrev store.applyProgressNotifyLocked.spec : Prop :=
  ∀ (s : Loc) (γ : StoreNames) (cap : Nat) (lr revision : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isStore s γ cap ∗ storeLatestRevAddr s ↦ lr }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"applyProgressNotifyLocked")) (Val #revision))
  {{ RET #(); storeLatestRevAddr s ↦ (if lr = W64 0 then lr else revision) }}

end spec

end EtcdGrove
end Perennial
