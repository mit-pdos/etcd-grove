/-
`(*mvcc.store).HashStorage()` (`kvstore.go`: `return s.hashes`): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `s.HashStorage()` on a store returns its hash storage (some interface value). -/
abbrev mvcc.store.HashStorage.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isStore s γ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.store.ty @!!
      go!"HashStorage")) (Val #()))
  {{ (h : GoInterface), RET #h; True }}

end spec

end EtcdGrove
end Perennial
