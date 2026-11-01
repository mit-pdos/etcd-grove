/-
`(*mvcc.store).HashStorage()` (`kvstore.go`: `return s.hashes`): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- **Candidate** (2026-11-01, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `s.HashStorage()`: the store's hash storage. -/
abbrev mvcc.store.HashStorage.specC : Prop :=
  ∀ (s : Loc) (γ : mvcc.MvccName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isMvcc s γ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.store.ty @!!
      go!"HashStorage")) (Val #()))
  {{ (hi : GoInterface), RET #hi;
      ∃ hs : Loc, ⌜hi = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.hashStorage.ty) #hs⌝ ∗
        mvcc.isHashStorage hs γ }}

end spec

end EtcdGrove
end Perennial
