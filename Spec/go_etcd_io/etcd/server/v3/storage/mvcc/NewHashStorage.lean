/-
`NewHashStorage` (`hash.go`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.HashDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `NewHashStorage(lg, s)` returns the store's hash storage (a `HashStorage` interface value of
a fresh `*hashStorage`, for the compaction's hashes: its `Store` is an axiom with no effect), with
the logger given (`hashStorageOk`, for a non-nil one: `Store` logs through it; audit B4b,
2026-10-18); it takes no resource of the store `s`. -/
abbrev mvcc.NewHashStorage.spec : Prop :=
  ∀ (lg s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ ⌜lg ≠ null⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewHashStorage)) (Val #lg)) (Val #s))
  {{ (h : Loc), RET #(interface.mkOk (go.GoType.PointerType hashStorage.ty) #h);
      mvcc.hashStorageOk h }}

end spec

end EtcdGrove
end Perennial
