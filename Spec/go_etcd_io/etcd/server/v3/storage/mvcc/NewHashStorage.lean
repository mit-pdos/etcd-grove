/-
`NewHashStorage` (`hash.go`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `NewHashStorage(lg, s)` returns the store's hash storage (a `HashStorage` interface value of
a fresh `*hashStorage`, for the compaction's hashes: its `Store` is an axiom with no effect); it
takes no resource of the store `s`. -/
abbrev mvcc.NewHashStorage.spec : Prop :=
  ∀ (lg s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewHashStorage)) (Val #lg)) (Val #s))
  {{ (h : Loc), RET #(interface.mkOk (go.GoType.PointerType hashStorage.ty) #h); True }}

end spec

end EtcdGrove
end Perennial
