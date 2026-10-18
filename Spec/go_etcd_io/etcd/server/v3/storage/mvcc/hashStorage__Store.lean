/-
`hashStorage.Store` (`hash.go`): the trust boundary.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.HashDefs

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
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `hs.Store(hash)` of a hash storage with a logger (`hashStorageOk`: `Store` logs first, a nil
logger panics; audit B4b, 2026-10-18) returns (the stored hashes are not modelled). -/
abbrev mvcc.hashStorage.Store.spec : Prop :=
  ∀ (hp : Loc) (h : KeyValueHash),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.hashStorageOk hp }}
    (App (Val (hp @!! go.GoType.PointerType hashStorage.ty @!! go!"Store")) (Val #h))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
