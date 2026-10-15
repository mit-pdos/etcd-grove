/-
`keyIndex.keep` (`key_index.go`): the hash's kept revisions (2026-10-13, unit 5a; `Compact.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

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

/-- `ki.keep(atRev, available)`, reading the key index (any fraction): `available` with the
revision `keep` keeps (`keepApply`: `doCompact`'s, but not a tombstone ending a generation that
is not the last, `kiKeep`; nothing for an empty key index). -/
abbrev mvcc.keyIndex.keep.spec : Prop :=
  ∀ (p : Loc) (gs : GoSlice) (ki : mvcc.KeyIndex) (dq : DFrac) (atRev : w64) (m : GoMap)
    (A : GMap Revision Unit),
  mvcc.gensOk ki →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownKi p gs ki dq ∗ ownMap m (DFrac.own 1) A }}
    (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"keep")) (Val #atRev)) (Val #m))
  {{ RET #(); mvcc.ownKi p gs ki dq ∗ ownMap m (DFrac.own 1) (mvcc.keepApply A atRev ki) }}

end spec

end EtcdGrove
end Perennial
