/-
`keyIndex.compact` (`key_index.go`): compaction (2026-10-13, unit 5a; `Compact.lean`).
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

/-- `ki.compact(lg, atRev, available)` of a key index that is not empty (the tree never holds an
empty one: `compact` would panic, `lg.Panic`) whose generations the walk can read (`gensOk`):
the key index compacted (`kiCompact`: `doCompact`'s generation cut at its revision, the earlier
ones dropped; a new generations slice), and the revision it keeps added to `available`. -/
abbrev mvcc.keyIndex.compact.spec : Prop :=
  ∀ (p : Loc) (gs : GoSlice) (ki : mvcc.KeyIndex) (lg : Loc) (atRev : w64) (m : GoMap)
    (A : GMap Revision Unit),
  lg ≠ null → mvcc.gensOk ki → mvcc.kiIsEmpty ki = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownKi p gs ki (DFrac.own 1) ∗ ownMap m (DFrac.own 1) A }}
    (App (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"compact")) (Val #lg))
      (Val #atRev)) (Val #m))
  {{ RET #(); ∃ gs' : GoSlice, mvcc.ownKi p gs' (mvcc.kiCompact atRev ki) (DFrac.own 1) ∗
      ownMap m (DFrac.own 1) (mvcc.availAdd A (mvcc.kiAvail atRev ki)) }}

end spec

end EtcdGrove
end Perennial
