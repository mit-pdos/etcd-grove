/-
`keyIndex.doCompact` (`key_index.go`): compaction's walk (2026-10-13, unit 5a; `Compact.lean`, `InvCompact.lean`).
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

/-- `ki.doCompact(atRev, available)` of the key index `ki` (its generations walked by the code: some,
every one but the last with a revision, `gensOk`): `doCompact`'s generation (`compactGenIdx`) and
revision index in it (`compactRevIdx`, `-1` if none), the revision it keeps added to `available`
(`kiAvail`). A read of the key index, at any fraction (`keep` holds it shared, under `RLock`).
(Its walk's closure writes the map: `generation.walk`'s closure is effectful, `walkFnSpecR`.) -/
abbrev mvcc.keyIndex.doCompact.spec : Prop :=
  ∀ (p : Loc) (gs : GoSlice) (ki : mvcc.KeyIndex) (dq : DFrac) (atRev : w64) (m : GoMap)
    (A : GMap Revision Unit),
  mvcc.gensOk ki →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownKi p gs ki dq ∗ ownMap m (DFrac.own 1) A }}
    (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"doCompact")) (Val #atRev))
      (Val #m))
  {{ RET (PairV #(W64 (mvcc.compactGenIdx atRev ki.gens : Int)) #(W64 (mvcc.compactRevIdx atRev ki)));
      mvcc.ownKi p gs ki dq ∗ ownMap m (DFrac.own 1) (mvcc.availAdd A (mvcc.kiAvail atRev ki)) }}

end spec

end EtcdGrove
end Perennial
