/-
`keyIndex.restore` (`key_index.go`; translated 2026-10-23, the restore plan's R0). Lean-first (no
Rocq counterpart); see `Model.lean`, `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Defs

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

/-- `ki.restore(lg, created, modified, ver)` (a non-nil logger): on a key index with no generation,
its one generation becomes `{created, ver, [modified]}` and `modified` its last change (`kiRestore`),
possibly reallocating the generations slice; on one with generations `lg.Panic` panics with its
message, the key index unchanged (the check precedes every write). -/
abbrev mvcc.keyIndex.restore.spec : Prop :=
  ∀ (p : Loc) (gs : GoSlice) (ki : mvcc.KeyIndex) (lg : Loc) (created modified : mvcc.Rev)
    (ver : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      ⌜lg ≠ null⌝ ∗ mvcc.ownKi p gs ki (DFrac.own 1) }}
    (App (App (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"restore")) (Val #lg))
      (Val #(mvcc.revVal created))) (Val #(mvcc.revVal modified))) (Val #ver))
  {{ (r : val), RET r;
      if ki.gens = [] then
        ⌜r = #()⌝ ∗ ∃ gs' : GoSlice,
          mvcc.ownKi p gs' (mvcc.kiRestore created.main modified ver) (DFrac.own 1)
      else
        ⌜r = PanicV #(go!"'restore' got an unexpected non-empty generations")⌝ ∗
          mvcc.ownKi p gs ki (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
