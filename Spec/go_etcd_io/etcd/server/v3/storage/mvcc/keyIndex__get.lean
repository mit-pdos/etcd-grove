/-
`keyIndex.get` (`key_index.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
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

/-- `ki.get(lg, atRev)` (a non-nil logger): if the key index is empty (`isEmpty`), `lg.Panic`
panics with its message; else the key's revision, create revision and version at `atRev`, or
`ErrRevisionNotFound` (`kiGet`, `kiGetVal`), with the lease recorded beside the revision
(`lf` of it; `NoLease` with `ErrRevisionNotFound`). A read, at any fraction. -/
abbrev mvcc.keyIndex.get.spec : Prop :=
  ∀ (p : Loc) (gs : GoSlice) (ki : mvcc.KeyIndex) (lf : mvcc.Rev → w64) (k : GoString) (dq : DFrac) (lg : Loc)
    (atRev : w64) (e : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      ⌜lg ≠ null⌝ ∗ mvcc.kiKey p k ∗ mvcc.ownKi p gs ki lf dq ∗
      globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e }}
    (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"get")) (Val #lg)) (Val #atRev))
  {{ (r : val), RET r;
      if mvcc.kiIsEmpty ki then
        ⌜r = PanicV #(go!"'get' got an unexpected empty keyIndex")⌝ ∗ mvcc.ownKi p gs ki lf dq
      else ⌜r = mvcc.kiGetVal ki lf atRev (GoInterface.ok e)⌝ ∗ mvcc.ownKi p gs ki lf dq }}

end spec

end EtcdGrove
end Perennial
