/-
`keyIndex.Less` (`key_index.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
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

/-- `a.Less(b)`: the keys' order (`bytes.Compare(a.key, b.key) == -1`, Go's `<` on the bytes). -/
abbrev mvcc.keyIndex.Less.spec : Prop :=
  ∀ (a b : Loc) (ka kb : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.kiKey a ka ∗ mvcc.kiKey b kb }}
    (App (Val (a @!! go.GoType.PointerType keyIndex.ty @!! go!"Less")) (Val #b))
  {{ RET #(decide (go.GoStringLt ka kb)); True }}

end spec

end EtcdGrove
end Perennial
