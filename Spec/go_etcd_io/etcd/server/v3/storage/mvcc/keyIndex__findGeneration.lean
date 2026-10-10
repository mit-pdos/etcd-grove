/-
`keyIndex.findGeneration` (`key_index.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
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

/-- `ki.findGeneration(rev)`: `nil`, or the address of the generation of the key at `rev`
(`kiFindGen`), in the generations slice `gs`. A read, at any fraction. -/
abbrev mvcc.keyIndex.findGeneration.spec : Prop :=
  ∀ (p : Loc) (gs : GoSlice) (ki : mvcc.KeyIndex) (dq : DFrac) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownKi p gs ki dq }}
    (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"findGeneration")) (Val #rev))
  {{ RET #(mvcc.genPtr gs (mvcc.kiFindGen ki rev)); mvcc.ownKi p gs ki dq }}

end spec

end EtcdGrove
end Perennial
