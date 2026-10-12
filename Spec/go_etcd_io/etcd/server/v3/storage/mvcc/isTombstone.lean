/-
`isTombstone` (`revision.go`). Lean-first (no Rocq counterpart); see `RevBytes.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevBytes

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

/-- `isTombstone(b)` decides `isTomb`: 18 bytes, the last the mark `'t'`. -/
abbrev mvcc.isTombstone.spec : Prop :=
  ∀ (s : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ s ↦*{dq} bs }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.isTombstone)) (Val #s))
  {{ RET #(mvcc.isTomb bs); s ↦*{dq} bs }}

end spec

end EtcdGrove
end Perennial
