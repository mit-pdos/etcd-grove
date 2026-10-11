/-
`NewRevBytes` (`revision.go`). Lean-first (no Rocq counterpart); see `RevBytes.lean`.
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

/-- `NewRevBytes()` is a fresh zeroed buffer of 17 bytes with room for the mark (capacity 18). -/
abbrev mvcc.NewRevBytes.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewRevBytes)) (Val #()))
  {{ (s : GoSlice), RET #s; s ↦* List.replicate 17 (W8 0) ∗ ownSliceCap w8 s (DFrac.own 1) ∗
      ⌜s.cap = W64 18⌝ }}

end spec

end EtcdGrove
end Perennial
