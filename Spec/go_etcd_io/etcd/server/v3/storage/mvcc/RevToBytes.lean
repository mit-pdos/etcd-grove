/-
`RevToBytes` (`revision.go`). Lean-first (no Rocq counterpart); see `RevBytes.lean`.
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

/-- `RevToBytes(rev, bytes)` writes the 17 bytes of `rev` into `bytes`, a buffer of 17 or 18
bytes, and returns it (its 18th byte, if any, as it was). -/
abbrev mvcc.RevToBytes.spec : Prop :=
  ∀ (rev : Revision) (s : GoSlice) (bs : List w8), bs.length = 17 ∨ bs.length = 18 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s ↦* bs ∗ ownSliceCap w8 s (DFrac.own 1) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.RevToBytes)) (Val #rev)) (Val #s))
  {{ (s' : GoSlice), RET #s';
      s' ↦* (mvcc.revBytes (mvcc.revOf rev) false ++ bs.drop 17) ∗ ownSliceCap w8 s' (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
