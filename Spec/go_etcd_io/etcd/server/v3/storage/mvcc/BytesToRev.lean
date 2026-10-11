/-
`BytesToRev` (`revision.go`). Lean-first (no Rocq counterpart); see `RevBytes.lean`.
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

/-- `BytesToRev(bytes)` decodes the 17 bytes of a revision `r` with at most one byte after them
(`BytesToBucketKey`'s revision). -/
abbrev mvcc.BytesToRev.spec : Prop :=
  ∀ (s : GoSlice) (r : mvcc.Rev) (rest : List w8) (dq : DFrac),
  rest.length ≤ 1 → 0 ≤ sint.Z r.main → 0 ≤ sint.Z r.sub →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s ↦*{dq} (mvcc.revBytes r false ++ rest) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.BytesToRev)) (Val #s))
  {{ RET #(mvcc.revVal r); s ↦*{dq} (mvcc.revBytes r false ++ rest) }}

end spec

end EtcdGrove
end Perennial
