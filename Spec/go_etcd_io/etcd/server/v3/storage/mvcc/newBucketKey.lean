/-
`newBucketKey` (`revision.go`). Lean-first (no Rocq counterpart); see `RevBytes.lean`.
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

/-- `newBucketKey(main, sub, isTombstone)` is the bucket key of those fields. -/
abbrev mvcc.newBucketKey.spec : Prop :=
  ∀ (main sub : w64) (tomb : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newBucketKey)) (Val #main))
      (Val #sub)) (Val #tomb))
  {{ RET #(BucketKey.mk (Revision.mk main sub) tomb); True }}

end spec

end EtcdGrove
end Perennial
