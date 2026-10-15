/-
`bucket.Name` (`bucket.go`). `b.Name()`: its `name` slice.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.schema

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage go_etcd_io.etcd.server.v3.storage.schema

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `b.Name()`: its `name` slice. -/
abbrev schema.bucket.Name.spec : Prop :=
  ∀ (b : bucket),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }}
    (App (Val (b @!! bucket.ty @!! go!"Name")) (Val #()))
  {{ RET #b.name'; True }}

end spec

end EtcdGrove
end Perennial
