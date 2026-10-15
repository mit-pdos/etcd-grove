/-
`bucket.String` (`bucket.go`). `b.String()`: its name's bytes as a string (`string(b.Name())`).
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

/-- `b.String()`: its name's bytes as a string (`string(b.Name())`). -/
abbrev schema.bucket.String.spec : Prop :=
  ∀ (b : bucket) (s : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ b.name' ↦*{dq} s }}
    (App (Val (b @!! bucket.ty @!! go!"String")) (Val #()))
  {{ RET #s; b.name' ↦*{dq} s }}

end spec

end EtcdGrove
end Perennial
