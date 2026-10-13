/-
`bucketBuffer.ForEach` (`tx_buffer.go`). `bb.ForEach(visitor)`: the visitor on each entry in order, until one returns an error,
which `ForEach` returns.
Lean-first (no Rocq counterpart); see `InvBuffer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `bb.ForEach(visitor)`: the visitor on each entry in order, until one returns an error,
which `ForEach` returns. -/
abbrev backend.bucketBuffer.ForEach.spec : Prop :=
  ∀ (bb : Loc) (dq : DFrac) (p : BBPhys) (es : List Ent) (f : GoFunc) (P : Nat → IProp GF)
    (Q : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bbAt bb dq p es ∗ visitorSpec f es P Q ∗ P 0 }}
    (App (Val (bb @!! go.GoType.PointerType bucketBuffer.ty @!! go!"ForEach")) (Val #f))
  {{ (err : GoInterface), RET #err; bbAt bb dq p es ∗
      ((⌜err = GoInterface.nil⌝ ∗ P es.length) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Q err)) }}

end spec

end EtcdGrove
end Perennial
