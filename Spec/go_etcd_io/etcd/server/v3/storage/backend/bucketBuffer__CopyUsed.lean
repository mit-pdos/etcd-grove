/-
`bucketBuffer.CopyUsed` (`tx_buffer.go`). `bb.CopyUsed()`: a new buffer of the entries, exactly as many slots (its `verify.Assert`
holds); the buffer unchanged (any fraction).
Lean-first (no Rocq counterpart); see `InvBuffer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Assert

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

/-- `bb.CopyUsed()`: a new buffer of the entries, exactly as many slots (its `verify.Assert`
holds); the buffer unchanged (any fraction). -/
abbrev backend.bucketBuffer.CopyUsed.spec : Prop :=
  ∀ (bb : Loc) (dq : DFrac) (p : BBPhys) (es : List Ent),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bbAt bb dq p es }}
    (App (Val (bb @!! go.GoType.PointerType bucketBuffer.ty @!! go!"CopyUsed")) (Val #()))
  {{ (c : Loc), RET #c; bbAt bb dq p es ∗
      ∃ p' : BBPhys, bbAt c (DFrac.own 1) p' es ∗ ⌜p'.kvs.length = es.length⌝ }}

end spec

end EtcdGrove
end Perennial
