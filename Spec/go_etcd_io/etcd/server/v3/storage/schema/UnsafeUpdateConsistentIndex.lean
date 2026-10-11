/-
`schema.UnsafeUpdateConsistentIndex(tx, index, term)`. Lean-first (no Rocq counterpart);
see `InvCindex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `UnsafeUpdateConsistentIndex(tx, index, term)`: `unsafeUpdateConsistentIndex` with the
monotonicity check. -/
abbrev schema.UnsafeUpdateConsistentIndex.spec : Prop :=
  ∀ (tx : GoInterfaceOk) (TM : MetaCI → IProp GF) (m : MetaCI) (index term : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ metaWriter tx TM ∗ TM m ∗ ⌜index ≠ W64 0 → uint.Z m.1 ≤ uint.Z index⌝ }}
    (App (App (App (Val (@! schema.UnsafeUpdateConsistentIndex)) (Val #(GoInterface.ok tx)))
      (Val #index)) (Val #term))
  {{ RET #(); TM (metaAfterSave m index term) }}

end spec

end EtcdGrove
end Perennial
