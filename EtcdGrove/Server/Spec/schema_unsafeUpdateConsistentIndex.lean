/-
`schema.unsafeUpdateConsistentIndex(tx, index, term, allowDecreasing)`. Lean-first (no Rocq
counterpart); see `InvCindex.lean`.
-/
import EtcdGrove.Server.InvCindex

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `unsafeUpdateConsistentIndex(tx, index, term, allowDecreasing)` writes `index` (if not 0)
and `term` (if not 0) to the meta keys of the batch transaction `tx`. Unless
`allowDecreasing`, it first checks, under `ETCD_VERIFY`, that `index` is not below the stored
index (`verify.Verify`, which panics otherwise): the precondition says the check passes. -/
abbrev schema.unsafeUpdateConsistentIndex.spec : Prop :=
  ∀ (tx : GoInterfaceOk) (TM : MetaCI → IProp GF) (m : MetaCI) (index term : w64)
    (allowDecreasing : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ metaWriter tx TM ∗ TM m ∗
      ⌜allowDecreasing = false → index ≠ W64 0 → uint.Z m.1 ≤ uint.Z index⌝ }}
    (App (App (App (App (Val (@! schema.unsafeUpdateConsistentIndex)) (Val #(GoInterface.ok tx)))
      (Val #index)) (Val #term)) (Val #allowDecreasing))
  {{ RET #(); TM (metaAfterSave m index term) }}

end spec

end EtcdGrove
end Perennial
