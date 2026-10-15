/-
`(*consistentIndex).UnsafeSave(tx)`. Lean-first (no Rocq counterpart); see `InvCindex.lean`.
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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- `ci.UnsafeSave(tx)` (by the holder of the batch transaction's lock, whose meta keys are
`TM m`) reads the index (the linearization point: the caller learns it is `k` and must know
that a non-zero `k` is not below the stored index, which etcd checks under `ETCD_VERIFY`),
then some term `t`, and writes them: the meta keys become `metaAfterSave m k t`. -/
abbrev consistentIndex.UnsafeSave.spec : Prop :=
  ∀ (ci : Loc) (γ : CINames) (tx : GoInterfaceOk) (TM : MetaCI → IProp GF) (PTi PTt : IProp GF)
    (m : MetaCI),
  ⊢ ∀ Φ : val → IProp GF,
    (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗ isCI ci γ ∗ metaWriter tx TM PTi PTt ∗ TM m ∗ PTi ∗ PTt) -∗
    (|={⊤ \ ↑ciN, ∅}=> ∃ k : w64, ciIdx γ k ∗ (ciIdx γ k ={∅, ⊤ \ ↑ciN}=∗
      ⌜k ≠ W64 0 → uint.Z m.1 ≤ uint.Z k⌝ ∗ ∀ t : w64, TM (metaAfterSave m k t) -∗ Φ #())) -∗
    WP (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"UnsafeSave")) (Val #(GoInterface.ok tx))) {{ Φ }}

end spec

end EtcdGrove
end Perennial
