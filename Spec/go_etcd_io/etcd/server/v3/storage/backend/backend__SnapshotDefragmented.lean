/-
`SnapshotDefragmented` (the backend, `backend.go`; `etcd#21776`). `b.SnapshotDefragmented()`:
calls `b.snapshotDefragmented(snapshotCompactTxMaxBytes)`. Lean-first (no Rocq counterpart); the
vocabulary is `InvSnapshot.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

set_option linter.iris.dupNamespace false

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

/-- `b.SnapshotDefragmented()`: a defragmented snapshot of bbolt's committed data `D`, read as the
caller's observation `Q` says of every commit, or a non-nil error if creating or compacting into the
temporary database fails. -/
abbrev backend.backend.SnapshotDefragmented.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (qo : Qp) (R : IProp GF)
    (Q : VData → GMap (GoString × GoString) GoString → GMap GoString BktData → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bOpen γ qo ∗ wbTok γ ∗ R ∗
      □ (∀ (vd : VData) (d : GMap (GoString × GoString) GoString) (r : GMap GoString BktData),
        R -∗ W -∗ Pk -∗ viewAt γ vd -∗ hkOwn γ d -∗ rbOwn γ r -∗ ⌜Q vd d r⌝) }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"SnapshotDefragmented")) (Val #()))
  {{ (s : GoInterface) (err : GoInterface), RET (PairV #s #err);
      bOpen γ qo ∗ R ∗
      ((⌜err ≠ GoInterface.nil ∧ s = GoInterface.nil⌝) ∨
        (∃ (ds : Loc) (D : Data),
          ⌜err = GoInterface.nil ∧
            s = interface.mkOk (go.GoType.PointerType defragmentedSnapshot.ty) #ds ∧
            Q (sData P D) (hkData P D) (rbData P D)⌝ ∗
          defragSnapOpen ds D)) }}

end spec

end EtcdGrove
end Perennial
