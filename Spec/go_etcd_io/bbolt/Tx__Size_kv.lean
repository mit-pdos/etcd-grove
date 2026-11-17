/-
`Tx.Size_kv` (bbolt). `tx.Size()`.
A corollary of bbolt's proved `Tx.Size` (`Spec/go_etcd_io/bbolt/Tx__Size.lean`) over the backend's
vocabulary (`InvBbolt.lean`), proved in `Proof/go_etcd_io/bbolt/Tx__Size_kv.lean` (stage S1 of
`notes/bbolt-integration-plan.md`, 2026-11-17; until then an axiom, the backend's trust boundary).
Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The backend: the buffers, bbolt as a
key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.bbolt backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `tx.Size()`: some size. -/
abbrev bbolt.Tx.Size_kv.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (q : Qp) (T : bbolt.TxView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ txLive tx γ q T }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Size")) (Val #()))
  {{ (n : w64), RET #n; txLive tx γ q T }}

end spec

end EtcdGrove
end Perennial
