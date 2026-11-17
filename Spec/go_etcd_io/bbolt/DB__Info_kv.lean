/-
`DB.Info_kv` (bbolt). `db.Info()` while a transaction of `db` is live.
A corollary of bbolt's proved `DB.Info` (`Spec/go_etcd_io/bbolt/DB__Info.lean`) over the backend's
vocabulary (`InvBbolt.lean`), proved in `Proof/go_etcd_io/bbolt/DB__Info_kv.lean` (stage S1 of
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

/-- `db.Info()` while a transaction `tx` of `db` is live: a pointer to a fresh `Info` (S1: bbolt's proved spec; until then
read-only).
(Go's `Info` asserts `db.data != nil` and reads it without `mmaplock`: it panics after `Close`, and
a remap may race with it. A live transaction excludes both.) -/
abbrev bbolt.DB.Info_kv.spec : Prop :=
  ∀ (db tx : Loc) (γ : DBNames) (q : Qp) (T : bbolt.TxView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ isDB db γ ∗ backend.txDB tx γ db ∗ txLive tx γ q T }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Info")) (Val #()))
  {{ (i : Loc), RET #i; (∃ v : Info, i ↦ v) ∗ txLive tx γ q T }}

end spec

end EtcdGrove
end Perennial
