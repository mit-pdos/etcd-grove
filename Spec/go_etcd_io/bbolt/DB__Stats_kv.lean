/-
`DB.Stats_kv` (bbolt). `db.Stats()` with a live transaction's reader slot.
A corollary of bbolt's proved `DB.Stats` (`Spec/go_etcd_io/bbolt/DB__Stats.lean`) over the backend's
vocabulary (`InvBbolt.lean`), proved in `Proof/go_etcd_io/bbolt/DB__Stats_kv.lean` (stage S1 of
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

/-- `db.Stats()`, paid for by a live transaction held whole (bbolt's `statSlot (some (tx, T))`:
the transaction's slot covers `statlock`'s reader; S1, until then `isDB db` alone): some
statistics. -/
abbrev bbolt.DB.Stats_kv.spec : Prop :=
  ∀ (db tx : Loc) (γ : DBNames) (T : bbolt.TxView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ isDB db γ ∗ txLive tx γ 1 T }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Stats")) (Val #()))
  {{ (s : Stats), RET #s; txLive tx γ 1 T }}

end spec

end EtcdGrove
end Perennial
