/-
`DB.Info_kv` (bbolt). `db.Info()` while a transaction of `db` is live: a pointer to some information, read-only.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/DB__Info_kv.lean`. Lean-first (no Rocq
counterpart); see `notes/decisions.md`, "The backend: the buffers, bbolt as a key-value contract,
the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.bbolt backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.Info()` while a transaction `tx` of `db` is live: a pointer to some information,
read-only. (Go's `Info` asserts `db.data != nil` and reads it without `mmaplock`: it panics after
`Close`, and a remap may race with it. A live transaction excludes both: a reader holds
`mmaplock.RLock`, the writer is the one that remaps, and `Close` waits for both. The premise
since audit B4b, 2026-10-18; until then only `isDB db`, which `Close` leaves true.) -/
abbrev bbolt.DB.Info_kv.spec : Prop :=
  ∀ (db tx : Loc) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ isDB db ∗ txDB tx db ∗ txLive tx q }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Info")) (Val #()))
  {{ (i : Loc), RET #i; (∃ v : Info, i ↦□ v) ∗ txLive tx q }}

end spec

end EtcdGrove
end Perennial
