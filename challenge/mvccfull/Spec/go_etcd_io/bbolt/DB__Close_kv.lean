/-
`DB.Close_kv` (bbolt). `db.Close()` (it waits for the open transactions): the database closed, and
(2026-11-04, R2b-3c, the user's approval) its file holding the committed data.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/DB__Close_kv.lean`. Lean-first (no Rocq
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.Close()` (it waits for the open transactions): the database closed, `nil` or an error the
environment caused (`¬ dbCloseOk`: D22 receiver epochs, S8d, 2026-10-25). (2026-11-04, R2b-3c, the
user's approval; until then it took only `isDB db` and gave nothing) With the database owned at its
committed data `D` (`ownDB`: no write transaction open), the file it is (`dbFile`) holds `D` once
closed (`fileHolds`, what a reopen reads): every commit wrote its pages and meta page before it
returned, `Close` writes nothing (graceful stops in one process: an unsynced write reads back). -/
abbrev bbolt.DB.Close_kv.spec : Prop :=
  ∀ (db : Loc) (γ : DBNames) (D : Data) (path : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ isDB db ∗ dbFile db path ∗ ownDB db γ D }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ fileHolds path D) ∨ ⌜¬ dbCloseOk⌝ }}

end spec

end EtcdGrove
end Perennial
