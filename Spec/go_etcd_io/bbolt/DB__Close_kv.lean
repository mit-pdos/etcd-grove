/-
`DB.Close_kv` (bbolt). `db.Close()` (it waits for the open transactions): the database closed, and
(2026-11-04, R2b-3c, the user's approval) its file holding the committed data.
bbolt's key-value contract as the backend uses it (`InvBbolt.lean`); since S3e a theorem
(`Proof/go_etcd_io/bbolt/DB__Close_kv.lean`), until then an axiom. Lean-first (no Rocq
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

/-- `db.Close()` (it waits for the open transactions): the database closed, `nil`.
(2026-11-04, R2b-3c, the user's approval; until then it took only `isDB db` and gave nothing) With
the database owned at its committed data `D` (`ownDB`: no write transaction open), the file it is
(`dbFile`) holds `D` once closed (`fileHolds`, what a reopen reads): every commit wrote its pages and
meta page before it returned, `Close` writes nothing. (S3e, 2026-11-17) A theorem, over bbolt's
`DB.Close_ownNoErr.spec`, with no error case (until then an error with `¬ dbCloseOk`, D22 receiver
epochs, S8d); `dbFile` takes the database's names. -/
abbrev bbolt.DB.Close_kv.spec : Prop :=
  ∀ (db : Loc) (γ : DBNames) (D : backend.Data) (path : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ isDB db γ ∗ dbFile db γ path ∗ ownDB db γ D }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ backend.fileHolds path D }}

end spec

end EtcdGrove
end Perennial
