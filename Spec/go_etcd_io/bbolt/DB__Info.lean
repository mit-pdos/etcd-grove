/-
`db.Info()` (`db.go`): `&Info{Data: uintptr(&db.data[0]), PageSize: db.pageSize}`, read without a
lock.

**Users.** `backend.go:606` (`db.Info().PageSize`, under the backend's read transaction). Snippet:
`ReqBackendRead`.

**Proof sketch.** A live transaction of `db` keeps the mapping (a reader's `mmaplock` slot, or the
writer's `rwlock`, which a remap needs): `db.data` and `db.pageSize` are read from `boltTx`'s share of
`isBolt`'s mapping invariant; allocate the `Info`.

**Changes.** Unchanged (`txDB` instead of the old `txDB tx γ db`).

**Margin.** `PageSize` is `4096` (`OptsM.ok`'s default page size), not stated.
-/
module

public import Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.Info()` while a transaction of `db` is live: a fresh `*Info`. -/
def DB.Info.spec : Prop :=
  ∀ [HasExt osFsExt] (db tx : Loc) (γ : BoltName) (ns : Bool) (q : Qp) (T : TxView),
  {{ isBolt (GF := GF) db γ ns ∗ txDB tx db ∗ boltTx tx γ q T }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Info")) (Val #()))
  {{ (i : Loc), RET #i; boltTx tx γ q T ∗ ∃ v : Info, i ↦ v }}

end spec

end Bbolt
end EtcdGrove
end Perennial
