/-
`db.Path()` (`db.go`): `db.path`, read without a lock.

**Users.** defrag (`backend.go:515, 651, 712`, with the database open). Snippet: `ReqDefrag`.

**Proof sketch.** `close` writes `db.path` under the locks; while the close right is held nobody
closes `db`, so `isBolt`'s field invariant lends the field (read-only): `γ.path`.

**Changes.** New.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api

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

/-- `db.Path()` on an open database: its file's path. -/
def DB.Path.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (ns : Bool),
  {{ isBolt (GF := GF) db γ ns ∗ boltOpened db γ }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Path")) (Val #()))
  {{ RET #γ.path; boltOpened db γ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
