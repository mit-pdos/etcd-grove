/-
`db.Path()` (`db.go`): `db.path`, read without a lock.

**Users.** defrag (`backend.go:515, 651, 712`, with the database open). Snippet: `ReqDefrag`.

**Proof sketch.** Only `close` writes `db.path` (`db.go:832`, under the locks; and `Open` before
`db` is shared); while any share of the close right is held nobody closes `db`, so `isBolt`'s
field invariant lends the field (read-only, a fraction per share): `γ.path`.

**Changes.** New.
**Changes (2026-11-12, `notes/specs-only/ledger.md`, the close right's share).** Takes any share `q`
of the close right and gives it back (was the whole: etcd's defrag calls
`Path` without the backend's lock, `backend.go:515, 712`, so it cannot hold the exclusive right).
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

/-- `db.Path()` on an open database (any share of its close right): its file's path. -/
def DB.Path.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (ns : Bool) (q : Qp),
  {{ isBolt (GF := GF) db γ ns ∗ boltOpened db γ q }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Path")) (Val #()))
  {{ RET #γ.path; boltOpened db γ q }}

end spec

end Bbolt
end EtcdGrove
end Perennial
