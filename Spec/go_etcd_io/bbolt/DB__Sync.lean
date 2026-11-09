/-
`db.Sync()` (`db.go`): `fdatasync` of the file (logged).

**Users.** defrag (`backend.go:578, 947`: the temporary database, opened with `NoSync`, synced
before its close and rename). Snippet: `ReqDefrag`.

**Proof sketch.** Under the close right (the file is open: `db.file` is set), call OsFs's
`Fdatasync` on the database's fd (its spec over the file's `OsMeta`, which the crash invariant and
the open database share). At its step, open the client's update: the file's bytes now on disk are
the page cache's; if no meta page write is in flight (`σ.busy` false) and no sync failed before
(`σ.lost` false), every crash image is `σ.data`'s (`BoltSt.sync true`); a failed sync marks `lost`
(D2). Fire with the outcome `ok = (err = nil)`.

**Changes.** New.

**Margin.** A failed sync's `lost` is never cleared in a generation (it could be, once every page a
failed sync dropped is rewritten and synced).
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

/-- `db.Sync()` on an open database: the client's sync update fires at the `fdatasync` with its
outcome (`σ.sync ok`): on success with no commit's meta write in flight and no earlier failed sync,
only the committed data is recoverable. -/
def DB.Sync.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (ns : Bool) (S : Bool → IProp GF),
  {{ isBolt (GF := GF) db γ ns ∗ boltOpened db γ ∗
      AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (ok : Bool), boltState γ 1 (σ.sync ok), COMM S ok }> }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err; boltOpened db γ ∗
      ∃ ok : Bool, S ok ∗ ⌜err = GoInterface.nil ↔ ok = true⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
