/-
`db.Close()` (`db.go`): waits for the writer (`rwlock`), `metalock` and every reader (`mmaplock`),
then, if still open, unmaps, unlocks and closes the file.

**Users.** `backend.Close` (`backend.go:486`), defrag (`backend.go:554, 570, 582`: the temporary
database closed twice on an error path, `cleanupTmpDB`), `examples/bbolt/bank/bbolttest.go` (`Boot`).
Snippets: `ReqDefrag` (a second `Close`), `ReqBank`.

**Proof sketch.** Take `rwlock`, `metalock`, `mmaplock` (writer side: every reader slot is back in
the pool); if `opened` (the close right's holder), move the file's OsFs halves from the open
database's lock resources back into `boltFile γ`'s closed state (munmap's, funlock's and the fd
close's errnos leave stale fds or mappings, which the closed state tolerates), set `opened = false`,
and record `dbClosed db`; release. A later `Close` finds `opened` false and returns nil.

**Changes.** The old spec (persistent `isBolt` alone) gave `True` (D9: the file lost to the caller).
Now the close right's holder gets the closed file back (for a reopen, etcd's defrag), and a closed
database may be closed again (`cleanupTmpDB` after `finishDefrag`'s `Close`). A `Close` by someone
without the right while the database is open is no longer allowed: the right's holder relies on the
database staying open (`Path`, `Sync`).

**Margin.** The error (a system call's) is not described: the file is closed either way.
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

/-- `db.Close()`: with the close right, closes `db` and gives the file back closed (`boltClosed
γ`), whatever the error; on a database already closed, does nothing. -/
def DB.Close.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (ns tok : Bool),
  {{ isBolt (GF := GF) db γ ns ∗ (if tok then boltOpened db γ else dbClosed db) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; dbClosed db ∗
      (if tok then boltClosed γ else ⌜err = GoInterface.nil⌝) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
