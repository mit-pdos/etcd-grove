/-
**A WAL directory holds no WAL** (2026-11-03; the WAL's API, the user's choice of an axiomatized
token: `notes/decisions.md`, "The WAL's API", change 6). Lean-first.

`walDirFresh dir` (timeless; axiomatized, as `netAddrFree`): the directory `dir` holds no
WAL, so that `bootstrap` on it starts a new member (`wal.Exist(dir)` false). Program start gives it
once for each directory of the members the program starts (`goose_adequacy_start`'s `startRights`,
under the environment premise `walDirsAbsent`); a first start's `bootstrap` consumes it. Nothing
else produces it, so a directory is started fresh once in a run; a restart reads a closed WAL's
files instead (`walFiles`, `storage/WalRecs.lean`). No axiom says it is exclusive (as for
`netAddrFree`): read as `True` every axiom about it holds, which is the start axiom's
satisfiability argument (`Proof/runtime/Start.lean`).
-/
module

public import Perennial.GooseLang.Lang
public import Perennial.ProgramLogic.Bounds

@[expose] public section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- **The directory `dir` holds no WAL** (axiomatized; see the file header). -/
axiom walDirFresh {GF : BundledGFunctors} [GooseExts] (dir : GoString) : IProp GF

/-- It is timeless (an abstract fact of the file system, read in one step). -/
axiom walDirFresh_timeless {GF : BundledGFunctors} [GooseExts] (dir : GoString) :
    Timeless (walDirFresh (GF := GF) dir)

attribute [instance] walDirFresh_timeless

end EtcdGrove
end Perennial
