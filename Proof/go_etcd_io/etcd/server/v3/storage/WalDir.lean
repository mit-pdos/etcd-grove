/-
**A data directory is fresh** (2026-11-03; the WAL's API, the user's choice of an axiomatized
token: `notes/decisions.md`, "The WAL's API", change 6; sweep repairs 1, W3/W4, 2026-11-07: of the
data directory, until then `walDirFresh` of its WAL directory). Lean-first.

`dataDirFresh dd` (timeless; axiomatized, as `netAddrFree`): the data directory `dd` is absent or
empty, so it holds no backend file at `config.backendPathOf dd`. (2026-11-24) No contract takes it any
more: `bootstrap`'s slot (`wal.bootRes`) takes the data directory's fresh area (`dataAreaFresh`, a claim
on the tree that says the same); until then `bootstrap` took it for a new member over an empty backend
(`bootstrapContract`'s `"%HD"`, `"%HDr"`, `"%HmEmpty"`). It says nothing of the WAL (wal-link P2, 2026-11-19: the WAL is in a dedicated
WAL directory outside `dd`, whose fresh area is `walAreaFresh`, allocated at adequacy; until then
also no WAL in `dd`'s WAL directory, `wal.Exist` false). Program start gives it once for each data directory of the members the
program starts (`goose_adequacy_start`'s `startRights`, under the environment premise
`dataDirsAbsent`), and nothing consumes it (until 2026-11-24 a first start's `bootstrap` did, through
`wal.bootRes`): an unused axiom, which a separate change to the start axiom could delete. Nothing else
produces it; a restart reads a closed WAL's files instead (`walFiles`, `storage/WalRecs.lean`). No axiom says it is exclusive (as for
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

/-- **The data directory `dd` is fresh** (axiomatized; see the file header). -/
axiom dataDirFresh {GF : BundledGFunctors} [GooseExts] (dd : GoString) : IProp GF

/-- It is timeless (an abstract fact of the file system, read in one step). -/
axiom dataDirFresh_timeless {GF : BundledGFunctors} [GooseExts] (dd : GoString) :
    Timeless (dataDirFresh (GF := GF) dd)

attribute [instance] dataDirFresh_timeless

end EtcdGrove
end Perennial
