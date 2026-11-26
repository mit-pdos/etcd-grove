/- Lean-first (no Rocq counterpart).

# C-I1: bbolt's file after a power loss, at the backend's interface (no interim trust left)

The module the member's crash proof (`MemberCrash.lean`) imports for C-I1. It holds no axiom: the crash
record `dbCrashKeep`/`dbCrashHole`, the crash premise `BoltCrashWhole` and the six laws
(`dbCrashKeep_new`, `_take`, `_putSame`, `_putStep`, `_close`, `dbCrash`) are `CrashLaws.lean`'s
definitions and theorems (bbolt's crash proof over the file extension), re-exported here, beside
`boltCrashWhole_exists` (the premise is never vacuous at a crash). What they rest on: `CrashLaws.lean`'s
header (the crash premise `BoltCrashWhole`, `dbOpts`'s producer `storage.OpenBackend`). Reviews of the
statements: `notes/axiom-review/c-i1-bbolt-crash.md`, `c-i1-takeput.md`, `c-i1-nopath.md`,
`c-i1-monotone.md`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.CrashLaws
public import GooseLang.Ext.Fs.Tests

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

/-- **`BoltCrashWhole` is never vacuous at a crash** (`bbolt.boltCrashWhole_exists`). -/
theorem boltCrashWhole_exists (I : Fs.Ino → Prop) {st st' : Fs.OsState} (hok : Fs.Tests.CacheOk st)
    (hc : Fs.MachineCrash st st') : ∃ st'', Fs.OsCrash st st'' ∧ BoltCrashWhole I st st'' :=
  bbolt.boltCrashWhole_exists I hok hc

end backend
end EtcdGrove
end Perennial
