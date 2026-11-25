/- Lean-first (no Rocq counterpart).

# C-I2, C-I3: `bootstrap` after a crash (interim axioms' statements, etcd-dist D6)

`notes/etcd-dist-d6.md`, "Crash interim axioms". **Statements, not yet axioms** (`abbrev <name>.law :
Prop`, used by nothing): two laws on `bootstrap` (names-only in
the translation: its behavior is what its contracts say), retired by #34's proof of `bootstrap`
(`Proof/.../etcdserver/bootstrap.lean`, `BootParts.lean`) extended to the restart branch (T9) and to a
first start's leftovers (T3). No proof uses them yet: `NewServer.specC`'s proof (T4) takes
`bootstrapCrashContract`, the member's first start (T7) `bootstrapLeftContract`.

**Both are about the fork with the torn-`Save` fix** (`upamanyus/etcd` branch
`goose-lean-fmtattrs-tornsave`, `768ecf158` on the pin `bc2b5f4d0`; `notes/etcd-dist-d6.md` §10, branch
`etcd-safe-walfix/2026-11-24`): `WAL.Save` with entries always ends with a state record, `ReadAll` drops
the trailing run of entry records (an unfinished `Save`), and `bootstrap` first calls
`wal.DiscardUnsaved`, which renames a WAL that holds no state record, no snapshot record above index 0
and no entry record followed by another record (it reads as `walFresh`) to the temporary directory
`Create` removes, so that `bootstrap` takes the first-start branch. At the current pin (`bc2b5f4d0`,
`etc/goose.py`'s project `etcd`) neither axiom is true: there `ReadAll` keeps a torn `Save`'s entries
(`issues/raft-commit-lost-with-entries-kept.md`) and an unsaved WAL is restarted with `RestartNode` on
an empty log. **They are false of the pinned code, so they are not axioms** (review 2026-11-24): each
becomes `axiom <name>_holds : <name>.law` when the pin moves to the fix (the fix's phase P0), after the
restrictions its review asks for.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCrashImage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.storage.WalAreaFresh

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- (C-I3) **The WAL area whose WAL directory is `dir`, holding an unsaved WAL**: `walAreaFresh`'s area
facts and resources with half of the root's call permission, and in place of no WAL (`walAbsent`) the
files of a closed WAL whose records read as `walFresh` (`walFiles`, any member and cluster in its
metadata; its files hold the other half of the call permission and the generation's lock token). Under
the fork's fix such a WAL is what `wal.Create` left, possibly with an unfinished first `Save` (entry
records and no state record), which `ReadAll` drops. **Wider than `wal.Unsaved`** (review 2026-11-24):
`walRead` drops snapshot records above the saved commit, so a history of one `SaveSnapshot` above index 0
also reads as `walFresh`, and `Unsaved` is false of it (Go then restarts). No producer of `walFiles` makes
such a history today (`walRecs_closeAU` needs the unfiltered fold), but a crash-side producer could: the
predicate is to be restated over the history (every operation a no-op `Save`, later the trailing entry
run of a torn first `Save`) before the law becomes an axiom. -/
def walAreaUnsaved (dir : GoString) : IProp GF :=
  iprop(∃ a : WalA GF, ⌜a.dir = dir ∧ WalFs.InArea a.r a.dir go!"wal" ∧ cleanAbsPath a.r ∧ a.Sio.path a.dir⌝ ∗
    (letI := a.ext; letI := a.semOk; letI := a.has; letI := a.W
     iprop(WalFs.walAreaOk walCodec walSrvMr a.R a.jr a.r ∗ WalFs.dirDurable a.r ∗
      Fs.osPathS a.R a.r (DFrac.own 1) a.jr ∗ WalFs.walAreaRes a.jr ∗
      Fs.osCallPerm (Fs.callKey a.R a.r) (1 : Qp).half)) ∗
    ∃ (id cid : w64), walFiles a id cid walFresh)

/-- (C-I3) **What a first start's `bootstrap` may find after a crash of an earlier first start**: the
configuration's dedicated WAL directory the member's, the WAL area fresh or holding an unsaved WAL
(`walAreaUnsaved`), and the data directory fresh (`dataDirFresh` and `dataAreaFresh`, as `wal.bootRes`).
The data area's leftovers (the backend file, `member/snap`) are not in it yet: their definition (T3) must
allow committed bucket creation (`CreateMetaBucket`, the stores' buckets) and exclude torn meta pages
(`nonissues/bbolt-init-not-crash-safe.md`) and a backend holding applied entries (review 2026-11-24,
`notes/axiom-review/c-i3-bootstrap-left.md`). `wal.bootRes cfg` is its first case. -/
def wal.bootResLeft (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop(⌜cfg.DedicatedWALDir' = srvWalDirOf cfg.DataDir'⌝ ∗
    (walAreaFresh (srvWalDirOf cfg.DataDir') ∨ walAreaUnsaved (srvWalDirOf cfg.DataDir')) ∗
    dataDirFresh cfg.DataDir' ∗ dataAreaFresh cfg.DataDir')

end defs

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- (C-I3) **`bootstrap`'s contract on a first start's leftovers**: `bootstrapContract` with the WAL's
slot `wal.bootRes cfg` widened to `wal.bootResLeft cfg`; the post unchanged (`bootOk`: a new member over
an empty backend). -/
def bootstrapLeftContract (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (γ : SrvRaft) (id : w64) (ctxs : List (List w8)) (N : Nat) (dir : w64 → List GoString) :
    IProp GF :=
  iprop(□ ({{ ⌜bootCfgOk cfg ∧ bootCfgFresh cfg U ∧ N + 7 + bootWB ≤ backend.wbInit ∧
          storage.dbOpensOk⌝ ∗
        zapLoggerOk cfg.Logger' ∗
        (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
        ⌜EtcdVerifyOff⌝ ∗
        bootCfgRO cfg U ∗ memStorRegAuth (∅ : GMap Loc MemStorNamesRec) ∗
        wal.bootResLeft cfg }}
      (App (Val (@! bootstrap)) (Val #cfg))
    {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
        ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ bootOk cfg γ id ctxs N dir b }}))

/-- (C-I2, the interim axiom's statement) **`bootstrap`'s restart branch on a data directory a crash left**
(`bootstrapCrashContract`, `InvCrashImage.lean`: the graceful restart contract with the backend's index
`i` only above the WAL's base, not below its commit, and the WAL's read facts `walReadFacts σ` the
caller's premise). Why it holds of the fixed fork (see the file header): `bootstrap` reads `haveWAL`
(`wal.Exist`), finds a WAL that is not unsaved (`DiscardUnsaved` keeps it: its records `σ` are those of
complete `Save`s), opens the backend (`bootstrapBackend`: `recoverSnapshot` with `beExist`, the backend's
index `i ≥ σ.b`, so no `.snap.db` is opened), and `bootstrapWALFromSnapshot` opens the WAL at the
snapshot and `ReadAll`s exactly `σ` (the trailing entry run of an unfinished `Save` dropped, the fix's
`readAll`); raft's `RestartNode` on a `MemoryStorage` holding `σ` (I1-I4 by `walReadFacts σ`: raft's
`loadState` does not panic on `σ.commit ≤ σ.last`). A backend ahead of the WAL's commit (`i > σ.commit`,
the apply thread's synced commits beside an unsynced commit-only `Save`) is what `bootOkR` already
covers at `i` (the apply thread skips entries at or below the consistent index). (Review 2026-11-24,
`notes/axiom-review/c-i2-bootstrap-crash.md`: refuted as first stated) Only for the deployment's names:
`γ.vs` the cluster's members `ps` (sorted out by `bootOkR`'s `Hraft`: non-empty, distinct, no `0`, `id`
among them), `γ.boot` their bootstrap log, and `dir` their peer URLs as the bootstrap log's members
record them (`bootOkR`'s `memberDirIs`), as `bootPremiseR` guards the graceful contract; quantified over
every `γ` the law gave `bootOkR`'s `γ.vs = ps` at `γ.vs := []`, i.e. `False` on success. And the contract
now asks `γ.cl.bootLen ≤ σ.commit` (an unsaved WAL beside an applied backend goes to the first-start
branch). Retired by #34's
`bootstrap` proof extended to the restart branch over the fixed `ReadAll` (T9). (P8, 2026-11-25) The
contract's files are `srvFilesC` (the WAL's files without their synced mark, what a crash leaves:
`SrvCrash.lean`); `bootstrap`'s `Open` and `ReadAll` take no synced mark, and write-mode `ReadAll` syncs. -/
abbrev bootstrapCrashContract.law : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (γ : SrvRaft) (id : w64) (N : Nat) (dir : w64 → List GoString) (ps : List w64),
    γ.vs = ps → ps ≠ [] → ps.Nodup → W64 0 ∉ ps → id ∈ ps → srvBootLogOk ps γ.boot →
    (∀ f ∈ ps, ((memBoot γ.boot).lookup f).map apply.MemberM.peerURLs = some (dir f)) →
    ⊢ bootstrapCrashContract (GF := GF) cfg U γ id N dir

/-- (C-I3, the interim axiom's statement) **`bootstrap`'s first-start branch on a first start's leftovers**
(`bootstrapLeftContract`). Why it holds of the fixed fork (see the file header): an unsaved WAL is
renamed away by `DiscardUnsaved` before anything else (one atomic rename to `Create`'s temporary
directory, then the parent's sync), after which `haveWAL` is false, as on a fresh WAL area; a leftover
`wal.tmp` is removed by `Create`. The data area's leftovers are not covered yet (see `wal.bootResLeft`);
a backend holding applied entries beside an unsaved WAL is likely reachable with the fork's fix (raft
hands out the bootstrap batch committed before its `Save`, etcd applies before `Save`, the backend
commits on its timer: code reading, review 2026-11-24, no test yet) and would make the fix's fresh
branch wrong there (T3, and an `issues/` file once a Go test shows it). Retired by #34's `bootstrap` proof over the fixed fork with these leftovers (T3). -/
abbrev bootstrapLeftContract.law : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (γ : SrvRaft) (id : w64) (ctxs : List (List w8)) (N : Nat) (dir : w64 → List GoString),
    ⊢ bootstrapLeftContract (GF := GF) cfg U γ id ctxs N dir

end boot

end EtcdGrove
end Perennial
