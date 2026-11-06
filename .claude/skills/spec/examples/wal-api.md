# The WAL's API: a trust-boundary API designed whole (2026-11-03)

**Kind:** a library outside the translation (etcd's `wal`, behind the server's
`serverstorage.Storage`), whose contract had grown one operation at a time; a client (a stopped
member's restart) needs what the library's files hold, which no piece said.

**Approved by the user** after three review rounds (two `spec-reviewer`s, one `axiom`-skill
refutation with Go tests). The modules: `Proof/go_etcd_io/etcd/server/v3/storage/WalRecs.lean`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/WalApi.lean`; the decision: `notes/decisions.md`,
"The WAL's API".

## First version (candidate 1)

One module with: the records `walRecs w σ` (a ghost variable whose meaning, "what a restart's
`ReadAll` returns", is trusted) and their model (`walSave`, `walSaveSnap`); the contract `isRNWal`
sealed, one law per operation (`Save`, `SaveSnap` as atomic updates of the records, `Sync`,
`Close` giving `walFiles dir id cid σ`, the closed WAL's files); `walFreshAt`/`walReopened`, what
`bootstrap` gives.

## Critiques and what they changed

1. **The axiom review refuted it with a Go test** along a sequence the server issues: a restart at a
   received snapshot named the next WAL file below the snapshot, the purge later removed the file
   with the record, and a later restart failed, though `Close` had given `walFiles σ`. A bug in the
   library (fixed on the goosed fork; a nonissue), invisible until the files' content was a claim.
   Two more sequences the server never issues broke `Close` and `SaveSnap`: premises now exclude
   them (`σ.b ≤ σ.commit`; at the base's index, the base's term). *Lesson:* a token claiming what
   files hold is refuted by sequences of operations, not single calls; attack it with them.
2. **What makes a trusted file claim true includes the environment's other actors**: `Close`
   releases every lock and the server's purge deletes unlocked files, so `walFiles` holds only once
   the purge stopped. A token (`walPurgeRight`) that the purge holds while it runs and `Close` takes.
   Likewise `Release` above the records' base let the purge remove what a restart reads: the records
   carry their base's lower bounds (`walBaseLb`), which `Release` takes.
3. **A pure helper the trust base states must be what Go computes**: `dd ++ "/member/wal"` was false
   of a trailing slash and ignored `DedicatedWALDir`; the directory became opaque
   (`config.walDirOf dataDir dedicated`), as `config.backendPathOf` already was.
4. **A sealed ghost variable whose meaning is trusted needs mechanical sealing**: `@[no_expose]` alone
   lets an `import all` update it; the modules are listed `sealed` in `etc/import-all.txt`.
5. **One predicate per thing, and the laws its clients use**: `walFreshAt`/`walReopened` were one
   predicate (`walOpened` at `walFresh` or `σ`); a directory's state became one ghost variable
   (`walDirFresh` or `walFiles`, exclusive per directory, timeless so it can sit in an invariant);
   persistence, the interface value and the base's laws added for the clients that destructured.
6. **List every trusted statement a change strengthens**, including the one that gives the contract
   (`NewStorage`'s, not `bootstrap`'s as first written): a same-name change is invisible to
   `etc/tcb-report.py --check`.

## The approved spec

`walRecs`, `walBaseLb`, `walDirFresh`, `walFiles`, `walPurgeRight`, `walMetaIs`, `walDirOf`,
`config.walDirOf` and the model in `WalRecs.lean`; `isWalStorage` with `walSave_spec`,
`walSaveSnap_spec`, `walSync_spec`, `walClose_spec`, `isWalStorage_ok`, and `walOpened` in
`WalApi.lean`; six changes to trusted statements outside it (the decision's list), approved together.
