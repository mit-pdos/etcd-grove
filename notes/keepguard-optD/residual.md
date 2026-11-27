# Keep guard replacement (D): the accepted residual (2026-11-27)

The fork's boot step (`catchUpWithBackend`, fork `keepfix-d-crashpin/2026-11-27` @01b0497d0) labels raft's
start snapshot with the backend's stored `(consistent_index, term)` pair. The fixed binary saves that pair
under one mutex (`pairMu`), so every pair it writes is a committed entry's. A backend written by a **pre-fix**
binary can hold a torn pair: the index with the previous entry's term, at a term boundary. Upstream reproduces
this: `nonissues/etcd-cindex-torn-index-term.md`.

**The effect.** Suppose a member crashed on the pre-fix binary with its backend ahead of the WAL's commit at
such a boundary, and then restarts on the fixed binary. Branch B (the WAL lacks the entry at `ci` with the
stored term) then:

- drops the WAL's entries above `ci`, which may have been acknowledged;
- rebases raft at `(ci, wrong term)`, which leaves the member looping on the leader's rejected appends;
- if a valid snapshot record at `ci` with the true term exists, makes the WAL read fail
  (`ErrSnapshotMismatch`), which is `Fatal`.

The review's test is `zz_review_torn_test.go`, under `plans/review-keepfix-d-trusted.md` §6. A rolling
upgrade can also carry a pre-fix leader's pair in a `.snap.db`.

**Why it is residual.** The proof's model runs only the fixed binary, so no modelled execution writes a torn
pair. Upamanyu approved recording this rather than gating branch B on a marker meta key (2026-11-27, the
keepfix-d packet, decision 3). Design: `~/coordinator-notes/plans/keepfix-d-design.md`, "Residual risks".

**A related correction (2026-11-27, approved).** The old `bootOk`/`bootOkR` `"Hthr"` row claimed the consistent
index is 0 after `bootstrap` (`applyThread γA ⟨W64 0, …⟩`). That was false of Go after a restart:
`bootstrap.go:316/324` (`SetBackend`, then the eager `ConsistentIndex()` in the log call) and `:537/:542` at 251a430ce
load the stored index. Corrected to `⟨γA.m0.1, γA.m0.1, W64 0, false⟩` (ledger, 2026-11-27).
