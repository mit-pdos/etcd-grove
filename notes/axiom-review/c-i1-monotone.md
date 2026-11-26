# C-I1's crash premise restated in prefix order: `bbolt.BoltCrashWhole`, with `dbCrash`

Review 2026-11-25, `axiom` skill, for the bbolt-crash workstream, on branch `axiom/c-i1-monotone` at
`61436d7e08` (etcd_safe line; parent `4f543c2f7c`). Earlier reviews of C-I1:
[c-i1-bbolt-crash](c-i1-bbolt-crash.md), [c-i1-nopath](c-i1-nopath.md), [c-i1-takeput](c-i1-takeput.md).
bbolt at the fork's `ea5656d` (P13's init fix; `e1fae5c` is the `WriteTo` fix cited below).

## What is reviewed

- `bbolt.BoltCrashWhole I st st'` (`Spec/go_etcd_io/bbolt/CrashPremise.lean`). The setting: a file of `I`
  whose size has not changed since its last sync and with no change in flight past its end, and meta slot
  `j < 2` (bytes `4096j+16 .. 4096j+80`) of the crash image validates. Then the slot's 56 field bytes are as
  of one change `n` (`valAt`), and each of its 8 checksum bytes is as of some change `m ≤ n`.
  - At `4f543c2f7c` the premise had only the first half: 56 field bytes as of one `n`, and nothing about
    the checksum.
- `backend.BoltCrashWhole` now abbreviates it. `backend.dbCrash` takes it as `hQ` for the record's inode.
- The member's crash law instantiates it for every inode: `hA1 : ∀ i0 st st', Q st st' → BoltCrashWhole (· = i0) st st'`
  (`MemberCrash.lean:1107`, `BackendImage.lean:134`).
- `boltCrashWhole_exists`: some crash satisfies it from every reachable state.

## Verdict: **survives** for bbolt's database file (no counterexample); two docstring errors; one scope finding at the member level

- **Sufficiency.** Under the restated premise, a slot that validates after a crash is, byte for byte, its
  durable state or the meta being written. With that, `dbCrash` holds of every image tried, the
  double-crash revival included.
- **Truth on C, for bbolt's file** (corrected 2026-11-26). Not "no tear at all": one `pwrite` can be cut at an
  arbitrary byte even from a page-aligned source (`MADV_COLLAPSE`, measured in the page cache;
  `notes/axiom-review/cstar-independent.md`). A cut inside the field bytes over torn residue can rebuild an older
  meta with no collision (`notes/axiom-review/t1b-options.md`), which the premise excludes. The exclusion holds only
  up to an FNV-64a coincidence once residue cannot survive a reopen (an open decision: option C★, `Open` poisons an invalid slot; pending).
  - The meta lies inside sector 0.
  - A completed `fdatasync` comes between any two writes of a slot, so mechanism B is absent.
- **Two docstring errors.**
  - "The 64-byte form is false on C" is wrong for bbolt's file (item D1).
  - "(B) never reaches a meta slot" is wrong for defrag's temporary database, which the member-level
    instantiation covers (item D2).
- **Scope finding** (predates this change). `hA1`'s `∀ i0` applies the premise to every file of the run.
  - The FNV-64a argument holds only for contents bbolt writes. A client-chosen 64 bytes at a slot offset of an
    etcd WAL segment, torn by mechanism A, can validate in a shape the premise excludes (item S1).
  - The fix narrows the premise, so it is pre-approved as trust-shrinking.

## Why the restated premise is sufficient (the argument the attacks rest on)

For the database inode, while a record exists (after `Open`'s `fdatasync`, fork `db.go:326`, under
`FsNoErrAll`):

1. **At most two candidates per slot byte.** The first is the durable value, at stamp 0. The second is the
   meta being written, at stamp `s`.
   - bbolt writes slot `txid % 2` once per commit, in one aligned 4096-byte `WriteAt` (`tx.go:613`). It then
     `fdatasync`s (`tx.go:621`).
   - The same slot is next written two commits later, after two more syncs (`tx.go:574`, `:621`).
   - `DB.grow`'s truncate is `fsync`ed before the data writes (`db.go:1349-1358`). So at every meta write the
     file meets the premise's size conditions.
   - Nothing else writes pages 0 and 1: page ids from the freelist are `≥ 2`; `WriteTo` writes to its `io.Writer`
     and only reads the db file; the mapping is read-only.
2. **Each written meta is self-consistent.** `Meta.Write` stores `Sum64()` of the fields.
3. **So the premise gives image ∈ {durable D, written W}, by value, without FNV.**
   - If `n < s`, the fields are D's and every checksum byte is as of `m ≤ n < s`, so the image is D.
   - If `n ≥ s`, the fields are W's. A validating checksum equals `FNV(W.fields) = W.checksum`, so the image
     is W. A checksum byte at an older stamp is used only where D's value coincides with W's.
4. **The current slot is never written while current.** Commit `t+1` writes slot `(t+1) % 2`. That slot holds
   the old meta `t-1` or a torn image, never the current meta `t`. Its candidates are therefore singletons.
5. **What `Open` picks** (`db.meta()`: the valid slot with the larger txid):
   - W if whole: data synced at `tx.go:574`, the record's `Dn` once the commit point fires at `PWriteStart`
     (condition of [c-i1-takeput](c-i1-takeput.md));
   - otherwise the current meta, which is `Dl`.
   - A durable non-current slot that validates has txid `< t`. One with a higher txid would have been picked
     at the last `Open` and made current.
   - `fileHoldsM`'s `metaOk` holds of each image: current meta at slot `txid % 2`, the other slot invalid or
     older, zeros at the probes (below).

Induction over generations: the durable state at each boot is the previous crash's image, which by (3) is a
whole bbolt-written meta or an invalid slot. So every generation starts in a state where (1) to (5) apply.

## Attacks tried

1. **The double-crash revival** (the finding that motivated the change; `origin/bbolt-crash-img/2026-11-25`).
   - Crash 1 tears commit `t+1`'s slot. The torn image T1 has the new fields F and a checksum mixing old and
     new bytes, so it is invalid and becomes stamp 0.
   - Generation 2 rewrites that slot with `t+1'` (W').
   - The revival image is F with checksum bytes taken from W' that complete `C(F)`.
   - Under the new premise this image has its fields as of 0. Its checksum bytes must then be as of 0, which
     gives T1's checksum, which is invalid. The image is **excluded**.
   - It is also not producible on C: an older field byte next to a newer checksum byte needs mechanism B
     (below). The 56-byte form admitted it, so `dbCrash` was false of the model under that form, as the
     motivation says.
2. **Three or more generations.** Each crash leaves the torn slot invalid, or makes it whole W (then current,
   with its data synced).
   - A second tear of the same slot leaves a mix of T1 and W'. That mix is invalid unless FNV collides, and
     the premise excludes the collision because the fields come from two stamps.
   - Generation k+1 again starts with one invalid non-current slot and a synced current slot.
   - A slot can be invalid only while it is the non-current one. A non-current slot is the only kind that gets
     written, and the other slot is written only after this one is whole and synced (attack 3). So at most one
     slot is invalid at any time, and `getPageSize` and `mmap` always find the valid one.
   - **Blocked** by induction (above).
3. **A torn slot rewritten twice.**
   - Within one generation the two writes have a completed `fdatasync` between them. After the first, the
     durable value is W', at stamp 0, and T1 is no longer a candidate.
   - Across generations this is attack 2.
   - Two writes with no sync between them would need a failed `writeMeta` followed by a retry of the same
     txid. Under `FsNoErrAll` (which `onFs` carries into every record law) no file step fails, and etcd's
     `batchTx.commit` calls `Fatal` on a commit error (`batch_tx.go:301-303`). **Blocked.**
4. **A crash inside `init`'s meta write, after P13** (`ea5656d`).
   - `init` writes four pages with zeroed metas and `fdatasync`s. It then writes the two metas and
     `fdatasync`s (`db.go:707-731`).
   - At a crash in the second write the size has been stable since the first sync, so the premise applies.
     A slot that validates is init's whole meta; every other image of each slot is invalid or zero.
   - P13's `needsInit` (`db.go:777-800`): every image of at most four pages whose bytes are zero or init's is
     initialized again, unless it is the whole image. No record exists before `Open` returns
     (`dbCrashKeep_new` needs a live write transaction), so `dbCrash` is not involved.
   - The first commit grows the file past four pages (`grow` to `datasz`, 32 KiB). **Blocked; the premise is not
     needed here.**
5. **`Tx.WriteTo` images** (the snapshot sent to a follower, which a follower installs onto `db`).
   - Before the fork's `e1fae5c` this was a real double-crash hole. `WriteTo` wrote txid `T` to page 0 and
     `T-1` to page 1 for every `T`. With `T` odd:
     - commit `T+1` writes slot 0, which holds the current meta. A tear falls back to `T-1` in slot 1;
     - the next generation's commit `T` then writes slot 1, the only valid slot. A second tear leaves no valid
       meta, so `Open` fails and etcd panics.
     - Both tears are images the premise admits (invalid slots), so the premise cannot block this.
   - The fork writes the current meta at `txid % 2` and the previous txid at the other slot (`tx.go:438-459`),
     as a commit leaves them. Both slots point at one tree, so this is attack 2's starting state.
   - The installed file is `fdatasync`ed by `Open` before its record exists (a new inode, a new
     `dbCrashKeep_new`).
   - **Blocked by the fork's fix.** The fix is load-bearing: the premise does not cover this case, and should
     not.
6. **The probe regions** (`getPageSize`'s reads at offsets 1024 and 2048 of page 0, `db.go:420-450`; offsets
   8192 and up only when page 1 is invalid too).
   - Every write bbolt makes to page 0 leaves the probe bytes zero, so their only candidate is 0:
     - `writeMeta` writes a zeroed page buffer with the header and meta set;
     - `initImage`, and the zero pages of `init`'s first write;
     - `WriteTo`'s zeroed buffer.
   - No crash image, in the model or on C, validates there. `metaOk`'s probe clauses hold.
   - The data pages a double-invalid probe would reach are unreachable: at most one slot is invalid (attack 2).
   - **Blocked by the code**; the premise need not mention the probe regions.
7. **Commit point and size windows.**
   - Inside `DB.grow` the premise's antecedent fails (a size change in flight or not yet synced). The slots'
     candidates are then singletons (attack 3's syncs), so no premise is needed.
   - A crash before the data `fdatasync` leaves the slot unchanged.
   - **No image found.**
8. **Coincidences.** `valAt` compares values. A torn slot whose old checksum bytes coincide with the new ones
   is value-equal to W, and the premise admits it with `m = n`. `Open` then picks W, which is `Dn`.
   **Harmless.**

## Truth on configuration C

- **The numbers check.**
  - `results/S0.txt` logs 2,325,853 writes and `S2.txt` 2,409,382. That is 4,735,235 crash points, of which
    4,734,979 are page-0 writes.
  - Torn pages: S0 has 0. S2 has 7, each "new prefix, cut at the source page boundary (752)", and each one of
    bpftrace's 7 `WB-TORN` writebacks.
  - The docstring's figures are right.
- **`STABLE=1` is a faithful proxy for bbolt's meta writes.**
  - `stable_writes` only makes `write_begin` wait for a folio under writeback (`folio_wait_stable`).
  - A bbolt meta slot is never under writeback when it is written. Its previous write was followed by
    `fdatasync`, which waits for writeback to finish, and nothing dirties the slot in between.
  - After a reboot the page is read clean from disk.
  - After a kill (which the model treats as a crash) the next `Open` `fdatasync`s before any commit
    (`db.go:326`), and that sync waits for any writeback the killed process left.
  - So on C (`STABLE=0`) the slot behaves as under `STABLE=1`. During the copy the folio is locked (writeback
    cannot take it), except in A's short-copy window.
- **Stronger than the docstring needs.**
  - `writeMeta`'s buffer is `make([]byte, 4096)`, Go's 4096-byte size class: two objects per 8 KiB span, so
    4096-aligned. The whole page comes from one source page, and A has no boundary to cut at.
  - The aligned control `S0` shows no tear in 2.3 M crash points.
  - The 64 meta bytes are page bytes 16-80, inside sector 0, so a device tearing at sector granularity
    cannot split them.
  - So on C a bbolt meta slot after a crash is its old or its new value. The premise's allowance for prefix
    tears is conservative, which is harmless.
- **Two unsynced writes of a meta page.** None in the database while a record exists:
  - `WriteTo` writes elsewhere;
  - `Open`'s `fdatasync` is a sync, not a write;
  - `init`'s two writes of pages 0 and 1 have a sync between them;
  - the retry case is attack 3.
  - The one bbolt file where mechanism B does reach meta slots is defrag's temporary database. It is opened
    with `NoSync` (`backend.go:531`), commits many times with no sync, and is `Sync`ed only before its rename
    (`backend.go:575-589`). The database's record never covers it: the new `Open` syncs before
    `dbCrashKeep_new`. But the member-level `∀ i0` covers it at crashes during defrag (item D2).
    - A B mix of two consecutive bbolt metas that validates is value-equal to one of them, except by an
      FNV-64a collision of non-adversarial fields. So the premise holds there up to its stated probabilistic
      part.

## Satisfiability

`boltCrashWhole_exists` proves, for every `I`, that the crash `Tests.durCrash` satisfies the premise. That
crash keeps every byte at its stamp-0 candidate. The proof's `key` gives `valAt … 0` for all 64 bytes, so both
conjuncts hold with `n = m = 0`. The crash depends on neither `I` nor `i0`, so the member-level `∀ i0` is
satisfied by one crash.

Built on the VM: `vmlake -j 32 build Spec.go_etcd_io.bbolt.CrashPremise
Proof.go_etcd_io.etcd.server.v3.storage.backend.CrashInterim`: exit 0, 2998 jobs, 639 s, only the existing
warnings (`dif_pos` deprecated, `gooseInvGS` semireducible).

Not checked: whether `durCrash` also satisfies `W1` (the joint premise of `memberGen_crash_law_holds`).

## Required docstring fixes

- **D1: "Why not stronger" is wrong for bbolt's file.** Today it says: "the 64-byte form is false on C: a
  prefix cut inside the checksum plus a one-byte coincidence validates a slot of two changes".
  - The coincidence makes each torn checksum byte equal to W's. `valAt` is a value, so the image is "all 64
    bytes as of `s`" and satisfies the 64-byte form.
  - For bbolt-written slots the two forms are equivalent on validating images (the sufficiency argument,
    step 3).
  - They differ only for a slot whose state at some change is not a self-consistent meta, as in a non-bbolt
    file: in item S1 an A tear inside the checksum of a client-chosen payload validates under the monotone
    form but not the 64-byte one.
  - Suggested wording: the prefix-ordered form is what mechanism A gives for any contents, with FNV-64a
    needed only for a cut inside the fields. The 64-byte form needs, in addition, that every change
    writes a self-consistent meta, which holds of bbolt's writes and of no other file.
- **D2: "(B) never reaches a meta slot" holds only for a syncing opening.** Defrag's temporary database is a
  bbolt file that the member-level instantiation covers. There B does reach the slots, and the premise
  holds only up to FNV-64a. Say so, or narrow the instantiation (S1's fix covers both).

## Scope finding (pre-existing, member level)

- **S1: `hA1`'s `∀ i0` applies the premise to every file.**
  - The first C-I1 review restricted `BoltCrashWhole` to the inodes it covers, because "it cannot be read
    over all files without forbidding the WAL's crashes" ([c-i1-bbolt-crash](c-i1-bbolt-crash.md)).
    `dbCrash` takes it for its record's `i0` only. `memberGen_crash_law_holds` and `memberBackend.law`
    quantify it over every inode, which undoes that restriction.
  - The definition's antecedent (size stable since the last sync, no extending change in flight) holds of
    etcd's WAL segments after their first sync: they are preallocated, then synced at the cut.
  - The attack, argued and not built:
    - a client `Put` with a value that covers a fresh segment's page 1 places chosen bytes X at page offsets
      16-80. X starts with the magic and version, has non-zero field bytes after some cut `c`, and has an
      FNV-64a state of 0 after `X[0..c)`. That is a 56-bit condition, found offline by a meet-in-the-middle
      search of about 2^28 steps; FNV-64a is invertible step by step, not a cryptographic hash;
    - the WAL's direct page writes come from the record's heap buffer, which is not page-aligned to the file
      (`ioutil.PageWriter`), so mechanism A can tear the page at a source page boundary;
    - a tear at `c` leaves `X[0..c)` followed by zeros, checksum included. That image validates
      (`FNV = 0`), yet its fields come from two stamps, so the premise excludes it;
    - mechanism B is not available in the WAL: `PageWriter` writes each page once per sync window, and
      hardstate-only `Save`s do not flush.
  - Likelihood: it needs an adversarial client, a rare kernel tear (about 10 per 10^8 writes under
    compaction) at the chosen offset, and an offline FNV search. A run where this happens is one on which
    etcd_safe's theorem says nothing.
  - **Fix (narrows a premise; pre-approved as trust-shrinking):** instantiate `hA1` only for the inode the
    crashed tree names at the backend's path. That is what `memberBackend.law` reads (`V'.now.entry k.J
    "db" = some (.file i0)`) and what `dbCrash` needs. The files ever at that path are bbolt databases:
    the database itself, defrag's renamed temporary database, and the installed `.snap.db`, which is
    `WriteTo`'s output.
  - Alternatively, `Q`'s premise could name the inodes a run's records cover. Either way the docstring's
    FNV argument then covers every file the premise is applied to.

## Not tried

- A Lean counterexample: none in reach. Every attack on bbolt's file is blocked by the premise, by the code
  (probe zeros, `needsInit`, `e1fae5c`) or by `FsNoErrAll`.
- S1 is argued only: no WAL payload was computed and no tear was measured.
- A power-loss measurement of bbolt's own meta writes on C. The argument for them rests on S0 (aligned
  buffers, no tear) and on the sync discipline.
- `W1` and `BoltCrashWhole` together, for one `Q`.
- `fileRcpt`'s receipt across generations, still open from review 3.
