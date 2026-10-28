# logkv: a log-applied register, proved end to end (2026-10-28, branch `logkv-eval`)

The base of the scalable-proof experiment: `examples/lintest/logkv/logkv.go`, a register whose
writes go through a lock-protected log that an apply goroutine applies, readers reading the
applied state, checked by the generic `lintest` driver. Proved end to end: **`logkv_adequate`**
(`Proof/github_com/mit_pdos/etcd_grove/examples/lintest/logkv/Adequacy.lean`): every real
execution of `initialize'(); Main()` of fewer than `2^63` steps never gets stuck and no thread
panics, so porcupine answered `Ok`. Its `#print axioms` (in `Results.lean`) is exactly
`counter_adequate`'s: 53 entries, the same list (the Go-semantics trust boundary of `fmt`, `os`,
`strings`, `sync`, `internal/synctest`, `initLb_of_spec`, and Lean's three), no `sorryAx`, no
new axiom. The linked `logkv.wp_Main` (`Link.lean`) rests on the same list.

(The variants `logkvcompact`, `logkvsnap`, `logkvrw`, `logkvappend` and their translations were
not read.)

## The specs

The API is the one a register under a mutex would have; nothing in it mentions the log, the
apply goroutine or where the linearization point is.

- **Vocabulary** (`Defs.lean`): `regState γ v` (the register's abstract state, `γ : GName`,
  timeless) and `isServer γ s` (persistent). The porcupine model `regS` (`regM`, states
  `GoString`, initially `""`): a write `Op{true, v}` goes to `v` whatever its output, a read
  must output the state (`regStep_put`, `regStep_get`); `regInOk`: the inputs are boxed `Op`s;
  `ioOk`: the input is a boxed `Op`, and a read's output a boxed `string` (what `Step`'s
  `input.(Op)` and `output.(string)` need).
- **`Server.Put`**: `{{ isPkgInit ∗ isServer γ s }} <<{ ∀∀ x, regState γ x }>> s.Put(v) @@ ∅
  <<{ regState γ v }>> {{ RET #(); True }}`. Logically atomic with mask `∅`: the
  implementation reserves no invariant namespace (all its state is under the mutex).
- **`Server.Get`**: the same shape, `<<{ regState γ x }>> {{ RET #x; True }}`.
- **`Server.Apply`**: `applySpec regS regInOk (regState γ) ∅ s.Apply`, the driver's contract,
  as the counter's.
- **`New`**: `{{ isPkgInit }} New() {{ s, ∃ γ, isServer γ s ∗ regState γ "" }}`.
- **`Server.applyLoop`** (internal, only `New` calls it): `{{ isServer γ s }} {{ RET #(); False }}`
  (it never returns; it needs nothing exclusive: two apply loops would also be safe).
- **`Model`, `Check`, `Main`**: the counter's, word for word with `regS`.

## The proof: helping through the lock invariant

The linearization point of `Put` is in the apply goroutine, so the writer's atomic update has to
travel there and its result has to come back. The lock invariant `logkvR γ γr s` holds:

- the log slice, `applied`, `state` (its points-to), and the other half of the register's ghost
  variable (`γ`) at `state`;
- the requests `rs : List (GoString × GName × GName)` (value, saved-postcondition name, ticket
  name) in a monotone list `γr` (authoritative here; a writer keeps `monoListIdxOwn γr i r`), with
  `rs.map fst` the log's contents and `applied ≤ |rs|`;
- `[∗list] r ∈ rs.drop applied, pendSlot γ r`: `∃ P, savedPropOwn r.γP □ P ∗ regAu γ r.v P`,
  where `regAu γ v P := |={⊤,∅}=> ∃ x, regState γ x ∗ (regState γ v -∗ |={∅,⊤}=> P)` is the
  writer's atomic update as Perennial's `<<{ }>>` gives it (a plain fancy update, no `AU`
  fixpoint);
- `[∗list] r ∈ rs.take applied, doneSlot r`: `∃ P, savedPropOwn r.γP □ P ∗ (P ∨ token r.γt)`.

`Put` appends its value, saves `P := True -∗ Φ #()` under a fresh name, keeps a fresh ticket, and
puts its update in a pending slot at the end. `applyLoop`, applying entry `applied`, fires the
head pending slot's update (the lock invariant's half of `γ` agrees with the update's, both go
to the entry's value: the linearization point) and moves the slot, now holding `P`, to the end
of the done list. `Put`, woken with `applied > i`, looks its request up (`mono_list_auth_idx_lookup`),
takes `P'` out of its done slot, leaving its ticket (the other disjunct would be a second
ticket), and gets `▷ (P' ≡ P)` from the saved propositions; the later goes with `Unlock`'s
step, so no later credit is needed. The mask `∅` comes for free: the update is fired under the
mutex, not in an invariant.

`Check`'s generator reads `vals[id%4]` from a captured slice, made read-only (`↦□`, `↦*□`) so the
generator's spec stays persistent.

## What was hard

Less than expected: the whole proof took one sitting, and the only real design question was the
one above, how the writer gets its result back. The options weighed:

- an invariant per request (`inv N (AU ∨ P ∗ … ∨ ticket)`), which would have put a namespace in
  `Put`'s mask (`@@ ↑logkvN` instead of `∅`), visible to every client;
- the update fired by the writer itself once applied: wrong, a later write or a read may already
  have seen the value;
- saved propositions keyed by a ghost index (chosen): the mask stays `∅`, the cost is one
  `▷ (P' ≡ P)`, which `Unlock`'s step pays. The precedent is the kv example's `opSlot`
  (`examples/kv/Defs.lean`, `savedPredOwn` + `token`).

Splitting the requests into a done prefix and a pending suffix (`take`/`drop` at `applied`)
instead of one big-sep with a case on `j < applied` kept every step local: applying is a
`cons`-off / `snoc`-on, appending a `snoc`, collecting a `bigSepL_lookup_acc` on the prefix.

Small frictions: `word` does not handle Go's signed remainder (`BitVec.srem`): `id % 4 ∈ [0, 4)`
for `id ≥ 0` is proved by hand (`srem4_bounds`, `BitVec.toInt_srem`, `Int.tmod_eq_emod_of_nonneg`).
`wp_apply` of a load ran `wp_auto` to the end of the loop body, past where the atomic update had
to be fired; firing it before the load fixed it. `Mutex.Unlock`'s `▷ R` premise is not closed
automatically after the critical section (`inext; iexact HR`).

## Revisions

Every spec or invariant changed after it was first written, and why:

1. **`lintest.genSpec` (outside the package)**: its precondition was `True`, for every `id`. Found
   while proving `Check`: logkv's generator indexes `vals[id%4]`, and Go's `%` is negative for a
   negative `id`, so it panics there and cannot meet the old spec. `Run` only calls `gen` with
   client indices `0, ..., clients - 1`, and `runClient.spec` already has `0 ≤ id`. Changed to
   `{{ ⌜0 ≤ sint.Z id⌝ }}` (`Proof/.../lintest/Defs.lean`); `runClient`'s proof gained one line.
   `Run.spec` is strictly stronger (a weaker premise); the other generators' proofs (counter, kv,
   kvwitness, linkvtxn, k8setcd3) are unchanged (they drop the premise, `_`). The `Gen.spec`s of
   linkvtxn and k8setcd3 are stated as `genSpec`, so they now say less than their Go code
   guarantees (any `id`); their only caller is `Run`. Not a Go bug (`Run` never passes a negative
   `id`), so nothing in `issues/`.
2. **`Names` → `GName`** (from the spec reviewer): the first version had `γ : Names` (`st`, `req`)
   in every public spec, exposing the log's ghost list. Now the API takes the register's name
   only and `isServer γ s := ∃ γr c, …` hides the requests' name.
3. **`regS.ioOk`** (from the spec reviewer): it required every output to be a boxed `string`,
   but `Step` asserts `output.(string)` only for reads. Weakened to `b = false → ∃ x, o = boxS x`,
   which makes `Model.spec` stronger (it accepts any output for a write) and `Apply`'s obligation
   weaker.

No invariant had to be revised: the lock invariant above is the first one written.

Known margins, not changed: `isServer`'s body (the lock invariant, the slots) is not sealed
(`@[no_expose]`; lintest has no package API file, `etc/api/`); `putVal` uses `Classical.choose`,
so the model is not computable (a tester could not evaluate it).

## Perennial

No limitation blocked the proof, and nothing in Perennial was changed. Perennial's logically
atomic triples being a one-shot fancy update (`ProgramLogic/AtomicFupd.lean`, no abort) made
storing a writer's update in a lock invariant direct. The `word` gap on `BitVec.srem` is the only
missing piece met (worked around above).

## Size

| File | Spec/ lines | Proof/ lines |
|---|---:|---:|
| `Defs` (model, vocabulary, lock invariant) | | 286 |
| `Model` | 40 | 119 |
| `New` | 39 | 82 |
| `Server__applyLoop` | 41 | 137 |
| `Server__Put` | 44 | 163 |
| `Server__Get` | 42 | 73 |
| `Server__Apply` | 42 | 105 |
| `Check` | 51 | 103 |
| `Main` | 45 | 62 |
| `Results` | | 26 |
| `Adequacy` (from counter's) | | 160 |
| `Link` (generated) | | 87 |
| `Init`, `PkgTable` (generated) | | 76 + 135 |
| **Total** | **344** | **1614** (1316 hand-written) |

Against the counter (a mutex-protected counter on the same driver): Spec/ 218 lines, Proof/ 1107.
The difference is `Defs` (+109), `applyLoop` (new, 137), `Put` (163) and the split of `Apply`
into `Put`/`Get`/`Apply`. Outside the package: `lintest/Defs.lean` (`genSpec`, 4 lines),
`lintest/runClient.lean` (1 line), `etc/gen-init.py` (the program's table), `etc/gen-link.py`
(`--lintest-logkv`) and `etc/link-lean-first-lintest-logkv.txt`.
