# logkvsnap: logkv with an immutable snapshot, proved by adapting logkv's proof (2026-10-28)

One variant of the scalable-proof experiment (`notes/logkv-eval.md` is the base). The feature
(`diff examples/lintest/logkv/logkv.go examples/lintest/logkvsnap/logkvsnap.go`): the server's
`applied` count and `state` become one pointer `s.snap` to an immutable `snapshot{val, index}`;
`applyLoop` allocates and publishes a new snapshot per entry (`s.snap = &snapshot{log[i], i+1}`),
`Put` waits on `s.snap.index`, and `Get` takes `sn := s.snap` under the lock and reads `sn.val`
**after unlocking**.

## Result

**`logkvsnap_adequate`** (`Proof/github_com/mit_pdos/etcd_grove/examples/lintest/logkvsnap/
Adequacy.lean`), the same statement as `logkv_adequate`: every real execution of
`initialize'(); Main()` of fewer than `2^63` steps never gets stuck and no thread panics. No
`sorry`, no new axiom: the `#print axioms` of `logkvsnap.wp_Main` and `logkvsnap_adequate`
(`Results.lean`) are, after renaming the package, line for line those of logkv's (81 lines of
output each, `diff` empty; no `sorryAx`).

Process: step 1 was a plain copy with `logkv` renamed to `logkvsnap` everywhere (commit
`7f86037d7e`); step 2 the changes below. Wall time: about 40 minutes, most of it finding the
right tactic for three Goose steps (below); no design question came up.

## What changed, and why

Only the lock invariant's description of the physical state, and the four proofs that touch
those fields. **No spec changed** (all eight `Spec/` files are the renamed copies; the public
API never mentioned the fields), so the `spec` skill had nothing to review.

1. **`Defs.lean`: the lock invariant `logkvsnapR`.** `appliedAddr s ↦ a ∗ stateAddr s ↦ st`
   became `∃ p, snapAddr s ↦ p ∗ p ↦□ (⟨st, a⟩ : Snap)`: the abstract applied count `a` and
   state `st` are kept, now as the fields of the current snapshot, which is read-only (`↦□`).
   Everything else (the request list, the slots, the ghost state, `isServer`, `regState`, the
   model) is unchanged. *Feature*: the fields moved. The persistent points-to is the one idea
   the feature needs (next item). 8 lines of code, plus the header.
2. **`Server__Get.lean`.** The linearization point is unchanged (right after `Lock`, the
   atomic update fired against the invariant's half of `γ`, the value `st`), but the value is
   now read after `Unlock`: the proof keeps `#Hp : p ↦□ ⟨st, a⟩` (persistent, so it survives
   giving the lock invariant back) and reads `sn.val` from it (`iStructNamed Hp; wp_auto`).
   *Feature*: this is exactly what "read after unlocking" costs, and it is why the snapshot
   must be read-only in the invariant (a fractional or exclusive points-to would have to go
   back into the invariant at `Unlock`). +4 lines.
3. **`Server__applyLoop.lean`.** The new snapshot is allocated and stored in the body; its
   points-to is made persistent (`ipersist`) and the invariant re-packed with the new pointer.
   *Feature* (publishing a new object). One friction, *tactic*: the body's last step (the store)
   is followed directly by the loop's postcondition, which is not a WP, so there is no update to
   `ipersist` under; the fix is `iapply wp_fupd` before the body's last `wp_apply`, then
   `ipersist «$r0»; imodintro` (the allocation is anonymous inside `wp_auto`, hence the
   hygienic names `«$r0»`/`«$r0_ptr»`; `wp_apply +noauto` + `wp_alloc` did not work because
   the allocation's argument still needs a load first). +6 lines.
4. **`New.lean`.** The initial `&snapshot{}` is a second allocation (`wp_alloc sn; wp_pures`
   before the server's own), made persistent and given to the invariant; `zero_val Snap` is
   rewritten to `⟨"", 0⟩` (`rfl`). *Feature*. +6 lines.
5. **`Server__Put.lean`.** Put's logic is untouched: its loop condition now reads
   `s.snap.index` (`iStructNamed Hp` before `wp_auto`), and its three destructurings and
   re-packings of the invariant gained the pointer (`%p`, `Hsnap`, `#Hp`, `iexists …, p`,
   `iframe #`). *Base choice*, not the feature: Put does nothing new; it changed only because
   the base's invariant lists the physical fields inline, so every `icases`/`iexists` of it
   names them.

The same bookkeeping (pattern and `iexists` edits) is also most of the diff in Get and applyLoop.

### What a different base would have saved

Of the ~35 changed code lines, roughly half are the mechanical re-listing of the invariant's
fields in `icases` patterns and `iexists` (items 2, 3 and 5). A base that put the physical state
behind one predicate, e.g. `ownApplied s a st` (in logkv: `appliedAddr s ↦ a ∗ stateAddr s ↦ st`;
here: `∃ p, snapAddr s ↦ p ∗ p ↦□ ⟨st, a⟩`), with the invariant written over it and three small
lemmas (read `a`, read `st` with the persistent fact the reader keeps, publish a new `(a, st)`),
would have confined the change to `Defs` and those lemmas: `Put` would be unchanged, and
`Get`/`applyLoop`/`New` would change only where the Go code itself changed (read after unlock,
allocate the snapshot). That is the usual "physical representation predicate" layering; logkv did
not need it, and for a 100-line program it would have cost more than it saves here.

## What carried over unchanged

All of `Spec/` (8 files), and in `Proof/`: the model and its lemmas (`Defs.lean` outside the
invariant), the helping protocol (pending/done slots, saved propositions, tickets, the monotone
request list), `Model`, `Server__Apply`, `Check`, `Main`, `Adequacy`, `Results`, and the generated
`Link` (`etc/gen-link.py --lintest-logkvsnap` regenerates it identically: the functions and
callees are the same), `Init` (`etc/gen-init.py <pkg>` identical) and `PkgTable` (the renamed
copy; `etc/gen-init.py --check` reports all 170 generated files up to date, so a plain run would
write nothing for it). Every argument of Put's proof (the request, the done slot, the saved
proposition's `▷ (P' ≡ P)` paid by `Unlock`) is unchanged.

## Changes outside my paths

None needed, none made. (`etc/link-lean-first-lintest-logkvsnap.txt` also needed no change.)

## Numbers

`git diff --stat 7f86037d7e..HEAD -- Spec/.../logkvsnap Proof/.../logkvsnap` (the copy commit
to the proof commit; this note not included):

```
 .../examples/lintest/logkvsnap/Defs.lean           | 23 +++++++++--------
 .../etcd_grove/examples/lintest/logkvsnap/New.lean | 16 ++++++++----
 .../examples/lintest/logkvsnap/Server__Get.lean    | 12 ++++++---
 .../examples/lintest/logkvsnap/Server__Put.lean    | 22 +++++++++-------
 .../lintest/logkvsnap/Server__applyLoop.lean       | 29 ++++++++++++++--------
 5 files changed, 63 insertions(+), 39 deletions(-)
```

Of these, about 20 changed lines are comments (file headers describing the fields); 0 lines of
`Spec/`. Out of 1958 copied lines (Spec 344, Proof 1614), 5 files of 22 changed.
