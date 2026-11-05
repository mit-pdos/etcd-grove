# A one-shot `Close` on a constructor's error paths (R-D, 2026-11-04)

`bootOk`, the trusted post of etcd's untranslated `bootstrap`, carried
`"#Hclose" ∷ □ {{ True }} b.Close() {{ True }}` for the deferred `b.Close()` on `NewServer`'s error
paths after `bootstrap`. It is false: `Close` reaches `backend.Close`, whose `close(b.stopc)` panics
on a second call. The honest triple takes the backend's whole open token (`bOpen γ 1`, exclusive),
and on the second error path (`Transport.Start` failing, after `mvcc.New`) that token is spread
over the store's ~8·10⁸ readers, its two loops, its compaction job and, with auth on, the auth
store. Three fresh spec-reviewer rounds over a scratch candidate; the user split the stage and
approved R-D1 (`notes/decisions.md`, "R-D1: the one-shot Close").

## The first version (candidate 1)

- `bootstrappedServer.Close.spec` (and the two inner `Close`s), translated: the record's read-only
  path to the backend, `isBackend`, `isStopChans`, `bOpen γ 1`; post `True`. `#Hclose` deleted.
- `store.Close` returns `compactJobResM`; `watchableStore.Close` returns the two loops' readers,
  deposited in the wait group at `Done`.
- Auth on, path 2: a trusted "abandon" clause in the auth realization: "with the write token, the
  publication token and every copy of the store's reader resource `RD` (all of `authRdSupply RD`),
  `K` back". Alternatives: (b) auth on implies `Start` cannot fail.

## The critiques, and what each changed

1. **Round 1.** The abandon clause is false or unstatable. `authRdSupply` is `authRdN - 1` copies,
   while the realization mints `authRdN` (the proof drops one at `NewAuthStore`), so a holder of the
   last copy could read after `backend.Close`. The trusted lifecycle `authBkLife` has no `R`, and
   `RD` is opaque to `NewServer`. Withdrawn; its sound form, over all `authRdN`, was kept as a
   fallback only. (b) is false: `Start` re-reads the TLS files (I/O errors, descriptor exhaustion).
   It was narrowed to "auth on implies the zero `TLSInfo`", which adds trust (two axioms
   strengthened). New option (d): move the auth store's currency out of `beMu`'s resource into a
   proved invariant keyed by tickets. No trusted change, so recommended. Also: the wait group's
   invariant cannot be allocated at count 0 (allocate after `Add(2)`, the deposits counted apart),
   and the leak on the error paths was to be recorded as a nonissue.
2. **Round 2.** (d)'s clause concluded `authKitIn M d`, which cannot be proved: the auth slots stay
   with the realization for good. It now concludes `authOpenM M d` (the open share alone). The
   currency's counter was backwards (it counts tickets out, not in). The fractions of the backend
   names summed to `1 + ε`; they were split again. The ticket count is now fixed by the
   construction, not by a burn law. The ticket sits inside `beRd`, so `authRd`'s ~10 positional
   unfolds stay. The Go test measured the leak: three goroutines, and a garbage-collector-dependent
   retry.
3. **Round 3.** Path 2 needs a law to join the shares: `authOpenM_join : bOpen (srvOpenQ M) ∗
   authOpenM M d ⊢ bOpen ½`. The wait group's invariant is no longer timeless, so every opener keeps
   its payload under `▷`. The `sorry`'s place is `authSrvTP_on`, and the baselines are named. The
   order of (d)'s steps under an open invariant was fixed. The nonissue gained the locked `0.tmp`:
   a retry that succeeds hangs at its first segment cut.
4. **The user**: split. R-D1 is R2, with readers by (b) and the loops' count named (`wsLoopN`).
   `authAbandonM` is a new conjunct of `authStoreKit`'s post, proved for auth off and `sorry` for
   auth on. R-D2 is (d). The user approved `authAbandonM`, and the ticket inside `beRd`.

## The approved spec (R-D1)

- `bootstrappedServer.Close.spec`, `bootstrappedStorage.Close.spec`, `bootstrappedBackend.Close.spec`:
  as candidate 1, over the proved `backend.backend.Close.spec`; `#Hclose` gone from `bootOk` and
  `bootOkR`.
- `store.Close`'s post `compactJobResM γ.kb`. `watchableStore.Close`'s post is the
  `[∗list] replicate mvcc.wsLoopN storeReader st γ.st ∗ compactJobResM γ.st.kb`. The loops' specs
  end at `wsDone s st γ.st`, which takes the loop's reader.
- `authStoreKit`'s post gains `authAbandonM M stl d RD := □ ∀ st, authRdSupply RD -∗
  authApplyResPre M stl st d RD ={⊤}=∗ authOpenM M d` (`authOpenM`: `authOpenQ` on, `True` off),
  and `authOpenM_join` goes beside `authKitIn_take`.
- Laws: `storeReaders_retire` (bulk, one credit), `storeRTs_shares`, `watchReader_storeReader`.

**Principles shown**: a persistent triple for a closer is false when the closed thing panics on a
second close: the triple takes the exclusive token ("A once-only resource is not spent per call").
A closer that waits for goroutines gives back what they held ("A closer gives back what the
goroutines it waits for held"). A clause a client applies is stated over what the client holds
there: counts that match the producer's, names it sees, and a conclusion the producer can give
("A clause is stated over what its user holds"). A narrowing premise ("`Start` cannot fail") is
checked against every re-read the code does. When a proved option needs no trusted change, prefer
it to a trusted clause, and split the stage with a named `sorry` if the user wants the rest landed
first.
