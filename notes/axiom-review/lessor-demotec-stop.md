# The lessor's `demotec` and stop channels (prove-ps2-lease, 2026-11-21)

Retired: `lease.lessor.Demote.wp_proof`, `lease.lessor.Stop.wp_proof`, `lease.lessorStopTok` (and its
`Timeless` instance). Changed claims of the remaining axioms `lease.NewLessor.wp_proof` and
`lease.lessor.Promote.wp_proof` (and `Renew`'s, which only reads): the lessor's invariant now holds
ghost state for `demotec`, and `lessorStopTok` is a definition. Each claim checked against the Go
code (`server/lease/lessor.go` at the etcd pin).

## `lessorStopTok lp` (LessorBackend.lean) (superseded: `stopC` is a close-once channel since prove-ps2-renew, below)

`stopC`, `doneC` read-only (`↦□`), each a broadcast channel (Perennial's `ownBroadcastChan`, `Q = True`):
the token holds `stopC`'s close right (`.Pending`) and `doneC`'s receive side (`.Unknown`).

- `NewLessor` must produce it: `newLessor` makes both with `make(chan struct{})` (`:238-239`), writes
  neither field again (grep: the only other mentions are receives, `:426`, `:632`, `:654`, the close of
  `stopC` in `Stop`, `:616`, and the deferred close of `doneC` in `runLoop`, `:621`). Fresh unbuffered
  channels are idle and owned (`chan.wp_make1`), `alloc_broadcast_chan` turns each into a broadcast
  channel (ghost state only). Nothing is ever sent on either, so the broadcast invariant (no send) holds.
  `runLoop` keeps `doneC`'s close right and `stopC`'s `.Unknown` (its `select`s receive); `Renew` gets
  `stopC`'s `.Unknown` from the lessor (persistent).
- Second `Stop`: refuted by the single `.Pending` (as before: "exclusive by use").
- Not timeless any more (it holds invariants); nothing needed the instance (the full build passes).

## `demotec` (InvLessor.lean: `demoteChanInv`, `demoteOuter`, `demoteTie`)

Each value `Promote` stores is a channel whose state lives in its own invariant (`demoteChanInv γc γt`:
open, or closed with the token `token γt` inside); the token of the current value sits in the lessor's
invariant `demoteOuter γd`, which also holds half of a ghost variable `γd` (the readers' names'
seventh, `γr.2.2.2.2.2.2`) at the field's value; `le.mu`'s guard holds the other half (fractionally,
`demoteTie`, inside `lessorExtra`, whose signature gained the lessor's `γl` to reach the pin).

- `NewLessor`: `demotec` is not in `newLessor`'s literal (`:225-242`), so nil: allocate `γd` at `nil`,
  `demoteOuter` at its `nil` disjunct. Ghost only.
- `Promote` (`:484`, under the write lock): a fresh channel (idle, owned), a fresh token and its
  `demoteChanInv`; around the store (atomic) open `demoteOuter`, set the variable (both halves held) to
  the new channel and put its token in. An old channel's token (two `Promote`s with no `Demote` between them; the claim
  does not depend on whether the server ever does that) is simply dropped: that channel is never
  closed, which can only leave a receiver of it blocked.
- `Renew` (`:404`, read lock): reads `demotec`; with the lock's share of the variable it opens
  `demoteOuter` and copies the persistent `demoteRecv` (isChan and the channel's invariant) out, then
  receives on it after releasing the lock, through `demoteChanInv` (a receive steps the channel's state
  inside the invariant; a closed channel stays closed). Its spec is unchanged.
- `Demote` (proved): under the write lock it holds the whole variable; it opens `demoteOuter` (a later
  credit strips the invariant's later), takes the token, sets the variable to `nil` there, closes
  (`closeAu` opens `demoteChanInv`: idle -> closed with the token in; closed is refuted by the two
  tokens), then stores `nil`.

Why a ghost variable and not the field's points-to: between the close and the store of `nil` the field
still holds the closed channel, so the invariant must tell "closed, being cleared by the lock's holder"
from "open"; only state the lock's guard shares (the variable) can, at fractional ownership.
Why not Perennial's `ownBroadcastChan` for `demotec`: it is stated at `HasLC.hasLC`, the lessor's
invariant at any `hlc`.

## prove-ps2-renew (2026-11-21): `Renew` proved; `stopC` and `revokec` close-once channels

Retired: `lease.lessor.Renew.wp_proof` (translated with its body, and `Lease.expired`). Its `select`
receives on a lease's `revokec`, on `demotec` and on `stopC`, which needs each channel's state reachable
by any receiver, at any `hlc` (the lessor's invariant is stated at any `hlc`, `ownBroadcastChan` only at
`HasLC.hasLC`). The `demotec` invariant's channel predicates are now shared, renamed: `onceChanInv`,
`onceRecv` (namespace `onceChanN`); `wp_once_close`, `once_recvAu` and `demote_recv` in `LessorLemmas`.

- `stopC` (`lessorStopTok`, `LessorBackend.lean`): a close-once channel, its token in `lessorStopTok`
  (was: a broadcast channel's `.Pending`); its receive side `lessorStopRecv lp` (persistent: `stopC ↦□ c`
  and `onceRecv c γt`) is a new conjunct of `lessorExtra` (under `le.mu`, though read-only: `Renew` holds
  only `lessorInv`). `doneC` stays a broadcast channel. `Stop` (proved) closes with `wp_once_close`.
  `NewLessor` (axiom) must now produce both: one fresh channel (`make(chan struct{})`, `lessor.go:238`),
  one invariant (`inv_alloc`, ghost only) whose persistent `onceRecv` goes into the lock's guard and the
  token into `lessorStopTok`; the two existentials are witnessed by the same names. `runLoop` (in
  `NewLessor`'s claim) receives on `stopC` through `lessorStopRecv`.
- `revokec` (`revokeCloser`, `leaseMeta`): `revokeCloser c` is now a close-once channel and its token
  (was: `isChan` and the channel's whole `ownChan .Idle`); `leaseMeta`'s `revokec` conjunct gains the
  persistent `revokeRecv c`. Both proved: `NewLease` and `initAndRecover` allocate the invariant at the
  `make`, `Grant` and `recover_one` copy the receive side into `leaseMeta` (`revokeCloser_recv`),
  `Revoke`'s deferred close is `wp_once_close`. No axiom states either.
- `leaseInit` (`Base.lean`) gains `leaseRenewed`'s `counterSpec`, grouped with `leaseRevoked`'s (so the
  clients' positional patterns are unchanged); its initializer is translated and proved
  (`etc/gen-init.py`), no axiom.

## prove-ps2-promote (2026-11-21): `Promote` proved

Retired: `lease.lessor.Promote.wp_proof` (translated with its body). The `demotec` claim above is now a proof:
`chan.wp_make1`, `token_alloc` and `inv_alloc` of `onceChanInv` at `.Idle`, and `promote_swap` (open `demoteOuter`
with a later credit, set the ghost variable's two halves to the new channel, put its token in, drop the old
channel's). The rest of the body: every lease refreshed, registered with the notifier and its checkpoint scheduled
(`leaseMeta`); with `leaseRevokeRate` or more leases, the sort (`sorter_byExpiry`, moved to `SortByExpiry.lean`) and
`Remaining()` of each sorted lease, which take the level-0 token and the two bounds the spec now has (ledger
2026-11-21); the float arithmetic steps by Perennial's uninterpreted `FloatOps`, the float-to-`Duration` conversion to
any value (`wp_ArbitraryInt`).
