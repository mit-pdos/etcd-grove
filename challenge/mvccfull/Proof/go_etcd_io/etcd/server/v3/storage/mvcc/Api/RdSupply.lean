/-
**The store handle's readers' supply** (track A, request 3, 2026-11-06; `notes/mvcc-api-invariants.md`,
"M4, track A, request 3"; the reader tokens, 2026-11-06, `notes/decisions.md`, "mvcc's API: the
store's readers as client-held tokens"). Lean-first (no Rocq counterpart). `Api.lean` imports it
non-publicly: its `isMvccPlain` holds a `rdSupply`.

A reader of the store (`storeReaderC`) is its locks' slots (`storeSlots`: a reader slot of each of
`s.mu` and `s.revMu`) and a ticket of the readers' pool (`ownToks γ.tk 1`), the right to borrow one
of the backend's reader slots the pool holds at the current storage. (2026-11-07, `notes/decisions.md`,
"mvcc's reader token carries the store's lock slots") The client's reader token (`ownToks γ.api.rdk
1`, the API's `mvccReaders γ 1`) is the right to a whole reader: the handle's pool (`rdkPool`) holds,
for each token out, its locks' slots (and, of a watchable store, its `s.mu` slot) and its ticket. No
thread token: the store's locks have a reader slot for each token. A client holding all the tokens
knows no read is in flight.

* `rdkPool`: the pool (`rdkPool_init`, `_borrow[L]`, `_giveBack`, `_take`: the census).
* `rdSupply`: a pool whose copies each lend the store's locks' slots and take them back. A plain
  store's pool is of `storeSlots` itself; a watchable store's inner store's is the watchable
  store's pool of `watchSlots` (with the watchable store's `s.mu` slot, kept in the wand), so the two
  handles share one pool.
* `rdSupply_init`: a readers' supply from `n` readers of the store, `n` tokens;
  `rdSupply_watch`: the inner store's supply from the watchable store's pool.
* `rdSupply_lend`: a reader of the store for a token, with its way back (`tokBack`); the slots are
  not timeless (their locks' guards hold invariants), so the borrow costs a later credit
  (`rdSupply_lendL`: under a later instead). `watchReader_lend`: the same of the watchable store's
  pool, a whole `watchReader` (a stream's calls of its store).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnHandle

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The store's locks' slots a reader holds** (a `storeReaderC` without its ticket). -/
def storeSlots (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(sync.ownRWMutex (muAddr s) (muInv s γ) ∗ sync.ownRWMutex (revMuAddr s) (revMuInv s γ))

/-- **The watchable store's slots a reader of it holds** (a `watchReader` without its ticket). -/
def watchSlots (s st : Loc) (γ : WsNames) : IProp GF :=
  iprop(storeSlots st γ.st ∗ sync.ownRWMutex (wsMuAddr s) (watchStoreInv s γ))

/-- The readers' pool's namespace. -/
def rdkPoolN : Namespace := (nroot .@ "mvcc") .@ "rdkPool"

/-- **The readers' pool of the client's reader tokens** (the reader token carries the store's lock
slots, 2026-11-07): for each of the `k` reader tokens out (`ownToks γ.api.rdk`, the API's
`mvccReaders`; the authority here counts them exactly), a copy of `R` (a reader's lock slots) and a
ticket of the store's readers' pool (`ownToks γ.tk`, kept together: timeless). A token is the right
to one copy and one ticket, without a thread token: the store's locks have a reader slot for each
token, so their number is not the threads'. -/
def rdkPool (γ : StoreNames) (R : IProp GF) : IProp GF :=
  inv rdkPoolN iprop(∃ k : Nat, ownTokAuth γ.api.rdk k ∗ ownToks γ.tk k ∗
    [∗list] _x ∈ List.replicate k (), R)

/-- **The store's readers' supply** (see the header). -/
def rdSupply (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ R : IProp GF, rdkPool γ R ∗ □ (R -∗ storeSlots s γ ∗ (storeSlots s γ -∗ R)))

end proof

end mvcc
end EtcdGrove
end Perennial
