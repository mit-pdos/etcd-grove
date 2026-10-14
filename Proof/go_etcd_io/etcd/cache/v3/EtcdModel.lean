/-
**The client's model of etcd** (Lean-first, no Rocq counterpart): what etcd's clients (the cache,
`client/v3/concurrency`, `client/v3/leasing`, `client/v3/experimental/recipes`) know of etcd itself,
as a class whose fields are the server-side facts and their laws. See `decisions.md`, "the etcd
model" (the cache's entries) and "The client's model as a class the server instantiates; the wire as
the handler's theorem transported" (2026-10-13, the vertical slice's unit V1).

Until V1 these were fourteen axioms (`InvEtcd.lean`, `InvEtcdTxn.lean`): four opaque predicates and
their laws. They are now the fields of `EtcdModel GF`, which every client package takes as a section
variable (`[EM : EtcdModel GF]`), and the server instantiates it
(`v3rpc/ClientModel.lean`, `etcdModelOfServer`): each predicate defined from the server's certified
log (`idxCert`), each law a theorem. So the clients' results, stated over any `EtcdModel GF`, are
statements about the verified server once applied to its instance.

* `etcdState rev pfx s`: etcd's key-value state at revision `rev`, restricted to the keys with prefix
  `pfx`, is `s` (sorted by key); its laws: one state per revision (`etcdState_agree`), and the
  history laws (`etcdState_revs`, `etcdState_create_persist`, `etcdState_modrev_det`,
  `etcdState_modrev_persist`).
* `etcdReachedAt r`: some response from etcd showed revision `r` to exist (timeless).
* `etcdRevToken r`: the revision `r` was made by the holder's commit (exclusive).
* `EtcdStep r0 r1 pfx evs` (an `IProp` since V1, a `Prop` before: the server's step is a fact about
  its certified log, a ghost lower bound): `r0 ≤ r1`; no event under `pfx` strictly between `r0` and
  `r1`; the events under `pfx` at `r1` are exactly `evs`. Persistent and timeless; its laws
  `etcdStep_transfer`, `etcdStep_compose`, `etcdStep_delete_present` take it as a conjunct.

The pure vocabulary they are stated in (`EtcdKv`, `EtcdEv`, `applyEvsState`) is here too.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvBtree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-! ## The pure vocabulary -/

/-- A key-value as etcd stores it (`mvccpb.KeyValue`'s fields). -/
structure EtcdKv where
  key : GoString
  createRev : w64
  modRev : w64
  version : w64
  value : GoString
  lease : w64

/-- An event as etcd stores it (`mvccpb.Event`): its type (`0` put, `1` delete) and its
key-value (for a delete, the key and the revision of the delete). -/
structure EtcdEv where
  typ : w32
  kv : EtcdKv

/-- etcd's order on keys, on key-values. -/
def etcdKvLess (a b : EtcdKv) : Prop := go.GoStringLt a.key b.key

instance etcdKvLess_dec : DecidableRel etcdKvLess := fun a b => go.goStringLt_dec a.key b.key

/-- One event applied to a state (as the store's `applyEv` applies it to a map): a put replaces
or inserts the key-value, a delete removes the key, any other type changes nothing. -/
def applyEvState (s : List EtcdKv) (e : EtcdEv) : List EtcdKv :=
  if e.typ = W32 1 then btDelete etcdKvLess e.kv s
  else if e.typ = W32 0 then btInsert etcdKvLess e.kv s
  else s

/-- Events applied in order. -/
def applyEvsState (s : List EtcdKv) (evs : List EtcdEv) : List EtcdKv :=
  evs.foldl applyEvState s

/-! ## The class -/

/-- **The client's model of etcd** over the ghost state `GF` (see the file header): the four
predicates and their laws. The server's instance is `v3rpc.etcdModelOfServer`. -/
class EtcdModel (GF : BundledGFunctors) where
  /-- etcd's key-value state at revision `rev`, restricted to the keys with prefix `pfx`, is `s`
  (sorted by key). -/
  etcdState : w64 → GoString → List EtcdKv → IProp GF
  /-- etcd has one state per revision. -/
  etcdState_agree : ∀ (rev : w64) (pfx : GoString) (s s' : List EtcdKv),
    etcdState rev pfx s ∗ etcdState rev pfx s' ⊢ ⌜s = s'⌝
  /-- **Revisions are well formed**: a key-value of etcd's state at `r` was created at a positive
  revision, last modified at or after it and at or before `r`, and has a positive version. -/
  etcdState_revs : ∀ (r : w64) (pfx : GoString) (s : List EtcdKv),
    etcdState r pfx s ⊢
      ⌜∀ v ∈ s, 0 < sint.Z v.createRev ∧ sint.Z v.createRev ≤ sint.Z v.modRev ∧
        sint.Z v.modRev ≤ sint.Z r ∧ 0 < sint.Z v.version⌝
  /-- **A key lives from its creation**: a key present at revision `r` with create revision `c`
  is present, with the same create revision, at every revision `a` in `[c, r]`. -/
  etcdState_create_persist : ∀ (r a : w64) (pfx : GoString) (s s' : List EtcdKv),
    etcdState r pfx s ∗ etcdState a pfx s' ⊢
      ⌜∀ v ∈ s, sint.Z v.createRev ≤ sint.Z a → sint.Z a ≤ sint.Z r →
        ∃ v' ∈ s', v'.key = v.key ∧ v'.createRev = v.createRev⌝
  /-- **A key's record is determined by its mod revision**: two states (at any revisions)
  holding the same key with the same mod revision hold the same key-value. -/
  etcdState_modrev_det : ∀ (a b : w64) (pfx : GoString) (s s' : List EtcdKv),
    etcdState a pfx s ∗ etcdState b pfx s' ⊢
      ⌜∀ v ∈ s, ∀ v' ∈ s', v.key = v'.key → v.modRev = v'.modRev → v = v'⌝
  /-- **A key-value lives unchanged from its mod revision while it is present**: a key-value of
  the state at `a` is in the state at every revision `b` in `[modRev, a]`. -/
  etcdState_modrev_persist : ∀ (a b : w64) (pfx : GoString) (s s' : List EtcdKv),
    etcdState a pfx s ∗ etcdState b pfx s' ⊢
      ⌜∀ v ∈ s, sint.Z v.modRev ≤ sint.Z b → sint.Z b ≤ sint.Z a → v ∈ s'⌝
  /-- **etcd has reached revision `r`**: some response from etcd showed revision `r` to exist.
  Knowledge obtained at a point in time (an `IProp`), which is what makes linearizability
  statable (`isEtcdKV`). -/
  etcdReachedAt : w64 → IProp GF
  /-- It carries no resources: it can sit in invariants opened without later credits. -/
  etcdReachedAt_timeless : ∀ (r : w64), Timeless (etcdReachedAt r)
  /-- **The revision `r` was made by the holder's commit**: an exclusive token, which the
  client's contract gives the caller of a commit that wrote (`txnCommitResultTok`, `putResult`). -/
  etcdRevToken : w64 → IProp GF
  /-- Two tokens for one revision: impossible (a revision is one commit's). -/
  etcdRevToken_excl : ∀ (r : w64), etcdRevToken r ∗ etcdRevToken r ⊢ False
  /-- **A step of etcd's history**: `r0 ≤ r1`; no event under the prefix `pfx` has a revision
  strictly between `r0` and `r1`; the events under `pfx` at revision `r1` are exactly `evs`, in
  order. What a watch response tells a watcher whose previous position is `r0`. -/
  EtcdStep : w64 → w64 → GoString → List EtcdEv → IProp GF
  EtcdStep_persistent : ∀ (r0 r1 : w64) (pfx : GoString) (evs : List EtcdEv),
    Persistent (EtcdStep r0 r1 pfx evs)
  EtcdStep_timeless : ∀ (r0 r1 : w64) (pfx : GoString) (evs : List EtcdEv),
    Timeless (EtcdStep r0 r1 pfx evs)
  /-- **Transfer.** etcd's state at `r1` is its state at any `a` with `r0 ≤ a < r1` with the
  events of the step applied. -/
  etcdStep_transfer : ∀ (r0 a r1 : w64) (pfx : GoString) (s : List EtcdKv) (evs : List EtcdEv),
    sint.Z r0 ≤ sint.Z a ∧ sint.Z a < sint.Z r1 →
    EtcdStep r0 r1 pfx evs ∗ etcdState a pfx s ⊢ etcdState r1 pfx (applyEvsState s evs)
  /-- **Composition.** A step with no events followed by a step is a step. -/
  etcdStep_compose : ∀ (a b c : w64) (pfx : GoString) (evs : List EtcdEv),
    EtcdStep a b pfx [] ∗ EtcdStep b c pfx evs ⊢ EtcdStep a c pfx evs
  /-- **A delete removes a present key**: in a step `r0 → r1` with events `cs`, each delete
  event removes a key that is there when it is applied, from etcd's state at any `a` with
  `r0 ≤ a < r1`. -/
  etcdStep_delete_present : ∀ (r0 a r1 : w64) (pfx : GoString) (s : List EtcdKv)
    (cs : List EtcdEv), sint.Z r0 ≤ sint.Z a ∧ sint.Z a < sint.Z r1 →
    EtcdStep r0 r1 pfx cs ∗ etcdState a pfx s ⊢
      ⌜∀ (i : Nat) (c : EtcdEv), cs[i]? = some c → c.typ = W32 1 →
        ∃ v ∈ applyEvsState s (cs.take i), v.key = c.kv.key⌝

export EtcdModel (etcdState etcdState_agree etcdState_revs etcdState_create_persist
  etcdState_modrev_det etcdState_modrev_persist etcdReachedAt etcdReachedAt_timeless etcdRevToken
  etcdRevToken_excl EtcdStep EtcdStep_persistent EtcdStep_timeless etcdStep_transfer
  etcdStep_compose etcdStep_delete_present)

attribute [instance] EtcdModel.etcdReachedAt_timeless EtcdModel.EtcdStep_persistent
  EtcdModel.EtcdStep_timeless

end EtcdGrove
end Perennial
