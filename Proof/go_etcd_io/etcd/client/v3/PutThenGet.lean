/-
**A put then a get by the one client: the get returns the put's value** (2026-10-17;
`notes/decisions.md`, D18, the monotone route). Lean-first, no Rocq counterpart.

The end-to-end specs (`client_put_end_to_end`, `client_get_end_to_end`, `Results.lean`) take
persistent atomic updates over the whole abstract state `etcdKV`: a put's update may fire more
than once (a retried or re-proposed put, `issues/etcd-client-retry-put-ctx-error.md`), even after
the put returned. A client that is the only writer does not need to know which firing was "the"
linearization point: every firing of the put of `key ↦ val` leaves `key` at `val`, and nothing
else changes the state, so a monotone flag ("the put has fired") suffices.

* `putGetInv γ γf key val`: the client's invariant holds `etcdKV` (its half; the server's KV
  invariant the other) with the state sorted by key (`σ.kvs`, as every state of a log is) and a
  monotone counter at `γf` (`0`: not fired; `1`: fired) such that, once fired, the state's value
  of `key` is `val`. Only the two updates below are made from it: the client is the only writer.
* `putAu_of_putGetInv`: the put's update, whose result is the flag's lower bound `1`
  (`kvOpStep_putKey`: a put with no options always writes `key ↦ val`).
* `getAu_of_putGetInv`: with the lower bound, a read update whose result is that the state's value
  of `key` is `val`.
* `ClientPutGet.lean`'s `putGetInv_alloc_log` allocates it, and its `client_Put_own` /
  `client_Get_own` are `client_put_end_to_end` and `client_get_end_to_end` at these updates; a get
  after a put that returned `nil` returns, if it returns `nil`, a reply whose first key-value's
  value is `val` (`client_get_value`).

No prophecy is needed: the conclusion is about one key with a single writer. A general client
(concurrent writers, or a result tied to the reply's own linearization point) is the prophecy
route of D18, not done.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvServerKV

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## The put's step, purely -/

section pure
open mvcc

/-- **A put with no options writes its value** (pure): from a state sorted by key, the put of
`key ↦ val` (`kv.Put(ctx, key, val)`'s) gives a sorted state whose value of `key` is `val`. -/
theorem kvOpStep_putKey (key val : GoString) (σ : KVState) (hs : σ.kvs.Pairwise etcdKvLess) :
    (kvOpStep (.put (putKeyOp key val)) σ).kvs.Pairwise etcdKvLess ∧
      (findKey key (kvOpStep (.put (putKeyOp key val)) σ).kvs).map EtcdKv.value = some val := by
  have hk : (kvOpStep (.put (putKeyOp key val)) σ).kvs =
      putKv (W64 ((σ.rev + 1 : Nat) : Int)) key val (W64 0) σ.kvs := by
    simp [kvOpStep, KVState.commit, txn.needsPrev, applyChanges, applyChange, txn.putChangeOf,
      txn.putValOf, txn.putLeaseOf, putKeyOp, txn.putOpOf]
  rw [hk]
  refine ⟨putKv_sorted hs _ key val _, ?_⟩
  obtain ⟨nv, hnv, -, hv⟩ := findKey_putKv_value σ.kvs hs (W64 ((σ.rev + 1 : Nat) : Int)) key val
    (W64 0)
  rw [hnv, ← hv]
  rfl

end pure

/-! ## The client's invariant and its two updates -/

section inv
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- What the invariant keeps of the state: sorted by key, and, once the put has fired (`1 ≤ n`),
`key`'s value `val`. -/
def putGetOk (key val : GoString) (σ : KVState) (n : Nat) : Prop :=
  σ.kvs.Pairwise etcdKvLess ∧ (1 ≤ n → (mvcc.findKey key σ.kvs).map EtcdKv.value = some val)

/-- **The client's invariant for a put of `key ↦ val` and gets of `key`** (see the file header):
`etcdKV` and the put's flag at `γf`. -/
def putGetInv (γ : ReadNames) (γf : GName) (key val : GoString) : IProp GF :=
  -- (D23, 2026-10-20) the server's workload lets the client deposit the put
  iprop(⌜γ.kv.wl.writes (.put (putKeyOp key val))⌝ ∗
    inv kvClientN iprop(∃ (σ : KVState) (n : Nat), etcdKV γ.kv σ ∗ monoNatAuthOwn γf 1 n ∗
      ⌜putGetOk key val σ n⌝))

instance putGetInv_persistent (γ : ReadNames) (γf : GName) (key val : GoString) :
    Persistent (putGetInv (GF := GF) γ γf key val) := by
  unfold putGetInv; infer_instance

/-- **The put's update** (persistent): each firing writes `key ↦ val` and sets the flag; its
result is the flag's lower bound `1`. -/
theorem putAu_of_putGetInv (γ : ReadNames) (γf : GName) (key val : GoString) :
    putGetInv γ γf key val ⊢
      kvOpAu (GF := GF) γ.kv (.put (putKeyOp key val)) (fun _ => monoNatLbOwn γf 1) := by
  have Hm := kvClientN_mask
  iintro #Hinv
  iunfold kvOpAu
  iunfold putGetInv at Hinv
  icases Hinv with ⟨%HW, #Hinv⟩
  isplitr
  · ipureintro; exact HW
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %n, Hσ, Hmn, %Hok⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn] with -
    · inext; iexists σ, n; iframe Hσ Hmn; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro Hσ
    imod Hmask with -
    imod (mono_nat_own_update (GF := GF) (γ := γf) (max n 1) (Nat.le_max_left n 1))
      $$ Hmn with ⟨Hmn, #Hlb⟩
    have Hstep := kvOpStep_putKey key val σ Hok.1
    imod Hclose $$ [Hσ Hmn] with -
    · inext; iexists (kvOpStep (.put (putKeyOp key val)) σ), (max n 1); iframe Hσ Hmn
      ipureintro; exact ⟨Hstep.1, fun _ => Hstep.2⟩
    imodintro
    iintro !>
    iapply monoNatLbOwn_le 1 (Nat.le_max_right n 1) $$ Hlb

/-- **A get's update after the put fired** (persistent): a read update whose result is that the
state's value of `key` is `val`. -/
theorem getAu_of_putGetInv (γ : ReadNames) (γf : GName) (key val : GoString) :
    putGetInv γ γf key val ∗ monoNatLbOwn γf 1 ⊢
      kvReadAu (GF := GF) γ.kv
        (fun σ => iprop(⌜(mvcc.findKey key σ.kvs).map EtcdKv.value = some val⌝)) := by
  have Hm := kvClientN_mask
  iintro ⟨#Hinv, #Hlb⟩
  iunfold kvReadAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold putGetInv at Hinv
  icases Hinv with ⟨-, #Hinv⟩
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %n, Hσ, Hmn, %Hok⟩
  ihave %Hv := monoNatLbOwn_valid γf 1 n 1 $$ Hmn Hlb
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn] with -
    · inext; iexists σ, n; iframe Hσ Hmn; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn] with -
    · inext; iexists σ, n; iframe Hσ Hmn; ipureintro; exact Hok
    imodintro
    iintro !>
    ipureintro; exact Hok.2 Hv.2

end inv

end client
end EtcdGrove
end Perennial
