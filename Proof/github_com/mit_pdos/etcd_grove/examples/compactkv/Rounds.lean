/-
**`compactkv`'s rounds: each round's get returns its put's value** (the client's `kv.Compact`,
2026-11-01; `PutThenGet.lean`'s monotone route, over a list of keys). `Main` is the one writer:
round `i` puts `keys[i] ↦ val`, then gets `keys[i]`. A put's update may fire more than once, even
after its call returned, and it changes nothing but its key: a monotone count of the rounds whose
put has fired suffices.

* `roundsInv γ γf keys val`: the client's invariant holds `etcdKV` (its half) with the state
  sorted by key, past revision `0`, and a monotone count `n` at `γf` such that the keys of the
  first `n` rounds hold `val`.
* `putAu_round`: round `i`'s put's update, given that the first `i` rounds' puts fired; its result
  is that the first `i + 1` did, and the state's revision at the firing.
* `getAu_round`: once round `i`'s put fired, a read update whose result is `keys[i] ↦ val`.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.PutThenGet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace compactkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
  client

section pure
variable [GooseExts]
open mvcc

/-- What the invariant keeps of the state after the first `n` rounds' puts fired: sorted by key,
past revision `0` (`NewStore`'s two revisions), and those rounds' keys at `val`. -/
def roundsOk (keys : List GoString) (val : GoString) (σ : KVState) (n : Nat) : Prop :=
  σ.kvs.Pairwise etcdKvLess ∧ 1 ≤ σ.rev ∧
    ∀ j k, j < n → keys[j]? = some k → (mvcc.findKey k σ.kvs).map EtcdKv.value = some val

/-- A put with no options writes its key and nothing else. -/
theorem kvOpStep_putKey_kvs (key val : GoString) (σ : KVState) :
    (kvOpStep (.put (putKeyOp key val)) σ).kvs =
      putKv (W64 ((σ.rev + 1 : Nat) : Int)) key val (W64 0) σ.kvs := by
  simp [kvOpStep, KVState.commit_kvs, KVState.leaseMissing, txn.needsPrev, mvcc.applyChanges,
    mvcc.applyChange, txn.putChangeOf, txn.putValOf, txn.putLeaseOf, putKeyOp, txn.putOpOf]

/-- A step never lowers the state's revision (`InvServerKV.lean`'s `kvOpStep_rev`, in a pure
section). -/
theorem kvOpStep_rev_le (op : KVOp) (σ : KVState) : σ.rev ≤ (kvOpStep op σ).rev := by
  cases op <;> simp only [kvOpStep] <;> (repeat' split) <;>
    (first | exact Nat.le_refl _ | (unfold KVState.commit; split <;> simp [KVState.rev]))

/-- **Round `i`'s put keeps the invariant**, once the first `i` rounds' puts fired. -/
theorem roundsOk_put (keys : List GoString) (val : GoString) (σ : KVState) (n i : Nat)
    (k : GoString) (hk : keys[i]? = some k) (hn : i ≤ n) (h : roundsOk keys val σ n) :
    roundsOk keys val (kvOpStep (.put (putKeyOp k val)) σ) (max n (i + 1)) := by
  obtain ⟨hs, hr, hv⟩ := h
  have Hstep := kvOpStep_putKey k val σ hs
  refine ⟨Hstep.1, Nat.le_trans hr (kvOpStep_rev_le _ σ), fun j k' hj hk' => ?_⟩
  by_cases he : k' = k
  · subst he; exact Hstep.2
  · rw [kvOpStep_putKey_kvs, findKey_putKv_other hs _ k' k val _ (Ne.symm he)]
    rcases Nat.lt_or_ge j n with hj' | hj'
    · exact hv j k' hj' hk'
    · have : j = i := by omega
      subst this
      rw [hk] at hk'
      exact absurd (Option.some.inj hk').symm he

end pure

section inv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The client's invariant for the rounds** (see the file header): `etcdKV` and the count of
rounds whose put fired at `γf`. -/
def roundsInv (γ : ReadNames) (γf : GName) (keys : List GoString) (val : GoString) : IProp GF :=
  inv kvClientN iprop(∃ (σ : KVState) (n : Nat), etcdKV γ.kv σ ∗ monoNatAuthOwn γf 1 n ∗
    ⌜roundsOk keys val σ n⌝)

instance roundsInv_persistent (γ : ReadNames) (γf : GName) (keys : List GoString)
    (val : GoString) : Persistent (roundsInv (GF := GF) γ γf keys val) := by
  unfold roundsInv; infer_instance

/-- The invariant at a start state (a log's, past revision `0`), no round's put fired. -/
theorem roundsInv_alloc (γr : ReadNames) (l : mvcc.Log) (keys : List GoString) (val : GoString)
    (Em : CoPset) (hl : 2 ≤ l.length) :
    etcdKV (GF := GF) γr.kv (kvStateOf l) ⊢ |={Em}=> ∃ γf : GName, roundsInv γr γf keys val := by
  iintro Hσ
  imod (mono_nat_own_alloc (GF := GF) 0) with ⟨%γf, Hm, -⟩
  imod inv_alloc kvClientN Em (iprop(∃ (σ : KVState) (n : Nat), etcdKV γr.kv σ ∗
      monoNatAuthOwn γf 1 n ∗ ⌜roundsOk keys val σ n⌝)) $$ [Hσ Hm] with #Hinv
  · inext; iexists kvStateOf l, 0; iframe Hσ Hm
    ipureintro
    refine ⟨KVState.kvs_sorted _, ?_, fun _ _ h => absurd h (by omega)⟩
    rw [kvStateOf_rev]; omega
  imodintro
  iexists γf
  iunfold roundsInv
  iexact Hinv

/-- **Round `i`'s put's update** (persistent): from the first `i` rounds' puts fired, each firing
writes `keys[i] ↦ val`; its result is that the first `i + 1` fired and the state's revision past
`0`. -/
theorem putAu_round (γ : ReadNames) (γf : GName) (keys : List GoString) (val : GoString) (i : Nat)
    (k : GoString) (hk : keys[i]? = some k) :
    roundsInv γ γf keys val ∗ monoNatLbOwn γf i ⊢
      kvOpAu (GF := GF) γ.kv (.put (putKeyOp k val))
        (fun σ => iprop(monoNatLbOwn γf (i + 1) ∗ ⌜1 ≤ σ.rev⌝)) := by
  have Hm := kvClientN_mask
  iintro ⟨#Hinv, #Hlb⟩
  iunfold kvOpAu
  iunfold roundsInv at Hinv
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %n, Hσ, Hmn, %Hok⟩
  ihave %Hv := monoNatLbOwn_valid γf 1 n i $$ Hmn Hlb
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
    imod (mono_nat_own_update (GF := GF) (γ := γf) (max n (i + 1)) (Nat.le_max_left n (i + 1)))
      $$ Hmn with ⟨Hmn, #Hlb'⟩
    have Hstep := roundsOk_put keys val σ n i k hk Hv.2 Hok
    imod Hclose $$ [Hσ Hmn] with -
    · inext; iexists (kvOpStep (.put (putKeyOp k val)) σ), (max n (i + 1)); iframe Hσ Hmn
      ipureintro; exact Hstep
    imodintro
    iintro !>
    isplitl
    · iapply monoNatLbOwn_le (i + 1) (Nat.le_max_right n (i + 1)) $$ Hlb'
    ipureintro; exact Hok.2.1

/-- **Round `i`'s get's update, after its put fired** (persistent): a read update whose result is
that the state's value of `keys[i]` is `val`. -/
theorem getAu_round (γ : ReadNames) (γf : GName) (keys : List GoString) (val : GoString) (i : Nat)
    (k : GoString) (hk : keys[i]? = some k) :
    roundsInv γ γf keys val ∗ monoNatLbOwn γf (i + 1) ⊢
      kvReadAu (GF := GF) γ.kv
        (fun σ => iprop(⌜(mvcc.findKey k σ.kvs).map EtcdKv.value = some val⌝)) := by
  have Hm := kvClientN_mask
  iintro ⟨#Hinv, #Hlb⟩
  iunfold kvReadAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold roundsInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %n, Hσ, Hmn, %Hok⟩
  ihave %Hv := monoNatLbOwn_valid γf 1 n (i + 1) $$ Hmn Hlb
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
    ipureintro; exact Hok.2.2 i k (by omega) hk

end inv

end compactkv
end EtcdGrove
end Perennial
