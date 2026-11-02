/-
**`compactkv`'s rounds: each round's get returns its put's value, and a get at a round's put's
revision too** (the client's `kv.Compact`, 2026-11-01; `PutThenGet.lean`'s monotone route, over a
list of keys). `Main` is the one writer: round `i` puts `keys[i] ↦ val`, then gets `keys[i]`, then
gets the previous round's key at that round's put's revision. A put's update may fire more than
once, even after its call returned, and it changes nothing but its key, in a revision of its own: a
monotone count of the rounds whose put has fired, and the revision of each one's first firing,
suffice; a state's earlier revisions never change (`kvOpStep_at`).

* `roundsInv γ γf γl γv keys val`: the client's invariant holds `etcdKV` (its half) with the state
  sorted by key, past revision `0`, a monotone count `n` at `γf` and the list `L` (`n` long) of the
  rounds' first firings' revisions at `γl`, such that round `j`'s key holds `val` at every revision
  from `L[j]` to the current one.
* `putAu_round`: round `i`'s put's update, given that the first `i` rounds' puts fired; its result
  is that the first `i + 1` did, round `i`'s first firing at most the revision this firing wrote,
  and the state's revision at the firing.
* `getAu_round`: once round `i`'s put fired, a read update whose result is `keys[i] ↦ val`.
* `getAtAu_round`: once round `i`'s put first fired at `r0`, a read update whose result is
  `keys[i] ↦ val` at every revision from `r0` to the current one.
* (watches across a compaction, W4) `oneValAu`: a read update whose result is that every revision
  is one put of `val`, or empty (`oneValW`, kept by every put): the watch's `noDupKeys` and the
  events' value (`NoDup.lean`).

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

/-- **Every revision is one put of `val`, or empty** (watches across a compaction, W4,
2026-11-01): the rounds' puts are the only writes. So no revision writes a key twice (the watch's
`noDupKeys`), and every event is a put of `val`. -/
def oneValW (val : GoString) (chs : List (List mvcc.Change)) : Prop :=
  ∀ cs ∈ chs, cs = [] ∨ ∃ (k : GoString) (l : w64), cs = [.put k val l]

/-- What the invariant keeps of the state after the rounds' puts whose first firings were at the
revisions `L` fired: sorted by key, past revision `0` (`NewStore`'s two revisions), and round `j`'s
key at `val` at every revision from `L[j]` to the current one. -/
def roundsOk (keys : List GoString) (val : GoString) (σ : KVState) (L : List Nat) : Prop :=
  σ.kvs.Pairwise etcdKvLess ∧ 1 ≤ σ.rev ∧
    (∀ (j : Nat) (k : GoString) (r0 : Nat), L[j]? = some r0 → keys[j]? = some k → r0 ≤ σ.rev ∧
      ∀ r, r0 ≤ r → r ≤ σ.rev → (mvcc.findKey k (σ.at r).kvs).map EtcdKv.value = some val) ∧
    oneValW val σ.changes

/-- A put with no options writes its key and nothing else. -/
theorem kvOpStep_putKey_kvs (key val : GoString) (σ : KVState) :
    (kvOpStep (.put (putKeyOp key val)) σ).kvs =
      putKv (W64 ((σ.rev + 1 : Nat) : Int)) key val (W64 0) σ.kvs := by
  simp [kvOpStep, KVState.commit_kvs, KVState.leaseMissing, txn.needsPrev, mvcc.applyChanges,
    mvcc.applyChange, txn.putChangeOf, txn.putValOf, txn.putLeaseOf, putKeyOp, txn.putOpOf]

/-- A put with no options commits one change. -/
theorem kvOpStep_putKey_eq (key val : GoString) (σ : KVState) :
    kvOpStep (.put (putKeyOp key val)) σ =
      σ.commit [txn.putChangeOf (putKeyOp key val) (mvcc.findKey key σ.kvs)] := by
  simp [kvOpStep, KVState.leaseMissing, txn.needsPrev, putKeyOp, txn.putOpOf]

/-- The revisions a round's first put adds to the list: its first firing's, `r`, unless it fired
before. -/
def roundsL (L : List Nat) (i r : Nat) : List Nat := if i < L.length then L else L ++ [r]

/-- **Round `i`'s put keeps the invariant**, once the first `i` rounds' puts fired: with the list
`roundsL L i (σ.rev + 1)`, which extends `L`, is at least `i + 1` long, and has round `i`'s first
firing at most this one's revision. -/
theorem roundsOk_put (keys : List GoString) (val : GoString) (σ : KVState) (L : List Nat) (i : Nat)
    (k : GoString) (hk : keys[i]? = some k) (hn : i ≤ L.length) (h : roundsOk keys val σ L) :
    roundsOk keys val (kvOpStep (.put (putKeyOp k val)) σ) (roundsL L i (σ.rev + 1)) ∧
      L <+: roundsL L i (σ.rev + 1) ∧ (roundsL L i (σ.rev + 1)).length = max L.length (i + 1) ∧
      ∃ r0, (roundsL L i (σ.rev + 1))[i]? = some r0 ∧ r0 ≤ σ.rev + 1 := by
  obtain ⟨hs, hr, hv, hov⟩ := h
  have Hstep := kvOpStep_putKey k val σ hs
  have hov' : oneValW val (kvOpStep (.put (putKeyOp k val)) σ).changes := by
    rw [kvOpStep_putKey_eq]
    unfold KVState.commit
    simp only [List.cons_ne_nil, ↓reduceIte]
    intro cs hcs
    rcases List.mem_append.1 hcs with h | h
    · exact hov cs h
    · simp only [List.mem_singleton] at h
      subst h
      right
      exact ⟨k, txn.putLeaseOf (putKeyOp k val) (mvcc.findKey k σ.kvs), by
        simp [txn.putChangeOf, txn.putValOf, putKeyOp, txn.putOpOf]⟩
  have hrev : (kvOpStep (.put (putKeyOp k val)) σ).rev = σ.rev + 1 := by
    rw [kvOpStep_putKey_eq]; exact KVState.commit_rev _ _ (List.cons_ne_nil _ _)
  have hat : ∀ r, r ≤ σ.rev → (kvOpStep (.put (putKeyOp k val)) σ).at r = σ.at r := by
    intro r hr'; rw [kvOpStep_putKey_eq]; exact KVState.commit_at _ _ r hr'
  -- the new revision's store: `k` at `val`, every other key as before
  have hnew : ∀ k', (k' = k ∨ (mvcc.findKey k' σ.kvs).map EtcdKv.value = some val) →
      (mvcc.findKey k' ((kvOpStep (.put (putKeyOp k val)) σ).at
        (kvOpStep (.put (putKeyOp k val)) σ).rev).kvs).map EtcdKv.value = some val := by
    intro k' hk'
    show (mvcc.findKey k' (kvOpStep (.put (putKeyOp k val)) σ).kvs).map EtcdKv.value = some val
    by_cases he : k' = k
    · subst he; exact Hstep.2
    · rw [kvOpStep_putKey_kvs, findKey_putKv_other hs _ k' k val _ (Ne.symm he)]
      exact hk'.resolve_left he
  -- a round already in `L` keeps its revisions
  have hold : ∀ (j : Nat) (k' : GoString) (r0 : Nat), L[j]? = some r0 → keys[j]? = some k' →
      r0 ≤ (kvOpStep (.put (putKeyOp k val)) σ).rev ∧
      ∀ r, r0 ≤ r → r ≤ (kvOpStep (.put (putKeyOp k val)) σ).rev →
        (mvcc.findKey k' ((kvOpStep (.put (putKeyOp k val)) σ).at r).kvs).map EtcdKv.value =
          some val := by
    intro j k' r0 hj hk'
    obtain ⟨h0, hrg⟩ := hv j k' r0 hj hk'
    refine ⟨by omega, fun r h1 h2 => ?_⟩
    rcases Nat.lt_or_ge σ.rev r with hgt | hle
    · have hr' : r = (kvOpStep (.put (putKeyOp k val)) σ).rev := by omega
      rw [hr']
      exact hnew k' (Or.inr (hrg σ.rev h0 (Nat.le_refl _)))
    · rw [hat r hle]; exact hrg r h1 hle
  unfold roundsL
  by_cases hi : i < L.length
  · rw [if_pos hi]
    obtain ⟨r0, hr0⟩ : ∃ r0, L[i]? = some r0 := ⟨_, List.getElem?_eq_getElem hi⟩
    refine ⟨⟨Hstep.1, by omega, hold, hov'⟩, List.prefix_refl _, by omega, r0, hr0, ?_⟩
    have := (hv i k r0 hr0 hk).1
    omega
  · rw [if_neg hi]
    have hil : i = L.length := by omega
    refine ⟨⟨Hstep.1, by omega, fun j k' r0 hj hk' => ?_, hov'⟩, List.prefix_append _ _,
      by simp; omega, σ.rev + 1, by rw [hil]; simp, Nat.le_refl _⟩
    rcases Nat.lt_or_ge j L.length with hjl | hjl
    · rw [List.getElem?_append_left hjl] at hj
      exact hold j k' r0 hj hk'
    · rw [List.getElem?_append_right hjl] at hj
      have hj0 : j - L.length = 0 := by
        rcases Nat.eq_zero_or_pos (j - L.length) with h0 | h0
        · exact h0
        · simp [show ¬ (j - L.length = 0) by omega] at hj
      rw [hj0] at hj
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      have hjk : j = i := by omega
      subst hjk
      rw [hk] at hk'
      cases hk'
      refine ⟨by omega, fun r h1 h2 => ?_⟩
      have hr' : r = (kvOpStep (.put (putKeyOp k val)) σ).rev := by omega
      rw [hr']
      exact hnew k (Or.inl rfl)

end pure

section inv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The client's invariant for the rounds** (see the file header): `etcdKV`, the count of
rounds whose put fired at `γf` and their first firings' revisions at `γl`; (the read-side law,
2026-11-02) the state's revision as a monotone counter at `γv` (as `client.kvClientInv`'s), where
a revision the cluster has reached is a lower bound (`roundsInv_revLb`). -/
def roundsInv (γ : ReadNames) (γf γl γv : GName) (keys : List GoString) (val : GoString) :
    IProp GF :=
  inv kvClientN iprop(∃ (σ : KVState) (n : Nat) (L : List Nat), etcdKV γ.kv σ ∗
    monoNatAuthOwn γf 1 n ∗ monoListAuthOwn γl 1 L ∗ monoNatAuthOwn γv 1 σ.rev ∗
    ⌜L.length = n ∧ roundsOk keys val σ L⌝)

instance roundsInv_persistent (γ : ReadNames) (γf γl γv : GName) (keys : List GoString)
    (val : GoString) : Persistent (roundsInv (GF := GF) γ γf γl γv keys val) := by
  unfold roundsInv; infer_instance

/-- The invariant at a start state (a log's, past revision `0`), no round's put fired. -/
theorem roundsInv_alloc (γr : ReadNames) (l : mvcc.Log) (keys : List GoString) (val : GoString)
    (Em : CoPset) (hl : 2 ≤ l.length) (hov : oneValW val (kvStateOf l).changes) :
    etcdKV (GF := GF) γr.kv (kvStateOf l) ⊢
      |={Em}=> ∃ γf γl γv : GName, roundsInv γr γf γl γv keys val := by
  iintro Hσ
  imod (mono_nat_own_alloc (GF := GF) 0) with ⟨%γf, Hm, -⟩
  imod (mono_list_own_alloc (GF := GF) ([] : List Nat)) with ⟨%γl, HL, -⟩
  imod (mono_nat_own_alloc (GF := GF) (kvStateOf l).rev) with ⟨%γv, Hrv, -⟩
  imod inv_alloc kvClientN Em (iprop(∃ (σ : KVState) (n : Nat) (L : List Nat), etcdKV γr.kv σ ∗
      monoNatAuthOwn γf 1 n ∗ monoListAuthOwn γl 1 L ∗ monoNatAuthOwn γv 1 σ.rev ∗
      ⌜L.length = n ∧ roundsOk keys val σ L⌝))
      $$ [Hσ Hm HL Hrv] with #Hinv
  · inext; iexists kvStateOf l, 0, []; iframe Hσ Hm HL Hrv
    ipureintro
    refine ⟨rfl, KVState.kvs_sorted _, ?_, fun _ _ _ h => by simp at h, hov⟩
    rw [kvStateOf_rev]; omega
  imodintro
  iexists γf, γl, γv
  iunfold roundsInv
  iexact Hinv

/-- **Round `i`'s put's update** (persistent): from the first `i` rounds' puts fired, each firing
writes `keys[i] ↦ val`; its result is that the first `i + 1` fired, round `i`'s first firing at a
revision `r0` at most the one this firing wrote (`σ.rev + 1`), and the state's revision past `0`. -/
theorem putAu_round (γ : ReadNames) (γf γl γv : GName) (keys : List GoString) (val : GoString)
    (i : Nat) (k : GoString) (hk : keys[i]? = some k) :
    roundsInv γ γf γl γv keys val ∗ monoNatLbOwn γf i ⊢
      kvOpAu (GF := GF) γ.kv (.put (putKeyOp k val))
        (fun σ => iprop(monoNatLbOwn γf (i + 1) ∗
          (∃ r0, monoListIdxOwn γl i r0 ∗ ⌜r0 ≤ σ.rev + 1⌝) ∗ ⌜1 ≤ σ.rev⌝)) := by
  have Hm := kvClientN_mask
  iintro ⟨#Hinv, #Hlb⟩
  iunfold kvOpAu
  iunfold roundsInv at Hinv
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %n, %L, Hσ, Hmn, HL, Hrv, %Hok⟩
  ihave %Hv := monoNatLbOwn_valid γf 1 n i $$ Hmn Hlb
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn HL Hrv] with -
    · inext; iexists σ, n, L; iframe Hσ Hmn HL Hrv; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro Hσ
    imod Hmask with -
    obtain ⟨Hstep, Hpre, Hlen, r0, Hr0, Hr0le⟩ :=
      roundsOk_put keys val σ L i k hk (by omega) Hok.2
    imod (mono_nat_own_update (GF := GF) (γ := γf) (max n (i + 1)) (Nat.le_max_left n (i + 1)))
      $$ Hmn with ⟨Hmn, #Hlb'⟩
    imod (monoListAuthOwn_update (GF := GF) (γ := γl) _ Hpre) $$ HL with ⟨HL, #HLb⟩
    ihave #Hidx := monoListIdxOwn_get (γ := γl) i r0 Hr0 $$ HLb
    imod (mono_nat_own_update (GF := GF) (γ := γv) (kvOpStep (.put (putKeyOp k val)) σ).rev
      (kvOpStep_rev _ σ)) $$ Hrv with ⟨Hrv, -⟩
    imod Hclose $$ [Hσ Hmn HL Hrv] with -
    · inext
      iexists (kvOpStep (.put (putKeyOp k val)) σ), (max n (i + 1)), (roundsL L i (σ.rev + 1))
      iframe Hσ Hmn HL Hrv
      ipureintro; exact ⟨by rw [Hlen, Hok.1], Hstep⟩
    imodintro
    iintro !>
    isplitl
    · iapply monoNatLbOwn_le (i + 1) (Nat.le_max_right n (i + 1)) $$ Hlb'
    isplitl
    · iexists r0; iframe Hidx; ipureintro; exact Hr0le
    ipureintro; exact Hok.2.2.1

/-- **Round `i`'s get's update, after its put fired** (persistent): a read update whose result is
that the state's value of `keys[i]` is `val`. -/
theorem getAu_round (γ : ReadNames) (γf γl γv : GName) (keys : List GoString) (val : GoString)
    (i : Nat) (k : GoString) (hk : keys[i]? = some k) (r : Nat) :
    roundsInv γ γf γl γv keys val ∗ monoNatLbOwn γf (i + 1) ∗ monoNatLbOwn γv r ⊢
      kvReadAu (GF := GF) γ.kv
        (fun σ => iprop(⌜(mvcc.findKey k σ.kvs).map EtcdKv.value = some val ∧ r ≤ σ.rev⌝)) := by
  have Hm := kvClientN_mask
  iintro ⟨#Hinv, #Hlb, #Hrlb⟩
  iunfold kvReadAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold roundsInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %n, %L, Hσ, Hmn, HL, Hrv, %Hok⟩
  ihave %Hv := monoNatLbOwn_valid γf 1 n (i + 1) $$ Hmn Hlb
  ihave %Hrr := monoNatLbOwn_valid γv 1 σ.rev r $$ Hrv Hrlb
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn HL Hrv] with -
    · inext; iexists σ, n, L; iframe Hσ Hmn HL Hrv; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn HL Hrv] with -
    · inext; iexists σ, n, L; iframe Hσ Hmn HL Hrv; ipureintro; exact Hok
    imodintro
    iintro !>
    ipureintro
    have hi : i < L.length := by omega
    obtain ⟨h0, hrg⟩ := Hok.2.2.2.1 i k _ (List.getElem?_eq_getElem hi) hk
    exact ⟨hrg σ.rev h0 (Nat.le_refl _), Hrr.2⟩

/-- **A get at a revision past round `i`'s put's first firing** (persistent): with round `i`'s first
firing at `r0`, a read update whose result is that `keys[i]` holds `val` at every revision from
`r0` to the state's current one. -/
theorem getAtAu_round (γ : ReadNames) (γf γl γv : GName) (keys : List GoString) (val : GoString)
    (i r0 : Nat) (k : GoString) (hk : keys[i]? = some k) :
    roundsInv γ γf γl γv keys val ∗ monoListIdxOwn γl i r0 ⊢
      kvReadAu (GF := GF) γ.kv
        (fun σ => iprop(⌜∀ r, r0 ≤ r → r ≤ σ.rev →
          (mvcc.findKey k (σ.at r).kvs).map EtcdKv.value = some val⌝)) := by
  have Hm := kvClientN_mask
  iintro ⟨#Hinv, #Hidx⟩
  iunfold kvReadAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold roundsInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %n, %L, Hσ, Hmn, HL, Hrv, %Hok⟩
  ihave %Hl := mono_list_auth_idx_lookup γl 1 L i r0 $$ HL Hidx
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn HL Hrv] with -
    · inext; iexists σ, n, L; iframe Hσ Hmn HL Hrv; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn HL Hrv] with -
    · inext; iexists σ, n, L; iframe Hσ Hmn HL Hrv; ipureintro; exact Hok
    imodintro
    iintro !>
    ipureintro
    exact (Hok.2.2.2.1 i k r0 Hl hk).2

/-- **The rounds' writes, read** (persistent; watches across a compaction, W4): a read update
whose result is that every revision is one put of `val`, or empty (`oneValW`). -/
theorem oneValAu (γ : ReadNames) (γf γl γv : GName) (keys : List GoString) (val : GoString) :
    roundsInv γ γf γl γv keys val ⊢
      kvReadAu (GF := GF) γ.kv (fun σ => iprop(⌜oneValW val σ.changes⌝)) := by
  have Hm := kvClientN_mask
  iintro #Hinv
  iunfold kvReadAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold roundsInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %n, %L, Hσ, Hmn, HL, Hrv, %Hok⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn HL Hrv] with -
    · inext; iexists σ, n, L; iframe Hσ Hmn HL Hrv; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn HL Hrv] with -
    · inext; iexists σ, n, L; iframe Hσ Hmn HL Hrv; ipureintro; exact Hok
    imodintro
    iintro !>
    ipureintro
    exact Hok.2.2.2.2

/-- **A read at a revision at least the counter's bound** (persistent; C3's watch side,
2026-11-02): a read update whose result is that the state's revision is at least `r`. -/
theorem getRevAu_round (γ : ReadNames) (γf γl γv : GName) (keys : List GoString) (val : GoString)
    (r : Nat) :
    roundsInv γ γf γl γv keys val ∗ monoNatLbOwn γv r ⊢
      kvReadAu (GF := GF) γ.kv (fun σ => iprop(⌜r ≤ σ.rev⌝)) := by
  have Hm := kvClientN_mask
  iintro ⟨#Hinv, #Hrlb⟩
  iunfold kvReadAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold roundsInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %n, %L, Hσ, Hmn, HL, Hrv, %Hok⟩
  ihave %Hrr := monoNatLbOwn_valid γv 1 σ.rev r $$ Hrv Hrlb
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn HL Hrv] with -
    · inext; iexists σ, n, L; iframe Hσ Hmn HL Hrv; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn HL Hrv] with -
    · inext; iexists σ, n, L; iframe Hσ Hmn HL Hrv; ipureintro; exact Hok
    imodintro
    iintro !>
    ipureintro
    exact Hrr.2

/-- **A revision the cluster has reached is a lower bound of the rounds' state** (the read-side
law, 2026-11-02, `kv_revLbZ_le`): with the KV invariant, a reached revision `n` gives the counter's
lower bound, so every later read of the rounds reads at a revision at least `n`. -/
theorem roundsInv_revLb [go_etcd_io.raft.v3.Assumptions] (γ : ReadNames) (γf γl γv : GName) (keys : List GoString)
    (val : GoString) (n : Nat) :
    ⊢ kvInv (GF := GF) γ.raft γ.kv -∗ roundsInv γ γf γl γv keys val -∗ kvRevLbZ γ.kv n ={⊤}=∗
      monoNatLbOwn γv n := by
  have Hm := kvClientN_mask
  iintro #Hkv #Hinv #Hlb
  iunfold roundsInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %n', %L, Hσ, Hmn, HL, Hrv, %Hok⟩
  have hE : (↑kvN : CoPset) ⊆ ⊤ \ ↑kvClientN :=
    Perennial.mask_ndot_ne' nroot _ _ (by decide)
  imod (kv_revLbZ_le γ.raft γ.kv (⊤ \ ↑kvClientN) hE n σ) $$ Hkv Hlb Hσ with ⟨Hσ, %Hn⟩
  ihave #Hlb' := monoNatLbOwn_get γv 1 σ.rev $$ Hrv
  imod Hclose $$ [Hσ Hmn HL Hrv] with -
  · inext; iexists σ, n', L; iframe Hσ Hmn HL Hrv; ipureintro; exact Hok
  imodintro
  iapply monoNatLbOwn_le n (by omega) $$ Hlb'

end inv

end compactkv
end EtcdGrove
end Perennial
