/- Lean-first (no Rocq counterpart).

# The cluster's KV shared by key prefix (`notes/etcd-dist-plan.md` §23, N9a)

Several workloads of one deployment write the cluster's KV at once (putget, durable, compact: one key
prefix each, `deployment.Compatible`), and each one's check is about its own prefix. The cluster's client
half of the KV state (`etcdKV γk σ`, which the start has after the members' boot) goes into one invariant,
`kvPfxInv γk ps`, with, for each owned prefix `p` of `ps` (at the ghost name `γ`), half of a ghost variable
holding `pfxView p σ`, the state's key-values under `p`. The owner of `p` holds the other half, so only it
changes them; a write of the owner of `p` leaves every other prefix's key-values as they were when no prefix
is a prefix of another (`PfxsApart`; the deployment's are `pg/`, `du/`, `cw/`, `wk/`, `ck/`).

- `pfxView`, `PfxsApart`, `PfxLocal` (an update of the state that changes no key-value of a prefix apart
  from `p`), `pfxLocal_putKey` (a put of a key under `p` is local to `p`);
- `kvPfxInv γk ps`, `kvPfx γk p γ` (persistent: the invariant, with `p` at `γ` among its prefixes);
- `kvPfx_au1`: an owner's update of the KV by an update local to its prefix, fired at most once (a write
  sent at most once: `KV_Put_dist`'s), from the owner's own invariant over its half
  (`inv (kvClientN.@s) (∃ v, ghostVar γ ½ v ∗ W v)`) and a step of `W`;
- `kvPfx_readAu`: an owner's persistent read update (`kvReadAu`, `KV_Get_dist`'s), from a persistent read
  of `W`;
- `kvPfx_alloc`: the start's allocation, from `etcdKV γk σ₀` with no key-value and no change, for prefixes
  apart: the invariant and each prefix's half at `[]`.

**The history** (F5, the compact workload, `notes/etcd-dist-plan.md` §26): an owner that checks reads at
older revisions or watches needs facts about the state's past, which its view (the current key-values) does
not carry. So the invariant also keeps the list of the state's changes (`monoListAuthOwn γh`, append-only:
every update is local, `PfxLocal`, so it appends changes, each of a key under its owner's prefix, and keeps the
compaction revision and base: every state extends the start's, `KVExt σ₀`), and, for each prefix, its owner's discipline over the changes of its
keys (`ok p`, e.g. "every change is a put of `v`"; `fun _ => True` for none). `kvPfxH γk p γ okp γh σ₀`
is the owner's fact with the discipline and the history's names; `kvPfx` the one without. Laws:
`kvPfx_au1H`/`kvPfx_readAuH` (the steps learn the history's facts: a lower bound of the changes, the
discipline), `kvPfx_seen` (with the KV invariant: a revision the cluster has reached bounds a lower bound of
the changes).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Perennial.Ghost.MonoList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
open client (putKeyOp)

/-! ## Prefix views, purely -/

section pure
variable [GooseExts]

/-- **The key-values of the state under the prefix `p`** (in key order). -/
def pfxView (p : GoString) (σ : KVState) : List EtcdKv :=
  σ.kvs.filter (fun v => decide (p <+: v.key))

/-- **No prefix of the list is a prefix of another's.** -/
def PfxsApart (ps : List (GoString × GName)) : Prop :=
  ∀ (i j : Nat) (a b : GoString × GName), i ≠ j → ps[i]? = some a → ps[j]? = some b → ¬ a.1 <+: b.1

/-- **The update `f` of the state is local to the prefix `p`**: it changes the key-values of no prefix
apart from `p`, and (the history, F5) it keeps the compaction revision and the base, its changes the
state's followed by changes of keys under `p` only. -/
def PfxLocal (p : GoString) (f : KVState → KVState) : Prop :=
  (∀ (σ : KVState) (q : GoString), ¬ q <+: p → ¬ p <+: q → pfxView q (f σ) = pfxView q σ) ∧
  ∀ σ : KVState, (f σ).compacted = σ.compacted ∧ (f σ).base = σ.base ∧
    ∃ new : List (List mvcc.Change), (f σ).changes = σ.changes ++ new ∧
      ∀ cs ∈ new, ∀ c ∈ cs, p <+: c.key

/-- **Every change of a key under `p` among the changes `chs` satisfies `ok`** (F5: an owner's
discipline over its prefix's history, which the shared invariant keeps). -/
def PfxChOk (p : GoString) (ok : mvcc.Change → Prop) (chs : List (List mvcc.Change)) : Prop :=
  ∀ cs ∈ chs, ∀ c ∈ cs, p <+: c.key → ok c

/-- **The state `σ` extends the start's `σ₀`** (F5): the same compaction revision and base, its changes
extending the start's. -/
def KVExt (σ₀ σ : KVState) : Prop :=
  σ.compacted = σ₀.compacted ∧ σ.base = σ₀.base ∧ σ₀.changes <+: σ.changes

theorem KVExt.rev_le {σ₀ σ : KVState} (h : KVExt σ₀ σ) : σ₀.rev ≤ σ.rev := by
  unfold KVState.rev; rw [h.1]; have := h.2.2.length_le; omega

theorem KVExt.rev_eq {σ₀ σ : KVState} (h : KVExt σ₀ σ) : σ.rev = σ₀.compacted + σ.changes.length := by
  unfold KVState.rev; rw [h.1]

/-- **Two extensions of the start, one's changes a prefix of the other's, agree at the first one's
revisions.** -/
theorem KVExt.at_eq {σ₀ σ1 σ2 : KVState} (h1 : KVExt σ₀ σ1) (h2 : KVExt σ₀ σ2)
    (hp : σ1.changes <+: σ2.changes) (r : Nat) (hr : r ≤ σ1.rev) : σ1.at r = σ2.at r := by
  have hc : σ1.compacted = σ2.compacted := h1.1.trans h2.1.symm
  have hb : σ1.base = σ2.base := h1.2.1.trans h2.2.1.symm
  unfold KVState.at
  rw [hc, hb]
  split
  · rfl
  · obtain ⟨t, ht⟩ := hp
    have hle : r - σ2.compacted ≤ σ1.changes.length := by unfold KVState.rev at hr; omega
    rw [← ht, List.take_append_of_le_length hle]

theorem pfxChOk_prefix {p : GoString} {ok : mvcc.Change → Prop} {l L : List (List mvcc.Change)}
    (h : l <+: L) (hL : PfxChOk p ok L) : PfxChOk p ok l :=
  fun cs hcs => hL cs (h.subset hcs)

/-- **An owner's changes keep every prefix's discipline**: the new changes, all under the owner's prefix
`p` and each `ok p`, break no other prefix's (none is under a prefix apart from `p`). -/
theorem pfxChOk_step (ps : List (GoString × GName)) (ok : GoString → mvcc.Change → Prop) (i : Nat)
    (p : GoString) (γ : GName) (hap : PfxsApart ps) (hi : ps[i]? = some (p, γ))
    (chs new : List (List mvcc.Change)) (hloc : ∀ cs ∈ new, ∀ c ∈ cs, p <+: c.key)
    (hok : ∀ cs ∈ new, ∀ c ∈ cs, ok p c) (h : ∀ e ∈ ps, PfxChOk e.1 (ok e.1) chs) :
    ∀ e ∈ ps, PfxChOk e.1 (ok e.1) (chs ++ new) := by
  intro e he cs hcs c hc hec
  rcases List.mem_append.1 hcs with hcs | hcs
  · exact h e he cs hcs c hc hec
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 he
    by_cases hki : k = i
    · subst hki
      rw [hi] at hk
      have he' : e = (p, γ) := (Option.some.inj hk).symm
      subst he'
      exact hok cs hcs c hc
    · have hpc := hloc cs hcs c hc
      rcases List.prefix_or_prefix_of_prefix hec hpc with h1 | h1
      · exact absurd h1 (hap k i e (p, γ) hki hk hi)
      · exact absurd h1 (hap i k (p, γ) e (Ne.symm hki) hi hk)

/-- A filter that selects no key of `nv`'s is unchanged by inserting `nv` (leasing's
`filter_btInsert`). -/
theorem filter_btInsert_other (nv : EtcdKv) (s : List EtcdKv) (P : EtcdKv → Bool)
    (hp : ∀ v, P v = true → v.key ≠ nv.key) :
    (btInsert etcdKvLess nv s).filter P = s.filter P := by
  have hnv : P nv = false := by
    cases h : P nv
    · rfl
    · exact absurd rfl (hp nv h)
  induction s with
  | nil => simp [btInsert, hnv]
  | cons w ws ih =>
    unfold btInsert
    split
    · rw [List.filter_cons, List.filter_cons, ih]
    · split
      · rw [List.filter_cons, hnv]; simp
      · rename_i h1 h2
        have he : w.key = nv.key := go.goStringLt_eq_of_not_lt h1 h2
        have hw : P w = false := by
          cases h : P w
          · rfl
          · exact absurd he (hp w h)
        rw [List.filter_cons, hnv, List.filter_cons, hw]; simp

/-- **The new key-value of `putKv r k val l s`.** -/
def putKvNew (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) : EtcdKv :=
  match s.find? (fun v => decide (v.key = k)) with
  | some v => { v with modRev := r, version := v.version + W64 1, value := val, lease := l }
  | none => { key := k, createRev := r, modRev := r, version := W64 1, value := val, lease := l }

theorem putKv_eq (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) :
    putKv r k val l s = btInsert etcdKvLess (putKvNew r k val l s) s := rfl

theorem putKvNew_key (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) :
    (putKvNew r k val l s).key = k := by
  unfold putKvNew
  split
  · rename_i v hf
    have := List.find?_some hf
    simpa using this
  · rfl

theorem putKvNew_value (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) :
    (putKvNew r k val l s).value = val := by
  unfold putKvNew; split <;> rfl

/-- A put of an absent key creates it at version `1`. -/
theorem putKvNew_version (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv)
    (h : ∀ x ∈ s, x.key ≠ k) : (putKvNew r k val l s).version = W64 1 := by
  have hn : s.find? (fun v => decide (v.key = k)) = none := by
    rw [List.find?_eq_none]
    intro x hx
    simpa using h x hx
  unfold putKvNew
  rw [hn]

/-- The put `putKv r k val l s` changes no key but `k`. -/
theorem filter_putKv_other (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv)
    (P : EtcdKv → Bool) (hp : ∀ v, P v = true → v.key ≠ k) :
    (putKv r k val l s).filter P = s.filter P := by
  rw [putKv_eq]
  apply filter_btInsert_other
  intro v hv
  rw [putKvNew_key]
  exact hp v hv

/-- A key-value after a put is the new one or one before it. -/
theorem mem_putKv {r : w64} {k val : GoString} {l : w64} {s : List EtcdKv} {x : EtcdKv}
    (h : x ∈ putKv r k val l s) : x = putKvNew r k val l s ∨ x ∈ s := by
  rw [putKv_eq] at h
  exact btInsert_mem h

/-- The new key-value is in the state after the put. -/
theorem putKvNew_mem (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) :
    putKvNew r k val l s ∈ putKv r k val l s := by
  rw [putKv_eq]
  generalize putKvNew r k val l s = v
  induction s with
  | nil => simp [btInsert]
  | cons w ws ih =>
    unfold btInsert
    split
    · exact List.mem_cons_of_mem _ ih
    · split <;> simp

/-- A key-value of another key is kept by a put. -/
theorem putKv_keep {r : w64} {k val : GoString} {l : w64} {s : List EtcdKv} {x : EtcdKv}
    (hx : x ∈ s) (hk : x.key ≠ k) : x ∈ putKv r k val l s := by
  have h := filter_putKv_other r k val l s (fun v => decide (v.key = x.key))
    (fun v hv => by simp at hv; rw [hv]; exact hk)
  have hx' : x ∈ s.filter (fun v => decide (v.key = x.key)) := List.mem_filter.2 ⟨hx, by simp⟩
  rw [← h] at hx'
  exact (List.mem_filter.1 hx').1

/-- A put with no options writes its key and nothing else (compactwatch's). -/
theorem kvOpStep_putKey_kvs' (key val : GoString) (σ : KVState) :
    (kvOpStep (.put (putKeyOp key val)) σ).kvs =
      putKv (W64 ((σ.rev + 1 : Nat) : Int)) key val (W64 0) σ.kvs := by
  simp [kvOpStep, KVState.commit_kvs, KVState.leaseMissing, txn.needsPrev, mvcc.applyChanges,
    mvcc.applyChange, txn.putChangeOf, txn.putValOf, txn.putLeaseOf, putKeyOp, txn.putOpOf]

/-- A put with no options commits its one change (compactwatch's `kvOpStep_putKey_eq`). -/
theorem kvOpStep_putKey_eq' (key val : GoString) (σ : KVState) :
    kvOpStep (.put (putKeyOp key val)) σ =
      σ.commit [txn.putChangeOf (putKeyOp key val) (mvcc.findKey key σ.kvs)] := by
  simp [kvOpStep, KVState.leaseMissing, txn.needsPrev, putKeyOp, txn.putOpOf]

/-- **A put with no options appends one revision, a put of its key and value** (the compaction
revision and the base kept). -/
theorem kvOpStep_putKey_hist (key val : GoString) (σ : KVState) :
    (kvOpStep (.put (putKeyOp key val)) σ).compacted = σ.compacted ∧
    (kvOpStep (.put (putKeyOp key val)) σ).base = σ.base ∧
    ∃ l : w64, (kvOpStep (.put (putKeyOp key val)) σ).changes =
      σ.changes ++ [[mvcc.Change.put key val l]] := by
  have hl : txn.putChangeOf (putKeyOp key val) (mvcc.findKey key σ.kvs) =
      mvcc.Change.put key val (txn.putLeaseOf (putKeyOp key val) (mvcc.findKey key σ.kvs)) := by
    simp [txn.putChangeOf, txn.putValOf, putKeyOp, txn.putOpOf]
  rw [kvOpStep_putKey_eq', hl]
  refine ⟨?_, ?_, txn.putLeaseOf (putKeyOp key val) (mvcc.findKey key σ.kvs), ?_⟩ <;>
    simp [KVState.commit]

/-- A put of a key under `p` keeps the compaction revision and the base, and appends one change, of
that key. -/
theorem pfxHist_putKey (p k val : GoString) (hk : p <+: k) (σ : KVState) :
    (kvOpStep (.put (putKeyOp k val)) σ).compacted = σ.compacted ∧
    (kvOpStep (.put (putKeyOp k val)) σ).base = σ.base ∧
    ∃ new : List (List mvcc.Change), (kvOpStep (.put (putKeyOp k val)) σ).changes = σ.changes ++ new ∧
      ∀ cs ∈ new, ∀ c ∈ cs, p <+: c.key := by
  obtain ⟨h1, h2, l, h3⟩ := kvOpStep_putKey_hist k val σ
  refine ⟨h1, h2, [[mvcc.Change.put k val l]], h3, ?_⟩
  intro cs hcs c hc
  simp only [List.mem_singleton] at hcs
  subst hcs
  simp only [List.mem_singleton] at hc
  subst hc
  exact hk

/-- A put of a key under `p` changes no prefix's key-values apart from `p`'s. -/
theorem pfxViews_putKey (p k val : GoString) (hk : p <+: k) (σ : KVState) (q : GoString)
    (hqp : ¬ q <+: p) (hpq : ¬ p <+: q) :
    pfxView q (kvOpStep (.put (putKeyOp k val)) σ) = pfxView q σ := by
  unfold pfxView
  rw [kvOpStep_putKey_kvs']
  apply filter_putKv_other
  intro v hv hvk
  simp only [decide_eq_true_eq] at hv
  rw [hvk] at hv
  rcases List.prefix_or_prefix_of_prefix hv hk with h | h
  · exact hqp h
  · exact hpq h

/-- **A put of a key under `p` is local to `p`**: prefixes apart from `p` are not prefixes of the key;
its one change is of that key. -/
theorem pfxLocal_putKey (p k val : GoString) (hk : p <+: k) :
    PfxLocal p (kvOpStep (.put (putKeyOp k val))) :=
  ⟨fun σ q hqp hpq => pfxViews_putKey p k val hk σ q hqp hpq, pfxHist_putKey p k val hk⟩

/-- The view of `p` after a put of a key under `p`: the new key-value or one before the put. -/
theorem mem_pfxView_put {p k val : GoString} {σ : KVState} {x : EtcdKv}
    (h : x ∈ pfxView p (kvOpStep (.put (putKeyOp k val)) σ)) :
    x = putKvNew (W64 ((σ.rev + 1 : Nat) : Int)) k val (W64 0) σ.kvs ∨ x ∈ pfxView p σ := by
  unfold pfxView at h ⊢
  rw [kvOpStep_putKey_kvs'] at h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 h
  rcases mem_putKv h1 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr (List.mem_filter.2 ⟨h3, h2⟩)

/-- A key-value of another key under `p` stays in `p`'s view after a put. -/
theorem pfxView_put_keep {p k val : GoString} {σ : KVState} {x : EtcdKv}
    (hx : x ∈ pfxView p σ) (hk : x.key ≠ k) :
    x ∈ pfxView p (kvOpStep (.put (putKeyOp k val)) σ) := by
  unfold pfxView at hx ⊢
  rw [kvOpStep_putKey_kvs']
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hx
  exact List.mem_filter.2 ⟨putKv_keep h1 hk, h2⟩

/-- The put's new key-value is in `p`'s view after it (a key under `p`). -/
theorem pfxView_put_new {p k val : GoString} (σ : KVState) (hk : p <+: k) :
    putKvNew (W64 ((σ.rev + 1 : Nat) : Int)) k val (W64 0) σ.kvs ∈
      pfxView p (kvOpStep (.put (putKeyOp k val)) σ) := by
  unfold pfxView
  rw [kvOpStep_putKey_kvs']
  refine List.mem_filter.2 ⟨putKvNew_mem _ _ _ _ _, ?_⟩
  simp only [decide_eq_true_eq, putKvNew_key]
  exact hk

/-- A key under `p` that has a key-value in the state has it in `p`'s view. -/
theorem mem_pfxView_of {p : GoString} {σ : KVState} {x : EtcdKv} (hx : x ∈ σ.kvs)
    (hk : p <+: x.key) : x ∈ pfxView p σ :=
  List.mem_filter.2 ⟨hx, by simpa using hk⟩

theorem mem_of_mem_pfxView {p : GoString} {σ : KVState} {x : EtcdKv} (hx : x ∈ pfxView p σ) :
    x ∈ σ.kvs ∧ p <+: x.key := by
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hx
  exact ⟨h1, by simpa using h2⟩

end pure

/-! ## The shared invariant -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The shared invariant's namespace (inside the clients' `kvClientN`, apart from the owners'). -/
abbrev kvShareN : Namespace := client.kvClientN .@ "share"

/-- **The cluster's client KV, shared by the prefixes `ps`** (see the file header): the state's half, each
prefix's view's half, the list of its changes (`γh`, append-only: every change of the KV is an owner's update
firing in this invariant), the state extending the start's `σ₀` (`KVExt`: every update keeps the compaction
revision and base and appends changes), and each
prefix's discipline over its history (`ok`, F5). -/
def kvPfxInv (γk : KVNames) (ps : List (GoString × GName)) (ok : GoString → mvcc.Change → Prop)
    (γh : GName) (σ₀ : KVState) : IProp GF :=
  inv kvShareN iprop(∃ σ : KVState, etcdKV γk σ ∗
    ([∗list] _k ↦ e ∈ ps, ghostVar e.2 (1 : Qp).half (pfxView e.1 σ)) ∗
    monoListAuthOwn γh 1 σ.changes ∗
    ⌜KVExt σ₀ σ ∧ ∀ e ∈ ps, PfxChOk e.1 (ok e.1) σ.changes⌝)

/-- **The prefix `p` is owned at `γ` in the shared KV of `γk`, under the discipline `okp`, its history
at `γh` from the start `σ₀`** (persistent; F5: what an owner that reads the history holds). -/
def kvPfxH (γk : KVNames) (p : GoString) (γ : GName) (okp : mvcc.Change → Prop) (γh : GName)
    (σ₀ : KVState) : IProp GF :=
  iprop(∃ (ps : List (GoString × GName)) (i : Nat) (ok : GoString → mvcc.Change → Prop),
    ⌜PfxsApart ps ∧ ps[i]? = some (p, γ) ∧ ∀ c, ok p c ↔ okp c⌝ ∗ kvPfxInv γk ps ok γh σ₀)

/-- **The prefix `p` is owned at `γ` in the shared KV of `γk`** (persistent; the owner's half,
`ghostVar γ ½ v`, is separate), with no discipline on its changes. -/
def kvPfx (γk : KVNames) (p : GoString) (γ : GName) : IProp GF :=
  iprop(∃ (γh : GName) (σ₀ : KVState), kvPfxH γk p γ (fun _ => True) γh σ₀)

instance kvPfxInv_persistent (γk : KVNames) (ps : List (GoString × GName))
    (ok : GoString → mvcc.Change → Prop) (γh : GName) (σ₀ : KVState) :
    Persistent (kvPfxInv (GF := GF) γk ps ok γh σ₀) := by
  unfold kvPfxInv; infer_instance

instance kvPfxH_persistent (γk : KVNames) (p : GoString) (γ : GName) (okp : mvcc.Change → Prop)
    (γh : GName) (σ₀ : KVState) : Persistent (kvPfxH (GF := GF) γk p γ okp γh σ₀) := by
  unfold kvPfxH; infer_instance

instance kvPfx_persistent (γk : KVNames) (p : GoString) (γ : GName) :
    Persistent (kvPfx (GF := GF) γk p γ) := by
  unfold kvPfx; infer_instance

/-- An owner with a discipline that allows every change owns its prefix with none. -/
theorem kvPfx_of_H (γk : KVNames) (p : GoString) (γ : GName) (okp : mvcc.Change → Prop) (γh : GName)
    (σ₀ : KVState) (h : ∀ c, okp c) :
    kvPfxH (GF := GF) γk p γ okp γh σ₀ ⊢ kvPfx γk p γ := by
  iintro #H
  iunfold kvPfxH at H
  icases H with ⟨%ps, %i, %ok, %Hps, #Hinv⟩
  iunfold kvPfx
  iexists γh, σ₀
  iunfold kvPfxH
  iexists ps, i, ok
  iframe Hinv
  ipureintro
  exact ⟨Hps.1, Hps.2.1, fun c => ⟨fun _ => trivial, fun _ => (Hps.2.2 c).2 (h c)⟩⟩

/-- The shared invariant opens inside an owner's (`kvClientN.@s`, `s ≠ "share"`), in an update's mask. -/
theorem kvShareN_mask (s : String) (hs : s ≠ "share") :
    (↑kvShareN : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑(client.kvClientN .@ s) := by
  intro p hp
  rw [Std.LawfulSet.mem_diff]
  exact ⟨client.kvClientN_mask p (nclose_subseteq client.kvClientN "share" p hp),
    fun h => ndot_ne_disjoint client.kvClientN (Ne.symm hs) p ⟨hp, h⟩⟩

/-- The owned prefix's item of the views, and the others'. -/
theorem views_acc (ps : List (GoString × GName)) (i : Nat) (p : GoString) (γ : GName)
    (hi : ps[i]? = some (p, γ)) (σ : KVState) :
    ([∗list] k ↦ e ∈ ps, ghostVar (GF := GF) e.2 (1 : Qp).half (pfxView e.1 σ)) ⊣⊢
      ghostVar γ (1 : Qp).half (pfxView p σ) ∗
        [∗list] k ↦ e ∈ ps, if k = i then emp else ghostVar e.2 (1 : Qp).half (pfxView e.1 σ) :=
  BigSepL.bigSepL_delete_cond hi

/-- The other prefixes' items, at a state whose views of them are the same. -/
theorem views_frame (ps : List (GoString × GName)) (i : Nat) (σ σ' : KVState)
    (h : ∀ (k : Nat) (e : GoString × GName), k ≠ i → ps[k]? = some e →
      pfxView e.1 σ' = pfxView e.1 σ) :
    ([∗list] k ↦ e ∈ ps, if k = i then emp else ghostVar (GF := GF) e.2 (1 : Qp).half (pfxView e.1 σ)) ⊢
      [∗list] k ↦ e ∈ ps, if k = i then emp else ghostVar e.2 (1 : Qp).half (pfxView e.1 σ') := by
  apply BigSepL.bigSepL_mono
  intro k e hk
  by_cases hki : k = i
  · rw [if_pos hki, if_pos hki]
  · rw [if_neg hki, if_neg hki, h k e hki hk]

/-- An update local to the owned prefix leaves the others' views. -/
theorem views_local {ps : List (GoString × GName)} {i : Nat} {p : GoString} {γ : GName}
    (hap : PfxsApart ps) (hi : ps[i]? = some (p, γ)) {f : KVState → KVState} (hf : PfxLocal p f)
    (σ : KVState) :
    ∀ (k : Nat) (e : GoString × GName), k ≠ i → ps[k]? = some e → pfxView e.1 (f σ) = pfxView e.1 σ := by
  intro k e hk he
  exact hf.1 σ e.1 (hap k i e (p, γ) hk he hi) (hap i k (p, γ) e (Ne.symm hk) hi he)

/-- **An owner's update of the KV, fired at most once, reading the history** (F5): `kvPfx_au1`'s, for an
owner under the discipline `okp` (`hok`: the update's changes satisfy it); the step also learns the state's
compaction revision and base, that its changes keep the discipline, and the changes after the update (a lower
bound at `γh`). -/
theorem kvPfx_au1H (γk : KVNames) (p : GoString) (γ : GName) (okp : mvcc.Change → Prop) (γh : GName)
    (σ₀ : KVState) (s : String) (hs : s ≠ "share")
    (W : List EtcdKv → IProp GF) [hW : ∀ v, Timeless (W v)]
    (f : KVState → KVState) (hf : PfxLocal p f)
    (hok : ∀ σ new, (f σ).changes = σ.changes ++ new → ∀ cs ∈ new, ∀ c ∈ cs, okp c)
    (Q : KVState → IProp GF) :
    kvPfxH γk p γ okp γh σ₀ ∗
      inv (client.kvClientN .@ s) iprop(∃ v, ghostVar γ (1 : Qp).half v ∗ W v) ∗
      (∀ σ, ⌜KVExt σ₀ σ ∧ PfxChOk p okp σ.changes⌝ -∗
        monoListLbOwn γh (f σ).changes -∗ W (pfxView p σ) ==∗ W (pfxView p (f σ)) ∗ Q σ) ⊢
    AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
      <{ etcdKV γk (f σ) ∗ ⌜kvRoom σ⌝, COMM Q σ }> := by
  have Hm := client.kvClientN_mask
  have Hm2 := kvShareN_mask s hs
  iintro ⟨#Hpfx, #Hinv, Hstep⟩
  iunfold kvPfxH at Hpfx
  icases Hpfx with ⟨%ps, %i, %ok, %Hps, #Hsh⟩
  obtain ⟨Hap, Hi, Hok⟩ := Hps
  iunfold kvPfxInv at Hsh
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hw Hclosew
  icases Hw with ⟨%v, Hhalf, HW⟩
  iinv Hsh with >Hs Hcloses
  icases Hs with ⟨%σ, Hσ, Hviews, Hh, %Hσok⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hcloses $$ [Hσ Hviews Hh] with -
    · inext; iexists σ; iframe Hσ Hviews Hh; ipureintro; exact Hσok
    imod Hclosew $$ [Hhalf HW] with -
    · inext; iexists v; iframe Hhalf HW
    imodintro
    itrivial
  · iintro ⟨Hσ, %Hroom⟩
    imod Hmask with -
    obtain ⟨hc, hb, new, hnew, hloc⟩ := hf.2 σ
    icases (views_acc ps i p γ Hi σ).1 $$ Hviews with ⟨Hown, Hrest⟩
    ihave %Hv := ghostVar_agree γ v _ (pfxView p σ) _ $$ Hhalf Hown
    subst Hv
    imod (ghostVar_update_halves (pfxView p (f σ)) γ (pfxView p σ) (pfxView p σ)) $$ Hhalf Hown
      with ⟨Hhalf, Hown⟩
    have hpre : σ.changes <+: (f σ).changes := by rw [hnew]; exact List.prefix_append _ _
    imod (monoListAuthOwn_update (f σ).changes hpre) $$ Hh with ⟨Hh, #Hlb⟩
    have hpre' : KVExt σ₀ σ ∧ PfxChOk p okp σ.changes :=
      ⟨Hσok.1, fun cs hcs c hc hpc =>
        (Hok c).1 (Hσok.2 (p, γ) (List.mem_of_getElem? Hi) cs hcs c hc hpc)⟩
    imod Hstep $$ %σ %hpre' Hlb HW with ⟨HW, HQ⟩
    ihave Hrest := views_frame ps i σ (f σ) (views_local Hap Hi hf σ) $$ Hrest
    have hnext : KVExt σ₀ (f σ) ∧ ∀ e ∈ ps, PfxChOk e.1 (ok e.1) (f σ).changes := by
      refine ⟨⟨by rw [hc]; exact Hσok.1.1, by rw [hb]; exact Hσok.1.2.1,
        Hσok.1.2.2.trans hpre⟩, ?_⟩
      rw [hnew]
      exact pfxChOk_step ps ok i p γ Hap Hi σ.changes new hloc
        (fun cs hcs c hc' => (Hok c).2 (hok σ new hnew cs hcs c hc')) Hσok.2
    imod Hcloses $$ [Hσ Hown Hrest Hh] with -
    · inext; iexists (f σ); iframe Hσ Hh
      isplitl [Hown Hrest]
      · iapply (views_acc ps i p γ Hi (f σ)).2
        iframe Hown Hrest
      ipureintro; exact hnext
    imod Hclosew $$ [Hhalf HW] with -
    · inext; iexists (pfxView p (f σ)); iframe Hhalf HW
    imodintro
    iexact HQ

/-- **An owner's update of the KV, fired at most once** (see the file header): from the shared KV, the
owner's invariant over its half and a step of its `W` (local to its prefix), an atomic update of the KV by
`f`, as `KV_Put_dist` takes (`kvAu1`'s). -/
theorem kvPfx_au1 (γk : KVNames) (p : GoString) (γ : GName) (s : String) (hs : s ≠ "share")
    (W : List EtcdKv → IProp GF) [hW : ∀ v, Timeless (W v)]
    (f : KVState → KVState) (hf : PfxLocal p f) (Q : KVState → IProp GF) :
    kvPfx γk p γ ∗ inv (client.kvClientN .@ s) iprop(∃ v, ghostVar γ (1 : Qp).half v ∗ W v) ∗
      (∀ σ, W (pfxView p σ) ==∗ W (pfxView p (f σ)) ∗ Q σ) ⊢
    AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
      <{ etcdKV γk (f σ) ∗ ⌜kvRoom σ⌝, COMM Q σ }> := by
  iintro ⟨#Hpfx, #Hinv, Hstep⟩
  iunfold kvPfx at Hpfx
  icases Hpfx with ⟨%γh, %σ₀, #HpH⟩
  iapply (kvPfx_au1H γk p γ (fun _ => True) γh σ₀ s hs W f hf
    (fun _ _ _ _ _ _ _ => trivial) Q)
  isplitr
  · iexact HpH
  isplitr
  · iexact Hinv
  iintro %σ %_hpre _Hlb HW
  iapply Hstep $$ HW

/-- **An owner's persistent read update of the KV** (see the file header): from the shared KV, the
owner's invariant over its half and a persistent read of its `W`, `kvReadAu` (`KV_Get_dist`'s). -/
theorem kvPfx_readAu (γk : KVNames) (p : GoString) (γ : GName) (s : String) (hs : s ≠ "share")
    (W : List EtcdKv → IProp GF) [hW : ∀ v, Timeless (W v)] (Q : KVState → IProp GF) :
    kvPfx γk p γ ∗ inv (client.kvClientN .@ s) iprop(∃ v, ghostVar γ (1 : Qp).half v ∗ W v) ∗
      □ (∀ σ, W (pfxView p σ) ==∗ W (pfxView p σ) ∗ □ Q σ) ⊢
    kvReadAu γk Q := by
  have Hm := client.kvClientN_mask
  have Hm2 := kvShareN_mask s hs
  iintro ⟨#Hpfx, #Hinv, #Hstep⟩
  iunfold kvPfx at Hpfx
  icases Hpfx with ⟨%γh, %σ₀, #HpH⟩
  iunfold kvPfxH at HpH
  icases HpH with ⟨%ps, %i, %ok, %Hps, #Hsh⟩
  obtain ⟨Hap, Hi, -⟩ := Hps
  iunfold kvPfxInv at Hsh
  iunfold kvReadAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hw Hclosew
  icases Hw with ⟨%v, Hhalf, HW⟩
  iinv Hsh with >Hs Hcloses
  icases Hs with ⟨%σ, Hσ, Hviews, Hh, %Hσok⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hcloses $$ [Hσ Hviews Hh] with -
    · inext; iexists σ; iframe Hσ Hviews Hh; ipureintro; exact Hσok
    imod Hclosew $$ [Hhalf HW] with -
    · inext; iexists v; iframe Hhalf HW
    imodintro
    itrivial
  · iintro ⟨Hσ, %Hroom⟩
    imod Hmask with -
    icases (views_acc ps i p γ Hi σ).1 $$ Hviews with ⟨Hown, Hrest⟩
    ihave %Hv := ghostVar_agree γ v _ (pfxView p σ) _ $$ Hhalf Hown
    subst Hv
    imod Hstep $$ HW with ⟨HW, #HQ⟩
    imod Hcloses $$ [Hσ Hown Hrest Hh] with -
    · inext; iexists σ; iframe Hσ Hh
      isplitl [Hown Hrest]
      · iapply (views_acc ps i p γ Hi σ).2
        iframe Hown Hrest
      ipureintro; exact Hσok
    imod Hclosew $$ [Hhalf HW] with -
    · inext; iexists (pfxView p σ); iframe Hhalf HW
    imodintro
    iintro !>
    iexact HQ

/-- **An owner's persistent read update of the KV, reading the history** (F5): `kvPfx_readAu`'s, the step
also learning that the state's changes extend `l0` (a lower bound the caller has), its compaction revision
and base, that its changes keep the owner's discipline, and their lower bound. -/
theorem kvPfx_readAuH (γk : KVNames) (p : GoString) (γ : GName) (okp : mvcc.Change → Prop) (γh : GName)
    (σ₀ : KVState) (s : String) (hs : s ≠ "share")
    (W : List EtcdKv → IProp GF) [hW : ∀ v, Timeless (W v)] (l0 : List (List mvcc.Change))
    (Q : KVState → IProp GF) :
    kvPfxH γk p γ okp γh σ₀ ∗
      inv (client.kvClientN .@ s) iprop(∃ v, ghostVar γ (1 : Qp).half v ∗ W v) ∗
      monoListLbOwn γh l0 ∗
      □ (∀ σ, ⌜l0 <+: σ.changes ∧ KVExt σ₀ σ ∧ PfxChOk p okp σ.changes⌝ -∗
        monoListLbOwn γh σ.changes -∗ W (pfxView p σ) ==∗ W (pfxView p σ) ∗ □ Q σ) ⊢
    kvReadAu γk Q := by
  have Hm := client.kvClientN_mask
  have Hm2 := kvShareN_mask s hs
  iintro ⟨#Hpfx, #Hinv, #Hl0, #Hstep⟩
  iunfold kvPfxH at Hpfx
  icases Hpfx with ⟨%ps, %i, %ok, %Hps, #Hsh⟩
  obtain ⟨Hap, Hi, Hok⟩ := Hps
  iunfold kvPfxInv at Hsh
  iunfold kvReadAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hw Hclosew
  icases Hw with ⟨%v, Hhalf, HW⟩
  iinv Hsh with >Hs Hcloses
  icases Hs with ⟨%σ, Hσ, Hviews, Hh, %Hσok⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hcloses $$ [Hσ Hviews Hh] with -
    · inext; iexists σ; iframe Hσ Hviews Hh; ipureintro; exact Hσok
    imod Hclosew $$ [Hhalf HW] with -
    · inext; iexists v; iframe Hhalf HW
    imodintro
    itrivial
  · iintro ⟨Hσ, %Hroom⟩
    imod Hmask with -
    ihave %Hp := mono_list_auth_lb_valid (GF := GF) γh 1 σ.changes l0 $$ Hh Hl0
    ihave #Hlb := monoListLbOwn_get γh 1 σ.changes $$ Hh
    icases (views_acc ps i p γ Hi σ).1 $$ Hviews with ⟨Hown, Hrest⟩
    ihave %Hv := ghostVar_agree γ v _ (pfxView p σ) _ $$ Hhalf Hown
    subst Hv
    have hpre' : l0 <+: σ.changes ∧ KVExt σ₀ σ ∧ PfxChOk p okp σ.changes :=
      ⟨Hp.2, Hσok.1, fun cs hcs c hc hpc =>
        (Hok c).1 (Hσok.2 (p, γ) (List.mem_of_getElem? Hi) cs hcs c hc hpc)⟩
    imod Hstep $$ %σ %hpre' Hlb HW with ⟨HW, #HQ⟩
    imod Hcloses $$ [Hσ Hown Hrest Hh] with -
    · inext; iexists σ; iframe Hσ Hh
      isplitl [Hown Hrest]
      · iapply (views_acc ps i p γ Hi σ).2
        iframe Hown Hrest
      ipureintro; exact Hσok
    imod Hclosew $$ [Hhalf HW] with -
    · inext; iexists (pfxView p σ); iframe Hhalf HW
    imodintro
    iintro !>
    iexact HQ

/-- `n` ghost variables at `[]`, each whole. -/
theorem ghostVars_alloc (n : Nat) :
    ⊢ |==> ∃ γs : List GName, ⌜γs.length = n⌝ ∗
      [∗list] γ ∈ γs, ghostVar (GF := GF) γ 1 ([] : List EtcdKv) := by
  induction n with
  | zero =>
    imodintro
    iexists []
    isplitr
    · ipureintro; rfl
    · iapply BigSepL.bigSepL_nil.2
      itrivial
  | succ n ih =>
    ihave H := ih
    imod H with ⟨%γs, %hl, Hs⟩
    imod (ghostVar_alloc (GF := GF) ([] : List EtcdKv)) with Hγ
    icases Hγ with ⟨%γ, Hγ⟩
    imodintro
    iexists γ :: γs
    isplitr
    · ipureintro; simp [hl]
    · iapply BigSepL.bigSepL_cons.2
      iframe Hγ Hs

/-- **The start's allocation of the shared KV** (see the file header): from the cluster's client half at
a state with no key-value and no change, for prefixes `pfxs` none a prefix of another and each prefix's
discipline `ok` (F5), the shared invariant, the history's name `γh` with a lower bound of the start's
changes, and, for each prefix, its name `γ` (`kvPfxH`, at the start's compaction revision and base) and the
owner's half at `[]`. -/
theorem kvPfx_alloc (γk : KVNames) (σ₀ : KVState) (h0 : σ₀.kvs = [])
    (hc0 : ∀ cs ∈ σ₀.changes, cs = []) (pfxs : List GoString)
    (hap : ∀ (i j : Nat) (a b : GoString), i ≠ j → pfxs[i]? = some a → pfxs[j]? = some b → ¬ a <+: b)
    (ok : GoString → mvcc.Change → Prop) (E : CoPset) :
    etcdKV (GF := GF) γk σ₀ ={E}=∗ ∃ (γh : GName) (γs : List GName), ⌜γs.length = pfxs.length⌝ ∗
      monoListLbOwn γh σ₀.changes ∗
      [∗list] e ∈ pfxs.zip γs, kvPfxH γk e.1 e.2 (ok e.1) γh σ₀ ∗
        ghostVar e.2 (1 : Qp).half ([] : List EtcdKv) := by
  iintro Hσ
  ihave H := ghostVars_alloc (GF := GF) pfxs.length
  imod H with ⟨%γs, %hl, Hs⟩
  imod (mono_list_own_alloc (GF := GF) σ₀.changes) with ⟨%γh, Hh, #Hlb⟩
  have hv : ∀ p : GoString, pfxView p σ₀ = [] := by
    intro p; unfold pfxView; rw [h0]; rfl
  -- each whole variable as two halves: the invariant's and the owner's
  have hz : (pfxs.zip γs).map Prod.snd = γs := by
    rw [List.map_snd_zip]; omega
  have hconv : ([∗list] γ ∈ γs, ghostVar (GF := GF) γ 1 ([] : List EtcdKv)) ⊢
      [∗list] e ∈ pfxs.zip γs, ghostVar (GF := GF) e.2 (1 : Qp).half (pfxView e.1 σ₀) ∗
        ghostVar e.2 (1 : Qp).half ([] : List EtcdKv) := by
    conv => lhs; rw [← hz]
    rw [BigSepL.bigSepL_map]
    apply BigSepL.bigSepL_mono
    intro k e _
    rw [hv]
    exact (ghostVar_split_half (GF := GF) e.2 1 ([] : List EtcdKv)).1
  ihave Hs2 := hconv $$ Hs
  icases (BigSepL.bigSepL_sep_eqv).1 $$ Hs2 with ⟨Hinvs, Hown⟩
  have hap' : PfxsApart (pfxs.zip γs) := by
    intro i j a b hij ha hb
    have ha' := List.getElem?_zip_eq_some.1 ha
    have hb' := List.getElem?_zip_eq_some.1 hb
    exact hap i j a.1 b.1 hij ha'.1 hb'.1
  have hok0 : KVExt σ₀ σ₀ ∧ ∀ e ∈ pfxs.zip γs, PfxChOk e.1 (ok e.1) σ₀.changes :=
    ⟨⟨rfl, rfl, List.prefix_refl _⟩, fun _ _ cs hcs c hc _ => by rw [hc0 cs hcs] at hc; simp at hc⟩
  imod (inv_alloc kvShareN E iprop(∃ σ : KVState, etcdKV (GF := GF) γk σ ∗
      ([∗list] _k ↦ e ∈ pfxs.zip γs, ghostVar e.2 (1 : Qp).half (pfxView e.1 σ)) ∗
      monoListAuthOwn γh 1 σ.changes ∗
      ⌜KVExt σ₀ σ ∧ ∀ e ∈ pfxs.zip γs, PfxChOk e.1 (ok e.1) σ.changes⌝)) $$ [Hσ Hinvs Hh] with #Hinv
  · inext; iexists σ₀; iframe Hσ Hinvs Hh; ipureintro; exact hok0
  have hall : □ kvPfxInv (GF := GF) γk (pfxs.zip γs) ok γh σ₀ ⊢
      [∗list] e ∈ pfxs.zip γs, kvPfxH (GF := GF) γk e.1 e.2 (ok e.1) γh σ₀ := by
    apply BigSepL.bigSepL_intro
    intro k e he
    iintro #Hinv'
    iunfold kvPfxH
    iexists (pfxs.zip γs), k, ok
    isplitr
    · ipureintro
      exact ⟨hap', by rw [he], fun _ => Iff.rfl⟩
    iexact Hinv'
  ihave #HinvP : kvPfxInv (GF := GF) γk (pfxs.zip γs) ok γh σ₀ $$ []
  · iunfold kvPfxInv
    iexact Hinv
  ihave Hall := hall $$ HinvP
  imodintro
  iexists γh, γs
  isplitr
  · ipureintro; exact hl
  iframe Hlb
  iapply (BigSepL.bigSepL_sep_eqv).2
  isplitl [Hall]
  · iexact Hall
  · iexact Hown
end ghost

section seen
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A revision the cluster's KV has reached is at most the shared state's** (F5; `kv_revLbZ_le` over the
shared invariant, outside every update): with the KV invariant, a reached revision `n` (`kvRevLbZ`) gives a
lower bound of the state's changes whose revision (the start's compaction revision plus their number) is at least `n`, so every read that
fires later (`kvPfx_readAuH` at that bound) reads at a revision at least `n`. -/
theorem kvPfx_seen [go_etcd_io.raft.v3.Assumptions] (γk : KVNames) (p : GoString) (γ : GName)
    (okp : mvcc.Change → Prop) (γh : GName) (σ₀ : KVState) (γr : ServerRaftNames)
    (n : Int) :
    ⊢ kvPfxH (GF := GF) (Gg := hG.goose_globalGS) γk p γ okp γh σ₀ -∗ kvInv γr γk -∗ kvRevLbZ γk n ={⊤}=∗
      ∃ l : List (List mvcc.Change), monoListLbOwn γh l ∗
        ⌜n ≤ ((σ₀.compacted + l.length : Nat) : Int)⌝ := by
  iintro #Hpfx #Hkv #Hlb
  iunfold kvPfxH at Hpfx
  icases Hpfx with ⟨%ps, %i, %ok, -, #Hsh⟩
  iunfold kvPfxInv at Hsh
  iinv Hsh with >Hs Hcloses
  icases Hs with ⟨%σ, Hσ, Hviews, Hh, %Hσok⟩
  have hE : (↑kvN : CoPset) ⊆ ⊤ \ ↑kvShareN := by
    intro x hx
    rw [Std.LawfulSet.mem_diff]
    refine ⟨CoPset.mem_full, fun h => ?_⟩
    have h2 := client.kvClientN_mask x (nclose_subseteq client.kvClientN "share" x h)
    rw [Std.LawfulSet.mem_diff] at h2
    exact h2.2 hx
  imod (kv_revLbZ_le γr γk (⊤ \ ↑kvShareN) hE n σ) $$ Hkv Hlb Hσ with ⟨Hσ, %Hn⟩
  ihave #Hl := monoListLbOwn_get γh 1 σ.changes $$ Hh
  imod Hcloses $$ [Hσ Hviews Hh] with -
  · inext; iexists σ; iframe Hσ Hviews Hh; ipureintro; exact Hσok
  imodintro
  iexists σ.changes
  iframe Hl
  ipureintro
  rw [← Hσok.1.rev_eq]; exact Hn

end seen

end etcd_dist
end EtcdGrove
end Perennial

end
