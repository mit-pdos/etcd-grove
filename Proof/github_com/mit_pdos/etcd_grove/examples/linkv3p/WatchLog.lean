/-
**The watch workload's logs, pure** (2026-10-26, D44/D46/D47: linkv3p's own facts about etcd's KV
state, kept in the adapter's invariant as its application property `γ.W`, instead of watchkv's
server workload). Lean-first (no Rocq counterpart).

watchkv's `Workload.lean` (`wkRev`, `WkLog`) and `WatchModel.lean` (`revEvs_low`, `revEvs_hi`,
`step_wk`, `prog_wk`), copied: watchkv's server workload is gone (D44) and watchkv's proof is redone
separately, so linkv3p does not rest on its files.

* `WkLog P L`: revisions `0` and `1` of `L` have no change, every later one is one put of the plan
  `P` (no lease).
* `wkW P ch`: the KV state's changes `ch` (revisions `1, 2, ...`) are a watchkv log's after
  revision `0` (`WkLog P ([] :: ch)`), and revision `1` is there: the application property the
  example's adapter keeps (`KMNames.W`). The start's changes have it (`wkW_start`); a put of the
  plan keeps it (`wkW_put`, `kvOpStep_putKeyOp`).
* `step_wk`, `prog_wk`: a step of etcd's history at a watchkv log, from the watch's position after
  `n` events (`common.Cur`), to a revision with events is to `2 + n`, with that put's one event;
  a step without events stays or, before the first event, is at most at `1`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.WatchBase
public import Proof.go_etcd_io.etcd.client.v3.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [ext : FfiSyntax]

export common (Cur Cur_zero)

/-- A revision from `2` on: one put of the plan, no lease. -/
def wkRev (P : List (GoString × GoString)) (cs : List mvcc.Change) : Prop :=
  ∃ k v, (k, v) ∈ P ∧ cs = [.put k v (W64 0)]

/-- **A watchkv log**: its first two revisions empty, every later one a put of the plan. -/
def WkLog (P : List (GoString × GoString)) (L : mvcc.Log) : Prop :=
  (∀ j cs, j < 2 → L[j]? = some cs → cs = []) ∧ ∀ j cs, 2 ≤ j → L[j]? = some cs → wkRev P cs

theorem WkLog.prefix {P : List (GoString × GoString)} {L L' : mvcc.Log} (h : WkLog P L)
    (hp : L' <+: L) : WkLog P L' := by
  obtain ⟨r, rfl⟩ := hp
  refine ⟨fun j cs hj hc => h.1 j cs hj ?_, fun j cs hj hc => h.2 j cs hj ?_⟩ <;>
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hc).1] <;> exact hc

/-- The start log is a watchkv log. -/
theorem WkLog.start (P : List (GoString × GoString)) : WkLog P [[], []] := by
  refine ⟨fun j cs _ h => ?_, fun j cs hj h => ?_⟩
  · rcases j with _ | _ | j <;> simp at h <;> exact h
  · rcases j with _ | _ | j
    · omega
    · omega
    · simp at h

/-- One revision more. -/
theorem WkLog.snoc {P : List (GoString × GoString)} {L : mvcc.Log} {cs : List mvcc.Change}
    (h : WkLog P L) (hl : 2 ≤ L.length) (hc : wkRev P cs) : WkLog P (L ++ [cs]) := by
  refine ⟨fun j c hj hj' => h.1 j c hj ?_, fun j c hj hj' => ?_⟩
  · rw [List.getElem?_append_left (by omega)] at hj'; exact hj'
  · rcases Nat.lt_or_ge j L.length with hjl | hjl
    · rw [List.getElem?_append_left hjl] at hj'; exact h.2 j c hj hj'
    · rw [List.getElem?_append_right hjl] at hj'
      have : j - L.length = 0 := by
        have := (List.getElem?_eq_some_iff.mp hj').1; simp at this; omega
      rw [this] at hj'; simp at hj'; subst hj'; exact hc

/-- **The example's property of the KV state's changes** (see the file header). -/
def wkW (P : List (GoString × GoString)) (ch : List (List mvcc.Change)) : Prop :=
  WkLog P ([] :: ch) ∧ ch ≠ []

/-- A prefix of the changes, revision `1` included, keeps it. -/
theorem wkW.prefix {P : List (GoString × GoString)} {ch ch' : List (List mvcc.Change)}
    (h : wkW P ch) (hp : ch' <+: ch) : WkLog P ([] :: ch') := by
  refine h.1.prefix ?_
  obtain ⟨t, rfl⟩ := hp
  exact ⟨t, rfl⟩

/-- The start's changes (revision `1`, empty). -/
theorem wkW_start (P : List (GoString × GoString)) : wkW P [[]] :=
  ⟨WkLog.start P, by simp⟩

/-- **The client's put of `k ↦ v`** (no lease, no flag) commits the one change `put k v 0`. -/
theorem kvOpStep_putKeyOp (k v : GoString) (σ : KVState) :
    kvOpStep (.put (client.putKeyOp k v)) σ = σ.commit [.put k v (W64 0)] := by
  simp [kvOpStep, client.putKeyOp, txn.putOpOf, txn.needsPrev, txn.putChangeOf, txn.putValOf,
    txn.putLeaseOf]

/-- A put of the plan keeps the property. -/
theorem wkW_put (P : List (GoString × GoString)) (k v : GoString) (hkv : (k, v) ∈ P)
    (σ : KVState) (h : wkW P σ.changes) :
    wkW P (kvOpStep (.put (client.putKeyOp k v)) σ).changes := by
  rw [kvOpStep_putKeyOp]
  simp only [KVState.commit, List.cons_ne_nil, ↓reduceIte]
  refine ⟨?_, by simp⟩
  have hl : 2 ≤ ([] :: σ.changes : mvcc.Log).length := by
    have := List.length_pos_iff.2 h.2; simp; omega
  have := h.1.snoc hl ⟨k, v, hkv, rfl⟩
  simpa using this

/-- Revisions `0` and `1` of a watchkv log have no event. -/
theorem revEvs_low {P : List (GoString × GoString)} {L : mvcc.Log} (h : WkLog P L)
    (pfx : GoString) (x : Nat) (hx : x < 2) : txn.revEvs L pfx x = [] := by
  unfold txn.revEvs
  cases hL : L[x]? with
  | none => simp [txn.evsUnder]
  | some cs =>
    rw [h.1 x cs hx hL]
    simp [txn.evsUnder]

/-- A later revision of a watchkv log, whose plan's keys are under the prefix, has the one event
of its put. -/
theorem revEvs_hi {P : List (GoString × GoString)} {L : mvcc.Log} (h : WkLog P L)
    (pfx : GoString) (hpk : ∀ kv ∈ P, pfx <+: kv.1) (x : Nat) (hx2 : 2 ≤ x)
    (hxl : x < L.length) :
    ∃ k v, (k, v) ∈ P ∧ L[x]? = some [mvcc.Change.put k v (W64 0)] ∧
      txn.revEvs L pfx x =
        [txn.changeEv (W64 (x : Int)) (mvcc.stateAt L (x - 1)) (mvcc.Change.put k v (W64 0))] := by
  have hx : L[x]? = some L[x] := List.getElem?_eq_getElem hxl
  obtain ⟨k, v, hkv, hcs⟩ := h.2 x L[x] hx2 hx
  refine ⟨k, v, hkv, by rw [hx, hcs], ?_⟩
  unfold txn.revEvs
  rw [hx, hcs]
  have hp : pfx <+: k := hpk (k, v) hkv
  simp [txn.evsUnder, mvcc.Change.key, hp]

/-- **A step to a revision with events** (see the file header). -/
theorem step_wk {P : List (GoString × GoString)} {L : mvcc.Log} (h : WkLog P L)
    (pfx : GoString) (hpk : ∀ kv ∈ P, pfx <+: kv.1) (n : Nat) (prev r1 : w64)
    (hcur : Cur n prev) (hlt : sint.Z prev < sint.Z r1) (hr1 : sint.Z r1 < L.length)
    (hnone : ∀ x : Nat, sint.Z prev < x → x < sint.Z r1 → txn.revEvs L pfx x = [])
    (hne : txn.revEvs L pfx (sint.Z r1).toNat ≠ []) :
    sint.Z r1 = 2 + n ∧ ∃ k v, (k, v) ∈ P ∧ L[2 + n]? = some [mvcc.Change.put k v (W64 0)] ∧
      txn.revEvs L pfx (sint.Z r1).toNat =
        [txn.changeEv (W64 ((2 + n : Nat) : Int)) (mvcc.stateAt L (1 + n))
          (mvcc.Change.put k v (W64 0))] := by
  have h0 : 0 ≤ sint.Z prev := by rcases hcur with ⟨-, h, -⟩ | ⟨-, h⟩ <;> omega
  have h2 : 2 ≤ sint.Z r1 := by
    refine Classical.byContradiction fun hc => hne ?_
    exact revEvs_low h pfx _ (by omega)
  have hle : ∀ x : Nat, 2 ≤ x → (x : Int) < sint.Z r1 → (x : Int) ≤ sint.Z prev := by
    intro x hx2 hx
    refine Classical.byContradiction fun hc => ?_
    obtain ⟨k, v, -, -, he⟩ := revEvs_hi h pfx hpk x hx2 (by omega)
    have := hnone x (by omega) hx
    rw [he] at this
    simp at this
  have hr : sint.Z r1 = 2 + n := by
    rcases hcur with ⟨rfl, -, hp1⟩ | ⟨hn, hp⟩
    · refine Classical.byContradiction fun hc => ?_
      have := hle 2 (Nat.le_refl _) (by omega)
      omega
    · refine Classical.byContradiction fun hc => ?_
      have := hle (sint.Z prev + 1).toNat (by omega) (by omega)
      omega
  refine ⟨hr, ?_⟩
  obtain ⟨k, v, hkv, hL, he⟩ := revEvs_hi h pfx hpk (2 + n) (by omega) (by omega)
  refine ⟨k, v, hkv, hL, ?_⟩
  rw [show (sint.Z r1).toNat = 2 + n by omega, he]
  simp only [show 2 + n - 1 = 1 + n by omega]

/-- **A step without events** (see the file header). -/
theorem prog_wk {P : List (GoString × GoString)} {L : mvcc.Log} (h : WkLog P L)
    (pfx : GoString) (hpk : ∀ kv ∈ P, pfx <+: kv.1) (n : Nat) (c p : w64)
    (hcur : Cur n c) (hle : sint.Z c ≤ sint.Z p) (hp : sint.Z p < L.length)
    (hnone : txn.revEvs L pfx (sint.Z p).toNat = []) :
    c = p ∨ Cur n p := by
  have hp1 : sint.Z p ≤ 1 := by
    refine Classical.byContradiction fun hc => ?_
    obtain ⟨k, v, -, -, he⟩ := revEvs_hi h pfx hpk (sint.Z p).toNat (by omega) (by omega)
    rw [he] at hnone
    simp at hnone
  rcases hcur with ⟨rfl, h0, -⟩ | ⟨hn, hc⟩
  · right; left; exact ⟨rfl, by omega, hp1⟩
  · omega

theorem putNv_value (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) :
    (txn.putNv r k val l s).value = val := by
  unfold txn.putNv
  cases s.find? (fun v => decide (v.key = k)) <;> rfl

theorem putNv_modRev (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) :
    (txn.putNv r k val l s).modRev = r := by
  unfold txn.putNv
  cases s.find? (fun v => decide (v.key = k)) <;> rfl

end pure

end linkv3p
end EtcdGrove
end Perennial
