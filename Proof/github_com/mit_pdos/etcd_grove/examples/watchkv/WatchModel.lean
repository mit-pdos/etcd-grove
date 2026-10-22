/-
**The watch's steps at a watchkv server, pure** (D23, 2026-10-20). Lean-first (no Rocq
counterpart).

In a watchkv log (`WkLog`) whose plan's keys are all under the prefix, revisions `0` and `1` have
no event under it (`revEvs_low`) and each later one has exactly one, the put of its key and value
(`revEvs_hi`). So a step of etcd's history (`srvStep`'s facts) from the watch's position `prev`
after `n` events (`Cur n prev`: `prev ≤ 1` before the first event, then the last event's
revision `1 + n`) to a revision with events is to revision `2 + n`, with that put's one event
(`step_wk`); and a step without events stays at the position or, before the first event, at
most at `1` (`prog_wk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Workload
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WatchBase
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ClientLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [ext : FfiSyntax]

/- **The watch's position after `n` events** (`common.Cur`). -/
export common (Cur Cur_zero)

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
  -- `r1 ≥ 2`: revisions below have no event
  have h2 : 2 ≤ sint.Z r1 := by
    refine Classical.byContradiction fun hc => hne ?_
    exact revEvs_low h pfx _ (by omega)
  -- nothing at `2 ≤ x < r1`: so `r1 - 1 ≤ max prev 1`
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

end pure

end watchkv
end EtcdGrove
end Perennial
