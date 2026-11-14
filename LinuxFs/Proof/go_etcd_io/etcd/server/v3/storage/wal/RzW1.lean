/- Lean-first (no Rocq counterpart).

# W1 across a resize's zeros (I3b, `wal-tc5`; pure)

A truncate announces the bytes it cuts off with the zero stamped by its change number `n`
(`rsAnn`), and `n` is among the resize stamps the layout's `OsMeta` knows (`rzMeta`, `rsPostK true`;
`segRzOf`). W1's change disjunct (`AsOfW`) excludes a candidate of a known resize stamp, so W1 over
the bytes with the zero appended gives W1 over the bytes without it: a frame as of a change at or
after `n` would read the truncate's zero (excluded), one as of a change before `n` reads what the
bytes had before (`latestAt_append_lt`), and as of the last sync the zero stamped `n > 0` is not
read (`valAt_append_pos`).

* `AsOfW.drop_rz`, `W1G.drop_rz`: the transport from the window's bytes to the exact tail's.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Abs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

theorem latestAt_append_lt (c : Cands) (x : w8) {n k : Nat} (hk : k < n) :
    latestAt (c ++ [(x, n)]) k = latestAt c k := by
  simp [latestAt, List.filter_append, show ¬ n ≤ k by omega]

theorem valAt_append_pos (c : Cands) (x : w8) {n : Nat} (hn : 0 < n) :
    valAt (c ++ [(x, n)]) 0 = valAt c 0 := by
  rw [valAt_latestAt, valAt_latestAt, latestAt_append_lt c x hn]

/-- A byte's candidates `cs' b`: those of `cs b`, or those with a resize's zero appended, its stamp
`n > 0` among the resize stamps `rz`. -/
def RzCands (rz : List Nat) (cs cs' : Cands) : Prop :=
  cs' = cs ∨ ∃ n, 0 < n ∧ n ∈ rz ∧ cs' = cs ++ [(0, n)]

/-- **W1 over the candidates with a known resize's zeros appended gives W1 without them.** -/
theorem AsOfW.drop_rz {cs cs' : Nat → Cands} {rz : List Nat} {v : Nat → w8} {o len : Nat}
    (hc : ∀ b, o ≤ b → b < o + len → RzCands rz (cs b) (cs' b))
    (h : AsOfW cs' rz v o len) : AsOfW cs rz v o len := by
  rcases h with h | ⟨k, hk, h⟩
  · left; intro b h1 h2
    rw [h b h1 h2]
    rcases hc b h1 h2 with e | ⟨n, hn, -, e⟩
    · rw [e]
    · rw [e, valAt_append_pos _ _ hn]
  · right; refine ⟨k, hk, fun b h1 h2 => ?_⟩
    obtain ⟨p, hp, hv, hp0, hpr⟩ := h b h1 h2
    rcases hc b h1 h2 with e | ⟨n, hn, hnr, e⟩
    · rw [e] at hp; exact ⟨p, hp, hv, hp0, hpr⟩
    · rw [e] at hp
      by_cases hnk : n ≤ k
      · rw [latestAt_append_last _ _ hnk] at hp
        cases hp; exact absurd hnr hpr
      · rw [latestAt_append_lt _ _ (by omega)] at hp
        exact ⟨p, hp, hv, hp0, hpr⟩

/-- **`W1G` over a layout's bytes with known resizes' zeros appended gives `W1G` over the bytes
without them** (same lengths). -/
theorem W1G.drop_rz {C : WalCodec} {js : List Ino} {img : Ino → List w8}
    {bsOf bsOf' : Ino → Option (List ByteG)} {rzOf : Ino → List Nat}
    (h : W1G C js img bsOf' rzOf)
    (hb : ∀ i bs, bsOf i = some bs → ∃ bs', bsOf' i = some bs' ∧ bs'.length = bs.length ∧
      ∀ b, b < bs.length → RzCands (rzOf i) (bs.getD b (0, [])).2 (bs'.getD b (0, [])).2) :
    W1G C js img bsOf rzOf := by
  intro k p hp i bs hi hbs hsz
  obtain ⟨bs', hbs', hl, hc⟩ := hb i bs hbs
  have h1 := h k p hp i bs' hi hbs' (by rw [hl]; exact hsz)
  exact AsOfW.drop_rz (fun b h1 h2 => hc b (by omega)) h1

end WalFs
end EtcdGrove
end Perennial

end
