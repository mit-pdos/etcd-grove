/-
U7j (`notes/bbolt-proof-plan.md`): `DeleteBucket`'s generations. The view `T.dropBkt n` bumps
`n`'s generation, so every handle of `n` (at most `T.gen n`, `gensOK`'s first clause) is stale:
- `gensOK_dropBkt`: `gensOK` kept when the root bucket's cache loses `n` and keeps every other name;
- `gensD1_dropBkt`: the same for the clause "a handle at its name's current generation is that
  name's opened bucket" (`∀ b n, X.handles !! b = some (n, T.gen n) → bktLoc X n = some b`,
  maintainer 14's third clause of `gensOK`, D1), stated on its own until it lands.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Tx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section delbkt
variable [GooseExts]

/-- `gensOK`'s third clause (D1, maintainer 14): a handle at its name's current generation is the
name's opened bucket. -/
def gensD1 (T : TxView) (X : WX) : Prop :=
  ∀ b n, X.handles !! b = some (n, T.gen n) → bktLoc X n = some b

/-- **`DeleteBucket`'s generations** (`gensOK`'s two clauses): the root's cache loses `n` and keeps
the others, the handles kept. -/
theorem gensOK_dropBkt (T : TxView) (X X' : WX) (n : GoString) (hh : X'.handles = X.handles)
    (hloc : ∀ m, m ≠ n → bktLoc X' m = bktLoc X m) (hn : bktLoc X' n = none)
    (h : gensOK T X) : gensOK (T.dropBkt n) X' := by
  refine ⟨fun b m g hb => ?_, fun m b hb => ?_⟩
  · rw [hh] at hb
    have := h.1 b m g hb
    simp only [TxView.dropBkt]
    split
    · rename_i e; subst e; omega
    · exact this
  · have hm : m ≠ n := by intro e; subst e; rw [hn] at hb; cases hb
    rw [hloc m hm] at hb
    rw [hh, h.2 m b hb]
    simp [TxView.dropBkt, hm]

/-- **`DeleteBucket`'s generations** (the third clause, D1): a handle of `n` is stale after the
bump, the others' names keep their buckets. -/
theorem gensD1_dropBkt (T : TxView) (X X' : WX) (n : GoString) (hh : X'.handles = X.handles)
    (hloc : ∀ m, m ≠ n → bktLoc X' m = bktLoc X m) (h : gensOK T X) (hd : gensD1 T X) :
    gensD1 (T.dropBkt n) X' := by
  intro b m hb
  rw [hh] at hb
  by_cases hm : m = n
  · subst hm
    have := h.1 b m _ hb
    simp [TxView.dropBkt] at this
    omega
  · rw [hloc m hm]
    apply hd b m
    rw [hb]; simp [TxView.dropBkt, hm]

end delbkt

end Write

end bbolt
end EtcdGrove
end Perennial
