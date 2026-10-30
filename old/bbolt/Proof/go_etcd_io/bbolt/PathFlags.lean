/-
The entries with a key at the end of a cursor's path: what ties `Cursor.seek`'s result to the
leaf `Cursor.node` returns, for `Put`/`Delete`'s check that the key is not a nested bucket's
(`ErrIncompatibleValue`).

`keySrcIs W B k kbs`: the key `k` a writer's cursor returned is where `keySrcOK` says, and its
bytes are `kbs`. `posKey W B pid k P`: every entry with key `k` of position `pid` (its node's,
or its page's) has flags satisfying `P`. `pathKey W B k P pid es`: so has the position the
stack `es` (from `pid` down) ends at. The search puts the leaf's index at the first entry not
below `k` (the entries increase), and `keyValue` returns that entry, so after `seek(kb)` an
entry with key `kb` of the leaf is the one returned: its flags are the flags returned, and the
key returned has the bytes `kb` (`Cursor.seek.sspec`).
-/
module

public import Proof.go_etcd_io.bbolt.WriteCursorLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section flags
variable [ext : FfiSyntax]

/-- The key `k` a writer's cursor returned (`keySrcOK`), with the bytes `kbs`. -/
def keySrcIs (W : WView) (B : BRec) (k : GoSlice) (kbs : List w8) : Prop :=
  (k = slice.nil ∧ kbs = []) ∨
  (∃ (l : Loc) (r : NRec) (i : Nat) (it : Inode) (w : WEntry), B.ns !! l = some r ∧
    r.ins[i]? = some it ∧ r.ws[i]? = some w ∧ it.key' = k ∧ w.ks ≠ Src.stale ∧ w.key = kbs) ∨
  (∃ (pid : w64) (p : Loc) (pg : List w8) (off n : Nat), wpageAt W B pid = some (p, pg) ∧
    (B.ib.root' = W64 0 → B.bv.page' ≠ null ∧ B.isrc ≠ Src.stale) ∧ 16 ≤ pg.length ∧
    off + n ≤ pg.length ∧ n < 2 ^ 32 ∧ k = sliceAt p off n ∧ bytesAt pg off n = kbs)

/-- Every entry with key `k` of position `pid` has flags satisfying `P`. -/
def posKey (W : WView) (B : BRec) (pid : w64) (k : List w8) (P : w32 → Prop) : Prop :=
  (∀ l r, resolve B pid = some l → B.ns !! l = some r → ∀ w ∈ r.ws, w.key = k → P w.flags) ∧
  (resolve B pid = none → ∀ lp, wpageAt W B pid = some lp →
    ∀ i < pageCount lp.2, leafKey lp.2 i = k → P (W32 (leafFlags lp.2 i : Int)))

/-- Every entry with key `k` of the position the stack elements `es` (from `pid` down) end at
has flags satisfying `P`. -/
def pathKey (W : WView) (B : BRec) (k : List w8) (P : w32 → Prop) : w64 → List elemRef → Prop
  | _, [] => False
  | pid, [_] => posKey W B pid k P
  | pid, r :: r2 :: rs => ∃ cs c, kidsAt W B pid = some (false, cs) ∧
      cs[(sint.Z r.index').toNat]? = some c ∧ pathKey W B k P c (r2 :: rs)

theorem keySrcIs_ok (W : WView) (B : BRec) (k : GoSlice) (kbs : List w8)
    (h : keySrcIs W B k kbs) : keySrcOK W B k := by
  rcases h with ⟨rfl, -⟩ | ⟨l, r, i, it, w, a, b, c, d, e, -⟩ | ⟨pid, p, pg, off, n, a, b, c, d, e, f, -⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨l, r, i, it, w, a, b, c, d, e⟩)
  · exact Or.inr (Or.inr ⟨pid, p, pg, off, n, a, b, c, d, e, f⟩)

end flags

end bbolt
end EtcdGrove
end Perennial
