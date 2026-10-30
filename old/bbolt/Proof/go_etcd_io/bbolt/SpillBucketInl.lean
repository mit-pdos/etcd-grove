/-
`Bucket.spill`'s inlineable child: a clean, ranked bucket whose root node is a leaf has no
other node (`spInl_ns`); an inlineable node's layout is its size (`spInl_size`); the inline
value `b.write()` returns is a good inline bucket (`spInl_good`).
-/
module

public import Proof.go_etcd_io.bbolt.SpillBucketLemmas
public import Proof.go_etcd_io.bbolt.SpillFit
public import Proof.go_etcd_io.bbolt.WrittenPage
public import Proof.go_etcd_io.bbolt.Inlineable
public import Proof.go_etcd_io.bbolt.SpillNodeStep
public import Proof.go_etcd_io.bbolt.MetaInj

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]
variable [go.FloatConvSemantics]

/-- A clean, ranked bucket whose root node is a leaf: no other node. -/
theorem spInl_ns (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (hr : bktRanked B) (r0 : NRec) (h0 : B.ns !! B.bv.rootNode' = some r0)
    (hleaf : r0.nv.isLeaf' = true) : ∀ l r, B.ns !! l = some r → l = B.bv.rootNode' := by
  obtain ⟨rk, N, hrk⟩ := hr
  have hcl := hc.2.2.2.2.2.2.2.1
  have hnb : ∀ n l r, B.ns !! l = some r → r.nv.isLeaf' = false → N + 1 - rk l < n → False := by
    intro n
    induction n with
    | zero => intro l r _ _ h; omega
    | succ n ih =>
      intro l r hl hb hn
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, h14, -⟩ := hcl l r hl
      by_cases hp : r.nv.parent' = null
      · have := h13 hp; subst this; rw [h0] at hl; cases hl; rw [hleaf] at hb; cases hb
      · obtain ⟨rp, hrp, hbr, -⟩ := h14 hp
        have h1 := (hrk l r hl).2 hp
        have h2 := (hrk _ rp hrp).1
        exact ih _ rp hrp hbr (by omega)
  intro l r hl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, h14, -⟩ := hcl l r hl
  by_cases hp : r.nv.parent' = null
  · exact (h13 hp).symm
  · obtain ⟨rp, hrp, hbr, -⟩ := h14 hp
    exact (hnb (N + 2) _ rp hrp hbr (by omega)).elim

/-- An inlineable node's size, without wrapping: its layout, at most the maximum. -/
theorem spInl_size (ins : List Inode) (M : Nat) (hM : M < 2 ^ 62)
    (hsz : ∀ (k : Nat) (it : Inode), ins[k]? = some it →
      uint.Z (sizeFrom (W64 16) (W64 16) (ins.take (k + 1))) ≤ M)
    (hkv : ∀ it ∈ ins, inodeKV it ≤ 2 ^ 28) :
    uint.nat (sizeFrom (W64 16) (W64 16) ins) = layoutOf ins ∧ (ins ≠ [] → layoutOf ins ≤ M) := by
  have hpre : ∀ k, k ≤ ins.length →
      uint.nat (sizeFrom (W64 16) (W64 16) (ins.take k)) = layoutOf (ins.take k) ∧
      (0 < k → layoutOf (ins.take k) ≤ M) := by
    intro k
    induction k with
    | zero => intro _; simp [sizeFrom, layoutOf]
    | succ k ih =>
      intro hk
      obtain ⟨ih1, -⟩ := ih (by omega)
      have hk' : k < ins.length := by omega
      have hget : ins[k]? = some ins[k] := List.getElem?_eq_getElem hk'
      have htake : ins.take (k + 1) = ins.take k ++ [ins[k]] := by
        rw [List.take_add_one, hget]; rfl
      have hle := hsz k ins[k] hget
      have hkv1 := hkv ins[k] (List.getElem_mem hk')
      have hlay : layoutOf (ins.take k) ≤ M + 16 := by
        cases k with
        | zero => simp [layoutOf]
        | succ j =>
          have := (ih (by omega)).2 (by omega); omega
      rw [htake, sizeFrom_append, layoutOf_snoc]
      have hstep : uint.nat (sizeFrom (W64 16) (W64 16) (ins.take k) +
          (W64 16 + ins[k].key'.len + ins[k].value'.len)) =
          layoutOf (ins.take k) + 16 + inodeKV ins[k] := by
        unfold inodeKV at hkv1 ⊢
        rw [← ih1] at hlay ⊢
        unfold uint.nat at hlay hkv1 ⊢
        word
      refine ⟨hstep, fun _ => ?_⟩
      rw [htake, sizeFrom_append] at hle
      have : uint.Z (sizeFrom (W64 16) (W64 16) (ins.take k) +
          (W64 16 + ins[k].key'.len + ins[k].value'.len)) =
          ((layoutOf (ins.take k) + 16 + inodeKV ins[k] : Nat) : Int) := by
        rw [← hstep]
      omega
  have h := hpre ins.length (Nat.le_refl _)
  rw [List.take_length] at h
  exact ⟨h.1, fun hne => h.2 (by cases ins with | nil => exact absurd rfl hne | cons _ _ => simp)⟩

theorem spFlags_even (f : w32) (h : f &&& W32 1 = W32 0) : uint.nat f % 2 = 0 := by
  have e := congrArg BitVec.toNat h
  simp only [BitVec.toNat_and] at e
  unfold uint.nat
  have : (W32 1).toNat = 1 := rfl
  rw [this, Nat.and_one_is_mod] at e
  exact e

/-- The inline value `b.write()` returns, of a leaf whose inodes are written well, sorted, none a
nested bucket: a good inline page. -/
theorem spInl_good (ks vs : List (List w8)) (ins : List Inode) (h : writeOK ks vs ins)
    (hs : ∀ i j, i < j → j < ins.length → go.GoStringLt (ks.getD i []) (ks.getD j []))
    (hf : ∀ i < ins.length, uint.nat (ins.getD i (zero_val Inode)).flags' % 2 = 0) :
    inlineGood (writtenPage (Page.mk (W64 0) (W16 0) (W16 0) (W32 0)) true ks vs ins []) := by
  obtain ⟨F1, -, Fid, Ffl, Fc, -, Fl, -⟩ := writtenPage_facts (Page.mk (W64 0) (W16 0) (W16 0) (W32 0))
    true ks vs ins [] h
  refine ⟨by rw [Fid]; rfl, by rw [Ffl]; rfl, writtenPage_leafWF _ ks vs ins [] h hs, by omega,
    fun i hi => ?_⟩
  rw [Fc] at hi
  obtain ⟨hfl, hks, -, -, -, -⟩ := Fl rfl i hi
  refine ⟨by rw [hks]; exact h.2.2.2.1 i hi, by rw [hfl]; exact hf i hi⟩

/-- What `b.write()` of an inlineable root leaf (inodes `ins`, entries `ws`) needs. -/
theorem spInl_write (ins : List Inode) (ws : List WEntry) (ps : Nat) (hps : ps < 2 ^ 20)
    (hil : ins.length = ws.length)
    (hlen : ∀ (i : Nat) (it : Inode) (w : WEntry), ins[i]? = some it → ws[i]? = some w →
      uint.nat it.key'.len = w.key.length ∧ uint.nat it.value'.len = w.value.length)
    (hkv : ∀ w ∈ ws, w.key.length + w.value.length ≤ 2 ^ 28)
    (hk : ∀ w ∈ ws, 0 < w.key.length)
    (hinl : inlineIns (maxInline ps) ins) :
    ins.length < 65535 ∧ (ws.map WEntry.key).length = ins.length ∧
    (ws.map WEntry.value).length = ins.length ∧
    (∀ i < ins.length, 0 < ((ws.map WEntry.key).getD i []).length) ∧
    16 + 16 * ins.length + kvLen (ws.map WEntry.key) (ws.map WEntry.value) ins.length ≤ 2147483647 ∧
    sizeFrom (W64 16) (W64 16) ins =
      W64 ((16 + 16 * ins.length + kvLen (ws.map WEntry.key) (ws.map WEntry.value) ins.length : Nat) : Int) ∧
    16 + 16 * ins.length + kvLen (ws.map WEntry.key) (ws.map WEntry.value) ins.length ≤ ps / 4 + 16 := by
  have hlay := spLayout_eq ins ws hil hlen
  have hkvl : kvLen (ws.map WEntry.key) (ws.map WEntry.value) ins.length =
      (ws.map (fun w => w.key.length + w.value.length)).sum := by
    rw [hil]; exact spKvLen ws
  have hlay' : layoutOf ins = 16 + 16 * ins.length +
      kvLen (ws.map WEntry.key) (ws.map WEntry.value) ins.length := by
    rw [hlay, hkvl]; unfold spLayoutW; rw [hil]
  have hmx : uint.Z (maxInline ps) = ((ps / 4 : Nat) : Int) := by
    unfold maxInline; unfold uint.Z; simp; omega
  have hkv' : ∀ it ∈ ins, inodeKV it ≤ 2 ^ 28 := by
    intro it hit
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hit
    have hiw : i < ws.length := by omega
    obtain ⟨e1, e2⟩ := hlen i ins[i] ws[i] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hiw)
    have := hkv ws[i] (List.getElem_mem hiw)
    unfold inodeKV; omega
  obtain ⟨hs1, hs2⟩ := spInl_size ins (ps / 4) (by omega)
    (fun k it h => by have := (hinl k it h).2; omega)
    hkv'
  have hbound : layoutOf ins ≤ ps / 4 + 16 := by
    by_cases h : ins = []
    · subst h; simp [layoutOf]
    · have := hs2 h; omega
  have hge := layoutOf_ge ins
  refine ⟨by omega, by simp [hil], by simp [hil], ?_, by omega, ?_, by omega⟩
  · intro i hi
    exact spGetD_pos _ (fun k hk' => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk'; exact hk w hw) i (by simp [← hil]; exact hi)
  · rw [← hlay', ← hs1]; unfold uint.nat; exact (w64_of_toNat _).symm

end pure

end bbolt
end EtcdGrove
end Perennial
