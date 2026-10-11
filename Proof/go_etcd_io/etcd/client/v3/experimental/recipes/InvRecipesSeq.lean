/-
`newSequentialKV`'s and `newUniqueKV`'s keys: the vocabulary of their specs and the order of the
sequential keys. Lean-first (no Rocq counterpart). See `decisions.md`, "Recipes", "Units 1b, 2
and 3".

**The sequential key** (`SeqNext kp sg key`, pure): `newSequentialKV(kv, kp, val)` gets the last
key under the prefix `kp` (`WithLastKey()`: the greatest key of the prefix range, `lastKeyOp`)
in etcd's state `sg`, parses the last `/`-field of that key with `Sscanf("%d")` (`lastField`,
`fmt.scanInt`), and makes `kp/<n + 1>` with `%016d` (`kp/0000000000000000` if the range is
empty). Where `scanInt` gives nothing (another key under `kp`), the key is still
`kp/<a 16-digit decimal>` (`decimalPad 16`).

**What it puts** (`seqKeyPutAt pfx kp key val g r`, persistent): the get saw `sg` at `g`; the
transaction at `r` found `__kp` (`baseKey kp`) unmodified since `g` in the state at `r - 1` and
put `__kp` and then `key` (no lease): etcd's state at `r` is those two puts on the state at
`r - 1`. Not "created": nothing in the transaction checks that `key` is absent, and a key under
`kp` that is not one of these (or one put without `__kp`) can make `key` an existing one.

**The order** (`seqNext_order`): if every key under `kp` in `sg` is `kp/%016d(m)` for some
`m < 10^16 - 1` (`SeqKeysBelow kp (10^16 - 1) sg`, the premise; `SeqKeysWf kp` is the bound
`10^16`), the new key is `kp/%016d(m_max + 1)` (`0` if none), greater (`go.GoStringLt`, etcd's
key order) than every key under `kp` in `sg`, and itself of that shape below `10^16`. Under the
premise the key is also absent from `sg` (`seqNext_absent`); absent at `r - 1` only if no key
under `kp` appeared since (`seqKeyPutAt_created`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesClient
public import Spec.fmt.Sscanf

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3
open concurrency

/-! ## Decimals and fields -/

/-- `"/"`. -/
theorem slash_eq : (go!"/" : GoString) = [W8 47] := rfl

/-- The last `/`-field of a key: `fields[len(fields) - 1]` of `strings.Split(key, "/")`. -/
def lastField (k : GoString) : GoString :=
  ((_root_.Perennial.strings.split k go!"/").getLast?).getD []

theorem splitAux_noSep (c : w8) (r field : GoString) (h : c ∉ r) :
    _root_.Perennial.strings.splitAux [c] r field = [field ++ r] := by
  induction r generalizing field with
  | nil => simp [_root_.Perennial.strings.splitAux]
  | cons a r ih =>
    have hac : a ≠ c := fun e => h (e ▸ List.mem_cons_self)
    have hr : c ∉ r := fun hm => h (List.mem_cons_of_mem _ hm)
    rw [_root_.Perennial.strings.splitAux]
    have : ¬ ([c] ≠ [] ∧ [c] <+: a :: r) := by
      rintro ⟨-, hp⟩
      simp at hp; exact hac hp.symm
    rw [if_neg this, ih (field ++ [a]) hr]
    simp

theorem splitAux_getLast (c : w8) (d : GoString) (hd : c ∉ d) :
    ∀ (x field : GoString),
      (_root_.Perennial.strings.splitAux [c] (x ++ c :: d) field).getLast? = some d := by
  intro x
  induction x with
  | nil =>
    intro field
    rw [List.nil_append, _root_.Perennial.strings.splitAux, if_pos (by simp)]
    simp [splitAux_noSep c d [] hd]
  | cons a x ih =>
    intro field
    rw [List.cons_append, _root_.Perennial.strings.splitAux]
    by_cases hac : a = c
    · subst hac
      rw [if_pos (by simp)]
      simp only [List.drop_succ_cons, List.drop_zero, List.length_singleton]
      rw [List.getLast?_cons, ih []]
      rfl
    · have : ¬ ([c] ≠ [] ∧ [c] <+: a :: (x ++ c :: d)) := by
        rintro ⟨-, hp⟩
        simp at hp; exact hac hp.symm
      rw [if_neg this]
      exact ih _

/-- The last `/`-field of `x/d`, for `d` without `/`, is `d`. -/
theorem lastField_slash (x d : GoString) (hd : W8 47 ∉ d) : lastField (x ++ go!"/" ++ d) = d := by
  unfold lastField _root_.Perennial.strings.split
  rw [slash_eq, List.append_assoc, List.singleton_append, splitAux_getLast _ d hd x []]
  rfl

theorem digitByte_ne {d : Nat} (h : d < 10) (b : w8) (hb : uint.Z b < 48) :
    _root_.Perennial.fmt.digitByte d ≠ b := by
  intro e
  have := (_root_.Perennial.fmt.digitByte_mem_range h).1
  rw [e] at this; omega

theorem fixedDigits_digits (k n : Nat) :
    ∀ c ∈ _root_.Perennial.fmt.fixedDigits k n, 48 ≤ uint.Z c ∧ uint.Z c ≤ 57 := by
  induction k with
  | zero => simp [_root_.Perennial.fmt.fixedDigits]
  | succ k ih =>
    intro c hc
    simp only [_root_.Perennial.fmt.fixedDigits, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact _root_.Perennial.fmt.digitByte_mem_range (Nat.mod_lt _ (by omega))
    · exact ih c hc

theorem digitsValue_fixedDigits (k n : Nat) :
    ∀ acc : Nat, (_root_.Perennial.fmt.fixedDigits k n).foldl
      (fun acc b => acc * 10 + (uint.nat b - 48)) acc = acc * 10 ^ k + n % 10 ^ k := by
  induction k with
  | zero => intro acc; simp [_root_.Perennial.fmt.fixedDigits, Nat.mod_one]
  | succ k ih =>
    intro acc
    simp only [_root_.Perennial.fmt.fixedDigits, List.foldl_cons]
    rw [ih]
    have hd : n / 10 ^ k % 10 < 10 := Nat.mod_lt _ (by omega)
    have hb : uint.nat (_root_.Perennial.fmt.digitByte (n / 10 ^ k % 10)) - 48 = n / 10 ^ k % 10 := by
      unfold _root_.Perennial.fmt.digitByte; word
    rw [hb, Nat.mod_pow_succ, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ k),
      Nat.mul_comm (n / 10 ^ k % 10) (10 ^ k)]
    omega

/-- `Sscanf("%d")` of `k ≥ 1` decimal digits (leading zeros allowed) is their value. -/
theorem scanInt_fixedDigits (k n : Nat) (hk : 0 < k) (hn : n < 2 ^ 63) :
    fmt.scanInt (_root_.Perennial.fmt.fixedDigits k n) = some (((n % 10 ^ k : Nat)) : Int) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hd : n / 10 ^ k % 10 < 10 := Nat.mod_lt _ (by omega)
  have hall := fixedDigits_digits (k + 1) n
  have hdrop : (_root_.Perennial.fmt.fixedDigits (k + 1) n).dropWhile (fun b => b == W8 32) =
      _root_.Perennial.fmt.fixedDigits (k + 1) n := by
    simp only [_root_.Perennial.fmt.fixedDigits, List.dropWhile_cons]
    have : (_root_.Perennial.fmt.digitByte (n / 10 ^ k % 10) == W8 32) = false := by
      simpa using digitByte_ne hd (W8 32) (by decide)
    rw [this]; rfl
  have hhead : (_root_.Perennial.fmt.fixedDigits (k + 1) n).head? =
      some (_root_.Perennial.fmt.digitByte (n / 10 ^ k % 10)) := rfl
  have h45 : _root_.Perennial.fmt.digitByte (n / 10 ^ k % 10) ≠ W8 45 :=
    digitByte_ne hd _ (by decide)
  have h43 : _root_.Perennial.fmt.digitByte (n / 10 ^ k % 10) ≠ W8 43 :=
    digitByte_ne hd _ (by decide)
  have htake : (_root_.Perennial.fmt.fixedDigits (k + 1) n).takeWhile fmt.isDigitByte =
      _root_.Perennial.fmt.fixedDigits (k + 1) n := by
    have := List.takeWhile_append_of_pos (p := fmt.isDigitByte)
      (l₁ := _root_.Perennial.fmt.fixedDigits (k + 1) n) (l₂ := [])
      (fun c hc => by simpa [fmt.isDigitByte] using hall c hc)
    simpa using this
  have hval : fmt.digitsValue (_root_.Perennial.fmt.fixedDigits (k + 1) n) = n % 10 ^ (k + 1) := by
    unfold fmt.digitsValue; rw [digitsValue_fixedDigits]; simp
  have hne : _root_.Perennial.fmt.fixedDigits (k + 1) n ≠ [] := by
    simp [_root_.Perennial.fmt.fixedDigits]
  have hlt : n % 10 ^ (k + 1) < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.mod_le _ _) hn
  unfold fmt.scanInt
  simp only [hdrop, hhead, Option.some.injEq, h45, h43, _root_.or_self, ↓reduceIte, htake, hval]
  rw [if_pos ⟨hne, by omega, by omega⟩]

/-! ## The sequential keys -/

/-- `OpGet(kp, WithLastKey()...)`: the prefix range of `kp`, sorted by key descending, limit 1. -/
def lastKeyOp (kp : GoString) : OpFull := opGetModel kp (withTopM (W64 0) (W64 2))

theorem lastKeyOp_fields (kp : GoString) :
    (lastKeyOp kp).t = W64 1 ∧ (lastKeyOp kp).base.rev = W64 0 ∧
    (lastKeyOp kp).base.serializable = false ∧
    (lastKeyOp kp).effSortOrder = W64 2 ∧ (lastKeyOp kp).sortTarget = W64 0 ∧
    (lastKeyOp kp).base.limit = W64 1 ∧ (lastKeyOp kp).base.countOnly = false ∧
    (lastKeyOp kp).keysOnly = false ∧ (lastKeyOp kp).base.minModRev = W64 0 ∧
    (lastKeyOp kp).base.maxModRev = W64 0 ∧ (lastKeyOp kp).base.minCreateRev = W64 0 ∧
    (lastKeyOp kp).base.maxCreateRev = W64 0 := by
  by_cases h : kp = [] <;>
  simp [lastKeyOp, opGetModel, opFold, withTopM, withPrefixM, withSortM, withLimitM,
    OpFull.getInit, OpFull.newOp, OpModel.zero, h, OpFull.effSortOrder]

theorem lastKeyOp_range (kp : GoString) (hkp : kp ≠ []) :
    (lastKeyOp kp).key = kp ∧ (lastKeyOp kp).base.rangeEnd = prefixRangeEnd kp := by
  simp [lastKeyOp, opGetModel, opFold, withTopM, withPrefixM, withSortM, withLimitM,
    OpFull.getInit, OpFull.newOp, OpModel.zero, hkp]

theorem lastKeyOp_isPrefixGet (pfx kp : GoString) : (lastKeyOp kp).isPrefixGet pfx = false := by
  by_cases h : kp = [] <;> by_cases h' : pfx = [] <;>
  simp [lastKeyOp, opGetModel, opFold, withTopM, withPrefixM, withSortM, withLimitM,
    OpFull.getInit, OpFull.newOp, OpModel.zero, h, h', OpFull.isPrefixGet]

theorem lastKeyOp_not_panics : ¬ opGetPanics (withTopM (W64 0) (W64 2)) := by
  simp [opGetPanics, opFold, withTopM, withPrefixM, withSortM, withLimitM, OpFull.newOp,
    OpModel.zero]

theorem lastKeyOp_under (pfx kp : GoString) (h : pfx <+: kp) :
    KeyRangeUnder pfx (lastKeyOp kp).key (lastKeyOp kp).base.rangeEnd := by
  by_cases hk : kp = []
  · subst hk
    have : pfx = [] := List.prefix_nil.1 h
    subst this
    intro k _; exact List.nil_prefix
  · obtain ⟨e1, e2⟩ := lastKeyOp_range kp hk
    rw [e1, e2]
    intro k hk'
    exact h.trans (keyRangeUnder_prefix kp hk k hk')

theorem rangeIn_lastKeyOp (kp : GoString) (hkp : kp ≠ []) (s : List EtcdKv) (v : EtcdKv) :
    v ∈ rangeIn s (lastKeyOp kp) ↔ v ∈ s ∧ kp <+: v.key := by
  obtain ⟨e1, e2⟩ := lastKeyOp_range kp hkp
  unfold rangeIn; rw [List.mem_filter, e1, e2, inRange_prefix kp v.key hkp]

/-- **`WithLastKey()`'s response**: nothing if the range is empty; otherwise the one key-value of
the range with the greatest key. -/
theorem lastKeyOp_kvs (kp : GoString) (s kvs : List EtcdKv)
    (h : rangeKvsOk (lastKeyOp kp) (rangeSel s (lastKeyOp kp)) kvs) :
    (kvs = [] ∧ rangeIn s (lastKeyOp kp) = []) ∨
    ∃ v, kvs = [v] ∧ v ∈ rangeIn s (lastKeyOp kp) ∧
      ∀ w ∈ rangeIn s (lastKeyOp kp), go.GoStringLe w.key v.key := by
  obtain ⟨ht, hrev, hser, hso, hst, hl, hc, hko, h1, h2, h3, h4⟩ := lastKeyOp_fields kp
  have hsel : rangeSel s (lastKeyOp kp) = rangeIn s (lastKeyOp kp) := by
    unfold rangeSel; rw [List.filter_eq_self]
    intro v _; exact kvFilterOk_zero _ v h1 h2 h3 h4
  rw [hsel] at h
  obtain ⟨l, hperm, -, -, hdesc, rfl⟩ := h
  have hdesc := hdesc hso
  rw [hst] at hdesc
  simp only [hc, hl, hko, Bool.false_eq_true, ↓reduceIte]
  cases l with
  | nil =>
    left
    refine ⟨by simp, ?_⟩
    exact List.eq_nil_of_subset_nil (fun x hx => hperm.symm.subset hx)
  | cons a l =>
    right
    refine ⟨a, ?_, hperm.subset List.mem_cons_self, ?_⟩
    · have : 0 < sint.Z (W64 1) := by decide
      simp [this]
    · intro w hw
      have hw' := hperm.symm.subset hw
      rcases List.mem_cons.1 hw' with rfl | hw''
      · exact Or.inl rfl
      · have := (List.pairwise_cons.1 hdesc).1 w hw''
        simpa [kvLeBy] using this

/-- The bookkeeping key `__kp`. -/
def baseKey (kp : GoString) : GoString := go!"__" ++ kp

/-- **`newSequentialKV`'s key, from the state `sg` its get saw** (see the module docstring): the
range empty, `kp/0000000000000000`; otherwise, for the greatest key `v` of the range, if
`Sscanf("%d")` parses its last field as `n` (`fmt.scanInt`), `kp/%016d(n + 1)` (`n + 1` wraps as
Go's `int`). -/
def SeqNext (kp : GoString) (sg : List EtcdKv) (key : GoString) : Prop :=
  (rangeIn sg (lastKeyOp kp) = [] ∧
    key = kp ++ go!"/" ++ _root_.Perennial.fmt.decimalPad 16 0) ∨
  ∃ v ∈ rangeIn sg (lastKeyOp kp), (∀ w ∈ rangeIn sg (lastKeyOp kp), go.GoStringLe w.key v.key) ∧
    ∀ n : w64, fmt.scanInt (lastField v.key) = some (sint.Z n) →
      key = kp ++ go!"/" ++ _root_.Perennial.fmt.decimalPad 16 (sint.Z (n + W64 1))

/-- **A sequential key**: `kp/%016d(m)`. -/
def seqKey (kp : GoString) (m : Nat) : GoString :=
  kp ++ go!"/" ++ _root_.Perennial.fmt.padZeros 16 (_root_.Perennial.fmt.decimalNat m)

/-- **Every key under `kp` in `s` is a sequential key below `N`.** -/
def SeqKeysBelow (kp : GoString) (N : Nat) (s : List EtcdKv) : Prop :=
  ∀ v ∈ s, kp <+: v.key → ∃ m < N, v.key = seqKey kp m

/-- **The keys under `kp` are `newSequentialKV`'s** (`kp/%016d(m)`, `m < 10^16`). -/
abbrev SeqKeysWf (kp : GoString) (s : List EtcdKv) : Prop := SeqKeysBelow kp (10 ^ 16) s

theorem goStringLt_append_left (x a b : GoString) (h : go.GoStringLt a b) :
    go.GoStringLt (x ++ a) (x ++ b) := by
  induction x with
  | nil => exact h
  | cons c x ih => exact List.Lex.cons ih

theorem seqKey_lt (kp : GoString) (a b : Nat) (hab : a < b) (hb : b < 10 ^ 16) :
    go.GoStringLt (seqKey kp a) (seqKey kp b) := by
  unfold seqKey
  rw [List.append_assoc, List.append_assoc]
  exact goStringLt_append_left _ _ _
    (goStringLt_append_left _ _ _ (_root_.Perennial.fmt.padZeros_decimalNat_lt 16 a b hab hb))

theorem seqKey_le (kp : GoString) (a b : Nat) (ha : a < 10 ^ 16)
    (h : go.GoStringLe (seqKey kp a) (seqKey kp b)) : a ≤ b := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have hlt' := seqKey_lt kp b a hlt ha
  rcases h with e | h
  · rw [e] at hlt'; exact goStringLt_irrefl _ hlt'
  · exact goStringLt_irrefl _ (goStringLt_trans h hlt')

theorem padZeros_decimalNat_noSlash (m : Nat) :
    W8 47 ∉ _root_.Perennial.fmt.padZeros 16 (_root_.Perennial.fmt.decimalNat m) := by
  intro hm
  unfold _root_.Perennial.fmt.padZeros at hm
  rcases List.mem_append.1 hm with hm | hm
  · have := List.eq_of_mem_replicate hm
    exact absurd this (by decide)
  · have := (_root_.Perennial.fmt.decimalNat_digits m _ hm).1
    exact absurd this (by decide)

theorem scanInt_seqField (m : Nat) (hm : m < 10 ^ 16) :
    fmt.scanInt (_root_.Perennial.fmt.padZeros 16 (_root_.Perennial.fmt.decimalNat m)) =
      some (m : Int) := by
  rw [_root_.Perennial.fmt.padZeros_decimalNat 15 m hm,
    scanInt_fixedDigits 16 m (by omega) (by omega), Nat.mod_eq_of_lt hm]

theorem decimalPad_seq (m : Nat) :
    _root_.Perennial.fmt.decimalPad 16 (m : Int) =
      _root_.Perennial.fmt.padZeros 16 (_root_.Perennial.fmt.decimalNat m) := by
  rw [_root_.Perennial.fmt.decimalPad_of_nonneg _ (by omega), _root_.Perennial.fmt.decimal_natCast]

/-- **The order of `newSequentialKV`'s keys, under the premise on the keys under `kp`**: if every
key under `kp` in the state `sg` the get saw is `kp/%016d(m)` with `m < 10^16 - 1`, the new key
is `kp/%016d(m)` for the `m` one past the greatest of them (`0` if none), `m < 10^16`: greater
(`go.GoStringLt`) than every key under `kp` in `sg`. -/
theorem seqNext_order (kp : GoString) (sg : List EtcdKv) (key : GoString) (hkp : kp ≠ [])
    (hwf : SeqKeysBelow kp (10 ^ 16 - 1) sg) (h : SeqNext kp sg key) :
    ∃ m, m < 10 ^ 16 ∧ key = seqKey kp m ∧
      (∀ v ∈ sg, kp <+: v.key → ∃ m' < m, v.key = seqKey kp m') ∧
      (∀ v ∈ sg, kp <+: v.key → go.GoStringLt v.key key) ∧
      (m = 0 ∨ ∃ v ∈ sg, v.key = seqKey kp (m - 1)) := by
  have hmem := rangeIn_lastKeyOp kp hkp sg
  rcases h with ⟨hnil, rfl⟩ | ⟨v, hv, hmax, hkey⟩
  · refine ⟨0, by omega, ?_, ?_, ?_, Or.inl rfl⟩
    · unfold seqKey; rw [← decimalPad_seq]; rfl
    · intro w hw hk
      have : w ∈ rangeIn sg (lastKeyOp kp) := (hmem w).2 ⟨hw, hk⟩
      rw [hnil] at this; simp at this
    · intro w hw hk
      have : w ∈ rangeIn sg (lastKeyOp kp) := (hmem w).2 ⟨hw, hk⟩
      rw [hnil] at this; simp at this
  · obtain ⟨hvs, hvk⟩ := (hmem v).1 hv
    obtain ⟨mv, hmv, hvkey⟩ := hwf v hvs hvk
    have hfield : lastField v.key =
        _root_.Perennial.fmt.padZeros 16 (_root_.Perennial.fmt.decimalNat mv) := by
      rw [hvkey]; unfold seqKey; exact lastField_slash _ _ (padZeros_decimalNat_noSlash mv)
    have hn : sint.Z (W64 (mv : Int)) = (mv : Int) := by
      have : (mv : Int) < 2 ^ 63 := by omega
      word
    have hk := hkey (W64 (mv : Int))
      (by rw [hfield, scanInt_seqField mv (by omega), hn])
    have hn1 : sint.Z (W64 (mv : Int) + W64 1) = ((mv + 1 : Nat) : Int) := by
      have : (mv : Int) < 2 ^ 63 - 2 := by omega
      push_cast; word
    rw [hn1, decimalPad_seq] at hk
    have hle : ∀ w ∈ sg, kp <+: w.key → ∃ m' < mv + 1, w.key = seqKey kp m' := by
      intro w hw hwk
      obtain ⟨mw, hmw, hwkey⟩ := hwf w hw hwk
      have := hmax w ((hmem w).2 ⟨hw, hwk⟩)
      rw [hwkey, hvkey] at this
      exact ⟨mw, Nat.lt_succ_of_le (seqKey_le kp mw mv (by omega) this), hwkey⟩
    refine ⟨mv + 1, by omega, hk, hle, ?_, Or.inr ⟨v, hvs, by simpa using hvkey⟩⟩
    intro w hw hwk
    obtain ⟨mw, hmw, hwkey⟩ := hle w hw hwk
    rw [hwkey, hk]
    exact seqKey_lt kp mw (mv + 1) hmw (by omega)

/-- Under the premise, the new key is absent from the state the get saw. -/
theorem seqNext_absent (kp : GoString) (sg : List EtcdKv) (key : GoString) (hkp : kp ≠ [])
    (hwf : SeqKeysBelow kp (10 ^ 16 - 1) sg) (h : SeqNext kp sg key) : ∀ v ∈ sg, v.key ≠ key := by
  obtain ⟨m, -, hk, -, hlt, -⟩ := seqNext_order kp sg key hkp hwf h
  intro v hv e
  have hpre : kp <+: v.key := by
    rw [e, hk]; unfold seqKey; rw [List.append_assoc]; exact List.prefix_append _ _
  have := hlt v hv hpre
  rw [e] at this; exact goStringLt_irrefl _ this

section sprintf
variable [FfiSyntax] [GoGlobalContext]

/-- `Sprintf("%s/%016d", x, n)` for a string `x` and an `int` `n` (of any sign) is `x/` then
`decimalPad 16 n` (`SprintfOut.str_slash_016d_int` for `n ≥ 0`). -/
theorem sprintf_slash_016d [go.IntoValInj GoString] [go.IntoValInj w64]
    (x : GoString) (n : w64) (out : GoString)
    (h : _root_.Perennial.fmt.SprintfOut go!"%s/%016d"
      [interface.mkOk go.string #x, interface.mkOk go.int #n] out) :
    out = x ++ go!"/" ++ _root_.Perennial.fmt.decimalPad 16 (sint.Z n) := by
  have hfmt : go!"%s/%016d" =
      W8 37 :: W8 115 :: W8 47 :: W8 37 :: [W8 48, W8 49, W8 54, W8 100] := rfl
  rw [hfmt] at h
  obtain ⟨o1, rfl, h1⟩ := _root_.Perennial.fmt.SprintfOut.str_inv h
  obtain ⟨o2, rfl, h2⟩ := _root_.Perennial.fmt.SprintfOut.byte_inv (by decide) h1
  obtain ⟨o3, rfl, h3⟩ := _root_.Perennial.fmt.SprintfOut.int_inv (w := 16) (rest := []) (by decide)
    (_root_.Perennial.fmt.IntArgValue.int n) (_root_.Perennial.fmt.IntArgValue.uniq_int n) h2
  rw [_root_.Perennial.fmt.SprintfOut.done_inv h3]
  simp

end sprintf

/-! ## `newSequentialKV`'s transaction -/

/-- `If(ModRevision(__kp) < g + 1).Then(OpPut(__kp, ""), OpPut(key, val))`. -/
def seqTxn (kp key val : GoString) (g : w64) : TxnModel :=
  { cmps := [compareM (cmpKeyM .mod (baseKey kp)) .lt (.num (g + W64 1))],
    thenOps := [.put (baseKey kp) [] (W64 0), .put key val (W64 0)], elseOps := [] }

theorem seqTxn_under (pfx kp key val : GoString) (g : w64) (hb : pfx <+: baseKey kp)
    (hk : pfx <+: key) : (seqTxn kp key val g).Under pfx := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    simp only [seqTxn, List.mem_singleton] at hc
    subst hc
    exact keyRangeUnder_key pfx _ hb
  · intro op hop
    simp only [seqTxn, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · exact hb
    · exact hk
  · intro op hop
    simp [seqTxn] at hop

/-- A comparison `ModRevision(k) < c` that holds: every key-value of `k` has a mod revision below
`c`. -/
theorem modRev_lt_of_cmp (k : GoString) (c : w64) (s : List EtcdKv)
    (h : cmpHolds s (compareM (cmpKeyM .mod k) .lt (.num c)) = true) :
    ∀ v ∈ s, v.key = k → sint.Z v.modRev < sint.Z c := by
  intro v hv hvk
  unfold cmpHolds at h
  simp only [compareM, cmpKeyM] at h
  have hin : v ∈ s.filter (fun w => inRange k [] w.key) :=
    List.mem_filter.2 ⟨hv, by simp [inRange, hvk]⟩
  have hne : s.filter (fun w => inRange k [] w.key) ≠ [] := List.ne_nil_of_mem hin
  simp only [hne, ite_false] at h
  have hall := List.all_eq_true.1 h v hin
  simp only [cmpKv, CmpOp.holds, int64Cmp, cmpSign] at hall
  by_cases hlt : sint.Z v.modRev < sint.Z c
  · exact hlt
  · exfalso
    simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at hall
    split at hall <;> simp at hall

/-- **`newSequentialKV`'s transaction succeeded**: `__kp` had a mod revision at most `g` (below
`g + 1`, for `g < 2^63 - 1`), and it put `__kp` and then `key` (a write). -/
theorem seqTxn_then (kp key val : GoString) (g r : w64) (s : List EtcdKv)
    (hg : sint.Z g < 2 ^ 63 - 1) (h : (runTxn r s (seqTxn kp key val g)).1 = true) :
    (∀ v ∈ s, v.key = baseKey kp → sint.Z v.modRev ≤ sint.Z g) ∧
    (runTxn r s (seqTxn kp key val g)).2.1 =
      putKv r key val (W64 0) (putKv r (baseKey kp) [] (W64 0) s) ∧
    txnWrote (runTxn r s (seqTxn kp key val g)).2.2 = true := by
  have hok : (seqTxn kp key val g).cmps.all (cmpHolds s) = true := h
  have hok' := hok
  simp only [seqTxn, List.all_cons, List.all_nil, Bool.and_true] at hok'
  have hg1 : sint.Z (g + W64 1) = sint.Z g + 1 := by word
  have e : runTxn r s (seqTxn kp key val g) =
      (true, putKv r key val (W64 0) (putKv r (baseKey kp) [] (W64 0) s), [.put, .put]) := by
    simp only [runTxn, hok, TxnModel.branch, ite_true]
    simp [seqTxn, runOps, applyTxnOp]
  rw [e]
  refine ⟨?_, rfl, rfl⟩
  intro v hv hvk
  have := modRev_lt_of_cmp _ _ s hok' v hv hvk
  omega

/-- **`newSequentialKV`'s transaction failed**: nothing was written. -/
theorem seqTxn_else (kp key val : GoString) (g r : w64) (s : List EtcdKv)
    (h : (runTxn r s (seqTxn kp key val g)).1 = false) :
    (runTxn r s (seqTxn kp key val g)).2.1 = s ∧
    txnWrote (runTxn r s (seqTxn kp key val g)).2.2 = false := by
  have hok : (seqTxn kp key val g).cmps.all (cmpHolds s) = false := h
  have e : runTxn r s (seqTxn kp key val g) = (false, s, []) := by
    simp only [runTxn, hok, TxnModel.branch]
    simp [seqTxn, runOps]
  rw [e]
  exact ⟨rfl, rfl⟩

/-! ## Puts -/

theorem putKv_mem (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) (x : EtcdKv)
    (hx : x ∈ putKv r k val l s) : x.key = k ∨ x ∈ s := by
  unfold putKv at hx
  rcases btInsert_mem hx with rfl | hx
  · left
    split
    · rename_i v hv
      have := List.find?_some hv
      simpa using this
    · rfl
  · exact Or.inr hx

theorem putKv_wf (pfx : GoString) (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv)
    (hwf : EtcdStateWf pfx s) (hk : pfx <+: k) : EtcdStateWf pfx (putKv r k val l s) := by
  refine ⟨?_, ?_⟩
  · have h0 : s.Pairwise etcdKvLess :=
      (List.pairwise_map (f := EtcdKv.key) (R := go.GoStringLt)).1 hwf.1
    unfold putKv
    exact (List.pairwise_map (f := EtcdKv.key) (R := go.GoStringLt)).2
      (btInsert_sorted etcdKvLess_swo h0)
  · intro v hv
    rcases putKv_mem r k val l s v hv with e | hv
    · rw [e]; exact hk
    · exact hwf.2 v hv

/-- A put of a key absent from `s` creates it: create and mod revision `r`, version `1`. -/
theorem putKv_new (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv)
    (habs : ∀ v ∈ s, v.key ≠ k) :
    ∃ v ∈ putKv r k val l s, v.key = k ∧ v.createRev = r ∧ v.modRev = r ∧
      v.version = W64 1 ∧ v.value = val ∧ v.lease = l := by
  have hfind : s.find? (fun v => decide (v.key = k)) = none := by
    rw [List.find?_eq_none]; intro v hv; simpa using habs v hv
  unfold putKv; rw [hfind]
  exact ⟨_, btInsert_self_mem _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem length_seqKey (kp : GoString) (m : Nat) (hm : m < 10 ^ 16) :
    (seqKey kp m).length = kp.length + 17 := by
  unfold seqKey
  have := _root_.Perennial.fmt.length_decimalNat_le m 16 (by omega) hm
  simp [_root_.Perennial.fmt.length_padZeros]
  omega

section iprop
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **What `newSequentialKV` put** (persistent; see the module docstring): its get saw the
state `sg` at `g` and `key` is made from it (`SeqNext`); in etcd's state `s0` at `r - 1`, `__kp`
was last modified at or before `g`; the state at `r` is `s0` with `__kp` (empty, no lease) and
then `key` (`val`, no lease) put at `r`. -/
def seqKeyPutAt (pfx kp key val : GoString) (g r : w64) : IProp GF :=
  iprop(∃ sg s0 : List EtcdKv, □ etcdState g pfx sg ∗ □ etcdState (r - W64 1) pfx s0 ∗
    □ etcdState r pfx (putKv r key val (W64 0) (putKv r (baseKey kp) [] (W64 0) s0)) ∗
    ⌜EtcdStateWf pfx sg ∧ EtcdStateWf pfx s0 ∧ SeqNext kp sg key ∧ 0 < sint.Z r ∧
      ∀ v ∈ s0, v.key = baseKey kp → sint.Z v.modRev ≤ sint.Z g⌝)

instance seqKeyPutAt_persistent (pfx kp key val : GoString) (g r : w64) :
    Persistent (seqKeyPutAt (GF := GF) pfx kp key val g r) := by
  unfold seqKeyPutAt; infer_instance

/-- **The order, on `newSequentialKV`'s result**: under the premise on the keys under `kp` at the
get's revision `g` (`SeqKeysBelow kp (10^16 - 1)`), the key is `kp/%016d(m)`, one past the
greatest such key then, and greater than every key under `kp` then (`seqNext_order`). -/
theorem seqKeyPutAt_order (pfx kp key val : GoString) (g r : w64) (hkp : kp ≠ []) :
    seqKeyPutAt (GF := GF) pfx kp key val g r ⊢
      ∃ sg : List EtcdKv, □ etcdState g pfx sg ∗
        ⌜SeqKeysBelow kp (10 ^ 16 - 1) sg →
          ∃ m, m < 10 ^ 16 ∧ key = seqKey kp m ∧
            (∀ v ∈ sg, kp <+: v.key → ∃ m' < m, v.key = seqKey kp m') ∧
            (∀ v ∈ sg, kp <+: v.key → go.GoStringLt v.key key) ∧
            (m = 0 ∨ ∃ v ∈ sg, v.key = seqKey kp (m - 1))⌝ := by
  unfold seqKeyPutAt
  iintro ⟨%sg, %s0, #Hsg, -, -, %H⟩
  iexists sg
  iframe Hsg
  ipureintro
  intro hwf
  exact seqNext_order kp sg key hkp hwf H.2.2.1

/-- **The key was created**, under the premise on the keys under `kp` at the get's revision `g`
and if no key under `kp` appeared between `g` and the transaction (every key under `kp` at
`r - 1` was there at `g`: true if every writer of a key under `kp` also puts `__kp`, which the
transaction's comparison then rules out). -/
theorem seqKeyPutAt_created (pfx kp key val : GoString) (g r : w64) (hkp : kp ≠ [])
    (hpk : pfx <+: key) (hpb : pfx <+: baseKey kp) :
    seqKeyPutAt (GF := GF) pfx kp key val g r ⊢
      ∀ s0 : List EtcdKv, □ etcdState (r - W64 1) pfx s0 -∗
      ∃ sg : List EtcdKv, □ etcdState g pfx sg ∗
        ⌜SeqKeysBelow kp (10 ^ 16 - 1) sg →
          (∀ v ∈ s0, kp <+: v.key → ∃ w ∈ sg, w.key = v.key) →
          ∃ s1 : List EtcdKv, s1 = putKv r key val (W64 0) (putKv r (baseKey kp) [] (W64 0) s0) ∧
            (∀ v ∈ s0, v.key ≠ key) ∧ EtcdStateWf pfx s1 ∧
            ∃ v ∈ s1, v.key = key ∧ v.createRev = r ∧ v.modRev = r ∧ v.version = W64 1 ∧
              v.value = val ∧ v.lease = W64 0⌝ := by
  unfold seqKeyPutAt
  iintro ⟨%sg, %s0, #Hsg, #Hs0, -, %H⟩ %s0' #Hs0'
  ihave %He := etcdState_agree _ _ _ _ $$ [Hs0 Hs0']
  · isplitl [Hs0]
    · iexact Hs0
    · iexact Hs0'
  subst He
  iexists sg
  iframe Hsg
  ipureintro
  intro hwf hnew
  obtain ⟨-, hwf0, hseq, -, -⟩ := H
  obtain ⟨m, hm, hk, -, -, -⟩ := seqNext_order kp sg key hkp hwf hseq
  have habs0 := seqNext_absent kp sg key hkp hwf hseq
  have hkkp : kp <+: key := by rw [hk]; unfold seqKey; rw [List.append_assoc]; exact List.prefix_append _ _
  have habs : ∀ v ∈ s0, v.key ≠ key := by
    intro v hv e
    obtain ⟨w, hw, hwk⟩ := hnew v hv (e ▸ hkkp)
    exact habs0 w hw (hwk.trans e)
  have hbk : baseKey kp ≠ key := by
    intro e
    have h1 := congrArg List.length e
    rw [hk, length_seqKey kp m hm] at h1
    simp [baseKey] at h1
  have habs1 : ∀ v ∈ putKv r (baseKey kp) [] (W64 0) s0, v.key ≠ key := by
    intro v hv
    rcases putKv_mem _ _ _ _ _ v hv with e | hv
    · rw [e]; exact hbk
    · exact habs v hv
  exact ⟨_, rfl, habs, putKv_wf _ _ _ _ _ _ (putKv_wf _ _ _ _ _ _ hwf0 hpb) hpk,
    putKv_new _ _ _ _ _ habs1⟩

end iprop

end recipes
end EtcdGrove
end Perennial
