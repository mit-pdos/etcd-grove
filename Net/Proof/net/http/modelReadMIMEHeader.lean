/-
The proof of `modelReadMIMEHeader` (`Net/Spec/net/http/modelReadMIMEHeader.lean`).

The loop's invariant (`mh_loop`): either `n` whole lines of the block read (the reader at
`r ++ mhPre hb n`, the map `hdrOwn` of the first `n` lines, `maxHeaders` at `maxH - n`), or a line
cut by an error read (the reader at the error's position, with `E`'s evidence: by the finality law
nothing follows, so the next `modelReadLine` returns the error). A line read is a prefix of the
stream's next bytes (`Htl`): a whole line is the next block line, or the empty line (the loop
returns); a cut line is a prefix of the next block line without its `"\n"` (`mh_cut_cases`): either
without a colon (a key's prefix, or the empty line's `"\r"`: the missing-colon `ProtocolError`, its
`[]byte` argument lent to `fmt.Sprintf`, `fmt.wp_Sprintf_bytes`) or the line's name, a colon and
some bytes. A line `k:w` (`mh_after`): the `Peek(1)` sees no space or tab (the next line's name, the
empty line, or nothing: an error), `trimLine` leaves `k:` and `w` without its trailing spaces
(`wp_trimLine`, `mh_trim_line`), the name passes its checks (`ValidHeaderFieldName` over
`tokenTable`, `canonQuick`), the value's check passes or gives a `ProtocolError`, and the value
without its leading spaces (`mhVal`) is stored under the name, absent so far (distinct names,
`mh_key_fresh`; `mh_ins`). `maxHeaders` never goes below `0` (the block's length is at most it).
-/
module

public import Net.Spec.net.http.modelReadMIMEHeader
public import Net.Spec.net.http.modelReadLine
public import Net.Spec.net.textproto.CanonicalMIMEHeaderKey
public import Net.Spec.vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldName
public import Net.Spec.vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldValue
public import Spec.bufio.Reader__Peek
public import Perennial.Spec.fmt.Sprintf
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.http


section pure

/-- A space or a tab (what `trimLine` and the value's skip loop drop). -/
def mhWs (c : w8) : Bool := decide (c = W8 32) || decide (c = W8 9)

/-- `l` without its trailing spaces and tabs. -/
def mhRtrim (l : List w8) : List w8 := (l.reverse.dropWhile mhWs).reverse

/-- What `trimLine` returns. -/
def mhTrim (l : List w8) : List w8 := mhRtrim (l.dropWhile mhWs)

/-- The value stored for a line `k:w` (its trailing then leading spaces dropped). -/
def mhVal (w : List w8) : List w8 := (mhRtrim w).dropWhile mhWs

/-- The block's first `n` lines' bytes. -/
def mhPre (hb : List HdrLine) (n : Nat) : List w8 := (hb.take n).flatMap hdrLineWire

/-- The bytes after them. -/
def mhTl (hb : List HdrLine) (eol rest : List w8) (n : Nat) : List w8 :=
  (hb.drop n).flatMap hdrLineWire ++ eol ++ W8 10 :: rest

/-- A header line without its `"\n"`. -/
def mhBody (kv : HdrLine) : List w8 := kv.1 ++ [W8 58, W8 32] ++ kv.2 ++ [W8 13]

theorem mh_split (hb : List HdrLine) (eol rest : List w8) (n : Nat) :
    hdrWire hb eol ++ rest = mhPre hb n ++ mhTl hb eol rest n := by
  unfold hdrWire mhPre mhTl
  rw [← List.take_append_drop n hb, List.flatMap_append]
  simp [List.append_assoc]

theorem mh_pre_succ (hb : List HdrLine) (n : Nat) (hn : n < hb.length) :
    mhPre hb (n + 1) = mhPre hb n ++ mhBody hb[n] ++ [W8 10] := by
  unfold mhPre mhBody
  rw [List.take_add_one, List.getElem?_eq_getElem hn, List.flatMap_append]
  simp only [Option.toList, List.flatMap_cons, List.flatMap_nil, List.append_nil, hdrLineWire,
    List.append_assoc, List.cons_append, List.nil_append]

theorem mh_tl_lt (hb : List HdrLine) (eol rest : List w8) (n : Nat) (hn : n < hb.length) :
    mhTl hb eol rest n = mhBody hb[n] ++ W8 10 :: mhTl hb eol rest (n + 1) := by
  unfold mhTl mhBody
  rw [List.drop_eq_getElem_cons hn, List.flatMap_cons]
  simp only [hdrLineWire, List.append_assoc, List.cons_append, List.nil_append]

theorem mh_tl_len (hb : List HdrLine) (eol rest : List w8) :
    mhTl hb eol rest hb.length = eol ++ W8 10 :: rest := by
  unfold mhTl; simp

theorem fieldByte_not_ws : ∀ c : w8, fieldByte c = true → c ≠ W8 32 ∧ c ≠ W8 9 ∧ c ≠ W8 58 ∧
    c ≠ W8 10 ∧ c ≠ W8 13 := by decide

theorem valByte_not : ∀ c : w8, valByte c = true → c ≠ W8 9 ∧ c ≠ W8 10 ∧ c ≠ W8 13 := by decide

theorem mh_line_ok {hb : List HdrLine} (hok : hdrBlockOk hb) {n : Nat} (hn : n < hb.length) :
    hdrLineOk hb[n] := hok.2 _ (List.getElem_mem hn)

/-- The next byte after `n` lines is no space or tab. -/
theorem mh_tl_head {hb : List HdrLine} {eol rest : List w8} (hok : hdrBlockOk hb)
    (heol : eol = [] ∨ eol = [W8 13]) {n : Nat} (hn : n ≤ hb.length) {c : w8} {q : List w8}
    (h : mhTl hb eol rest n = c :: q) : c ≠ W8 32 ∧ c ≠ W8 9 := by
  rcases Nat.lt_or_ge n hb.length with hlt | hge
  · rw [mh_tl_lt hb eol rest n hlt] at h
    obtain ⟨hne, hall, -⟩ := mh_line_ok hok hlt
    unfold mhBody at h
    obtain ⟨k0, ks, hk⟩ := List.exists_cons_of_ne_nil hne
    rw [hk] at h hall
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have := fieldByte_not_ws k0 (by simp at hall; exact hall.1)
    exact ⟨this.1, this.2.1⟩
  · have : n = hb.length := by omega
    subst this
    rw [mh_tl_len] at h
    rcases heol with rfl | rfl <;> simp at h <;> obtain ⟨rfl, -⟩ := h <;> decide

theorem mh_body_no_nl {kv : HdrLine} (h : hdrLineOk kv) : W8 10 ∉ mhBody kv := by
  obtain ⟨-, hk, -, hv, -⟩ := h
  have h1 : ∀ x ∈ kv.1, x ≠ W8 10 := fun x hx => (fieldByte_not_ws _ (List.all_eq_true.mp hk _ hx)).2.2.2.1
  have h2 : ∀ x ∈ kv.2, x ≠ W8 10 := fun x hx => (valByte_not _ (List.all_eq_true.mp hv _ hx)).2.1
  unfold mhBody
  intro hm
  simp only [List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.cons_append, List.nil_append] at hm
  rcases hm with hm | hm | hm | hm | hm
  · exact h1 _ hm rfl
  · exact absurd hm (by decide)
  · exact absurd hm (by decide)
  · exact h2 _ hm rfl
  · exact absurd hm (by decide)

/-- A line up to a `"\n"` of `s ++ "\n" ++ t` (`s` without one) is `s`. -/
theorem mh_prefix_nl {l s t : List w8} (hl : W8 10 ∉ l) (hs : W8 10 ∉ s)
    (h : l ++ [W8 10] <+: s ++ W8 10 :: t) : l = s := by
  induction l generalizing s with
  | nil =>
    cases s with
    | nil => rfl
    | cons x s =>
      obtain ⟨u, hu⟩ := h
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at hu
      exact absurd (hu.1 ▸ List.mem_cons_self) hs
  | cons y l ih =>
    cases s with
    | nil =>
      obtain ⟨u, hu⟩ := h
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hu
      exact absurd (hu.1 ▸ List.mem_cons_self) hl
    | cons x s =>
      obtain ⟨u, hu⟩ := h
      simp only [List.cons_append, List.append_assoc, List.cons.injEq] at hu
      have hxy : y = x := hu.1
      subst hxy
      have := ih (fun h => hl (List.mem_cons_of_mem _ h)) (fun h => hs (List.mem_cons_of_mem _ h))
        ⟨u, by rw [List.append_assoc]; exact hu.2⟩
      rw [this]

/-- A prefix of `s ++ "\n" ++ t` without a `"\n"` is a prefix of `s` (`s` without one). -/
theorem mh_prefix_no_nl {l s t : List w8} (hl : W8 10 ∉ l) (hs : W8 10 ∉ s)
    (h : l <+: s ++ W8 10 :: t) : l <+: s := by
  induction l generalizing s with
  | nil => exact List.nil_prefix
  | cons y l ih =>
    cases s with
    | nil =>
      obtain ⟨u, hu⟩ := h
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hu
      exact absurd (hu.1 ▸ List.mem_cons_self) hl
    | cons x s =>
      obtain ⟨u, hu⟩ := h
      simp only [List.cons_append, List.cons.injEq] at hu
      have hxy : y = x := hu.1
      subst hxy
      exact List.prefix_cons_inj _ |>.mpr
        (ih (fun h => hl (List.mem_cons_of_mem _ h)) (fun h => hs (List.mem_cons_of_mem _ h))
          ⟨u, hu.2⟩)

theorem mh_takeWhile_length {p : w8 → Bool} : ∀ (l : List w8) (i : Nat),
    (∀ j, j < i → ∃ x, l[j]? = some x ∧ p x = true) →
    (∀ x, l[i]? = some x → p x = false) → (l.takeWhile p).length = i
  | [], i, h2, _ => by
    cases i with
    | zero => rfl
    | succ i => obtain ⟨x, hx, -⟩ := h2 0 (by omega); simp at hx
  | x :: l, 0, _, h3 => by simp [h3 x rfl]
  | x :: l, i + 1, h2, h3 => by
    obtain ⟨y, hy, hpy⟩ := h2 0 (by omega)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
    subst hy
    simp only [List.takeWhile_cons, hpy, ↓reduceIte, List.length_cons, Nat.add_right_cancel_iff]
    exact mh_takeWhile_length l i (fun j hj => by simpa using h2 (j + 1) (by omega))
      (fun z hz => h3 z (by simpa using hz))

theorem mh_drop_takeWhile {p : w8 → Bool} : ∀ (l : List w8), l.drop (l.takeWhile p).length = l.dropWhile p
  | [] => rfl
  | x :: l => by
    by_cases hx : p x = true
    · simp [hx, mh_drop_takeWhile l]
    · simp [hx]

theorem mh_dropWhile_all {p : w8 → Bool} : ∀ (l : List w8), (∀ x ∈ l, p x = true) → l.dropWhile p = []
  | [] => fun _ => rfl
  | x :: l => fun h => by
    simp [h x (by simp), mh_dropWhile_all l (fun y hy => h y (by simp [hy]))]

theorem mh_rtrim_take (xs : List w8) (m : Nat) (hm : m ≤ xs.length)
    (hall : ∀ j x, m ≤ j → xs[j]? = some x → mhWs x = true)
    (hend : m = 0 ∨ ∃ x, xs[m - 1]? = some x ∧ mhWs x = false) :
    mhRtrim xs = xs.take m := by
  unfold mhRtrim
  conv => lhs; rw [← List.take_append_drop m xs]
  rw [List.reverse_append, List.dropWhile_append, mh_dropWhile_all]
  · simp only [List.isEmpty_nil, ↓reduceIte]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp
    rcases hend with h0 | ⟨x, hx, hwx⟩
    · omega
    · have hm0 : m = (m - 1) + 1 := by omega
      rw [hm0, List.take_add_one, hx]
      simp [hwx]
  · intro x hx
    rw [List.mem_reverse] at hx
    obtain ⟨j, hj, hxj⟩ := List.getElem_of_mem hx
    rw [List.getElem_drop] at hxj
    exact hall (m + j) x (by omega)
      (by rw [List.getElem?_eq_getElem (by simp at hj; omega)]; exact congrArg some hxj)

theorem mh_law_tl {r P T q : List w8} (h : r ++ P ++ q <+: r ++ (P ++ T)) : q <+: T := by
  rw [List.append_assoc] at h
  exact (List.prefix_append_right_inj P).1 ((List.prefix_append_right_inj r).1 h)

theorem mh_head_of_prefix {c : w8} {q T : List w8} (h : c :: q <+: T) : ∃ T', T = c :: T' := by
  obtain ⟨u, hu⟩ := h
  exact ⟨q ++ u, by rw [← hu]; rfl⟩

theorem mh_pre_zero (hb : List HdrLine) : mhPre hb 0 = [] := by simp [mhPre]

theorem mh_dropCR_body (kv : HdrLine) : dropCR (mhBody kv) = kv.1 ++ W8 58 :: W8 32 :: kv.2 := by
  unfold dropCR mhBody
  have h1 : (kv.1 ++ [W8 58, W8 32] ++ kv.2 ++ [W8 13]).getLast? = some (W8 13) :=
    List.getLast?_concat
  rw [ite_eq_left_of_eq_true _ _ (eq_true h1), List.dropLast_concat]
  simp

theorem mh_dropCR_eol {eol : List w8} (heol : eol = [] ∨ eol = [W8 13]) : dropCR eol = [] := by
  rcases heol with rfl | rfl <;> decide

theorem mh_eol_no_nl {eol : List w8} (heol : eol = [] ∨ eol = [W8 13]) : W8 10 ∉ eol := by
  rcases heol with rfl | rfl <;> decide

theorem mh_take_len (hb : List HdrLine) : hb.take hb.length = hb := List.take_length

theorem mh_pre_len (hb : List HdrLine) (eol : List w8) :
    mhPre hb hb.length ++ eol ++ [W8 10] = hdrWire hb eol := by
  simp [mhPre, hdrWire]

theorem mh_trim_eq (bs : List w8) (i nn : Nat) (hi1 : (bs.takeWhile mhWs).length = i)
    (hin : i ≤ nn) (hnl : nn ≤ bs.length)
    (hall : ∀ j x, nn ≤ j → bs[j]? = some x → mhWs x = true)
    (hend : nn = i ∨ ∃ x, bs[nn - 1]? = some x ∧ mhWs x = false) :
    mhTrim bs = subslice i nn bs := by
  unfold mhTrim
  rw [← mh_drop_takeWhile, hi1]
  rw [mh_rtrim_take (bs.drop i) (nn - i) (by simp; omega)]
  · simp only [subslice, List.drop_take]
  · intro j x hj hx
    rw [List.getElem?_drop] at hx
    exact hall (i + j) x (by omega) hx
  · by_cases h : nn = i
    · left; omega
    rcases hend with h' | ⟨x, hx, hwx⟩
    · exact absurd h' h
    · right
      refine ⟨x, ?_, hwx⟩
      rw [List.getElem?_drop, show i + (nn - i - 1) = nn - 1 by omega]; exact hx

theorem mh_colon_idx {k w line : List w8} (hk : k.all fieldByte = true) (hw : line = k ++ W8 58 :: w)
    (j : Nat) (hj : line[j]? = some (W8 58))
    (hbefore : ∀ j' x, j' < j → line[j']? = some x → x ≠ W8 58) : j = k.length := by
  subst hw
  rcases Nat.lt_trichotomy j k.length with h | h | h
  · exfalso
    rw [List.getElem?_append_left h] at hj
    have hm := List.mem_of_getElem? hj
    exact (fieldByte_not_ws _ (List.all_eq_true.mp hk _ hm)).2.2.1 rfl
  · exact h
  · exfalso
    exact hbefore k.length (W8 58) h (by simp) rfl

theorem mh_rtrim_cons_nonws (a : List w8) (c : w8) (hc : mhWs c = false) (w : List w8) :
    mhRtrim (a ++ c :: w) = a ++ c :: mhRtrim w := by
  unfold mhRtrim
  have hin : (w.reverse ++ [c]).dropWhile mhWs = w.reverse.dropWhile mhWs ++ [c] := by
    rw [List.dropWhile_append]
    by_cases h : (w.reverse.dropWhile mhWs).isEmpty
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), List.isEmpty_iff.mp h]; simp [hc]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
  rw [List.reverse_append, List.reverse_cons, List.dropWhile_append (xs := w.reverse ++ [c]), hin]
  simp

theorem mh_trim_line {k w : List w8} (hne : k ≠ []) (hk : k.all fieldByte = true) :
    mhTrim (k ++ W8 58 :: w) = k ++ W8 58 :: mhRtrim w := by
  unfold mhTrim
  obtain ⟨k0, ks, rfl⟩ := List.exists_cons_of_ne_nil hne
  have h0 := fieldByte_not_ws k0 (List.all_eq_true.mp hk k0 (by simp))
  have hw0 : mhWs k0 = false := by simp [mhWs]; exact ⟨h0.1, h0.2.1⟩
  rw [List.cons_append, List.dropWhile_cons]
  simp only [hw0, Bool.false_eq_true, ↓reduceIte]
  rw [← List.cons_append]
  exact mh_rtrim_cons_nonws _ _ (by decide) _

theorem mh_proto_ptrTyped [GooseExts] [GoGlobalContext] (msg : GoString) :
    interface.mkOk net.textproto.ProtocolError.ty #msg ≠ GoInterface.nil ∧
      _root_.Perennial.io.ptrTyped (interface.mkOk net.textproto.ProtocolError.ty #msg) := by
  refine ⟨by simp [interface.mkOk], ?_⟩
  intro ii T h hty
  simp only [interface.mkOk, GoInterface.ok.injEq] at h
  subst h
  exfalso
  revert hty
  unfold net.textproto.ProtocolError.ty
  intro hty
  cases hty

theorem mh_succ (i k : w64) (hi0 : 0 ≤ sint.Z i) (hlt : sint.Z i < sint.Z k) :
    sint.nat (i + W64 1) = sint.nat i + 1 ∧ 0 ≤ sint.Z (i + W64 1) := by
  constructor <;> word

theorem mh_rtrim_last {l : List w8} {x : w8} (hl : l.getLast? = some x) (hx : mhWs x = false) :
    mhRtrim l = l := by
  unfold mhRtrim
  obtain ⟨ys, rfl⟩ : ∃ ys, l = ys ++ [x] := by
    have h := List.getLast?_eq_some_iff.mp hl
    exact h
  simp [hx]

theorem valByte_ws : ∀ c : w8, valByte c = true → c ≠ W8 32 → mhWs c = false := by decide

theorem mh_val_whole {kv : HdrLine} (hlo : hdrLineOk kv) : mhVal (W8 32 :: kv.2) = kv.2 := by
  obtain ⟨-, -, -, hv, hhead, hlast⟩ := hlo
  unfold mhVal
  cases h : kv.2.getLast? with
  | none =>
    have : kv.2 = [] := List.getLast?_eq_none_iff.mp h
    rw [this]; decide
  | some y =>
    have hy : y ∈ kv.2 := List.mem_of_getLast? h
    have hwy : mhWs y = false := valByte_ws y (List.all_eq_true.mp hv _ hy) (fun he => hlast (he ▸ h))
    have hl : (W8 32 :: kv.2).getLast? = some y := by
      rw [List.getLast?_cons, h]; rfl
    rw [mh_rtrim_last hl hwy]
    obtain ⟨z, zs, hz⟩ := List.exists_cons_of_ne_nil (show kv.2 ≠ [] by intro he; rw [he] at h; simp at h)
    have hz0 : mhWs z = false := valByte_ws z (List.all_eq_true.mp hv _ (by rw [hz]; simp))
      (fun he => hhead (by rw [hz, he]; rfl))
    have h32 : mhWs (W8 32) = true := by decide
    rw [hz]
    simp only [List.dropWhile_cons, h32, hz0, ↓reduceIte, Bool.false_eq_true]

theorem mh_key_fresh {hb : List HdrLine} (hok : hdrBlockOk hb) {n : Nat} (hn : n < hb.length) :
    hb[n].fst ∉ (hb.take n).map Prod.fst := by
  have hnd := hok.1
  rw [← List.take_append_drop n hb, List.map_append, List.nodup_append] at hnd
  intro hm
  have hm2 : hb[n].fst ∈ (hb.drop n).map Prod.fst := by
    have : (hb.drop n).map Prod.fst = hb[n].fst :: (hb.drop (n + 1)).map Prod.fst := by
      rw [List.drop_eq_getElem_cons hn]; rfl
    rw [this]; exact List.mem_cons_self
  exact hnd.2.2 _ hm _ hm2 rfl

theorem mh_take_succ (hb : List HdrLine) (n : Nat) (hn : n < hb.length) :
    hb.take (n + 1) = hb.take n ++ [(hb[n].fst, hb[n].snd)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn]; rfl

theorem mh_cut_cases {kv : HdrLine} (hlo : hdrLineOk kv) {l : List w8} (hl : l <+: mhBody kv) :
    (∀ x ∈ l, x ≠ W8 58) ∨ ∃ w, l = kv.1 ++ W8 58 :: w := by
  rw [List.prefix_iff_eq_take] at hl
  unfold mhBody at hl
  have hb : kv.1 ++ [W8 58, W8 32] ++ kv.2 ++ [W8 13] =
      kv.1 ++ W8 58 :: (W8 32 :: (kv.2 ++ [W8 13])) := by simp
  rw [hb, List.take_append] at hl
  by_cases hle : l.length ≤ kv.1.length
  · left
    rw [Nat.sub_eq_zero_of_le hle, List.take_zero, List.append_nil] at hl
    intro x hx he
    rw [hl] at hx
    have hm := List.mem_of_mem_take hx
    exact (fieldByte_not_ws _ (List.all_eq_true.mp hlo.2.1 _ hm)).2.2.1 he
  · right
    rw [List.take_of_length_le (by omega : kv.1.length ≤ l.length)] at hl
    obtain ⟨m, hm⟩ : ∃ m, l.length - kv.1.length = m + 1 := ⟨l.length - kv.1.length - 1, by omega⟩
    rw [hm, List.take_succ_cons] at hl
    exact ⟨_, hl⟩

theorem mh_cut_eol {eol rest l : List w8} (heol : eol = [] ∨ eol = [W8 13]) (hne : l ≠ [])
    (hl10 : W8 10 ∉ l) (hl : l <+: eol ++ W8 10 :: rest) : ∀ x ∈ l, x ≠ W8 58 := by
  have h := mh_prefix_no_nl hl10 (mh_eol_no_nl heol) hl
  rcases heol with rfl | rfl
  · exact absurd (List.prefix_nil.1 h) hne
  · intro x hx he
    subst he
    have := h.subset hx
    simp at this

open Classical in
/-- The bytes `bs` of the `[]byte` argument `sl`, lent to `fmt.Sprintf`. -/
noncomputable def mhB [GooseExts] [GoGlobalContext] (sl : GoSlice) (bs : List w8) :
    GoInterface → Option fmt.Lent :=
  fun x => if x = interface.mkOk (go.SliceType go.byte) #sl then some (.bytes bs) else none

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

set_option goose.wp.extras true

/-- `fmt.Sprintf` with the bytes of its `[]byte` arguments lent (Perennial's
`fmt.wp_Sprintf_bytes`). -/
abbrev SprintfBytes.law : Prop :=
  ∀ (B : GoInterface → Option fmt.Lent) (dqb : DFrac) (format : GoString) (args_sl : GoSlice)
    (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗ fmt.bytesOwn dqb B xs ∗
      fmt.argsOkB B fmt.methodVerbs format xs }}
    (App (App (Val (@! fmt.Sprintf)) (Val #format)) (Val #args_sl))
  {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗ fmt.bytesOwn dqb B xs ∗
      ⌜fmt.SprintfOutB B format xs s⌝ }}

set_option hygiene false in
local macro "tl_inv" : tactic => `(tactic| (
  iframe; iexists _; iframe; ipureintro
  have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
  rw [hn]
  refine ⟨by word, by omega, fun j hj => ?_⟩
  rcases Nat.lt_or_ge j (sint.nat i) with h | h
  · exact Hi.2.2 j h
  · have : j = sint.nat i := by omega
    subst this; exact ⟨_, hx, by first | decide | simp_all [mhWs]⟩))

set_option hygiene false in
local macro "tl_inv2" : tactic => `(tactic| (
  iframe; iexists _; iframe; ipureintro
  have hn1 : sint.nat (nn - W64 1) = sint.nat nn - 1 := by word
  rw [hn1]
  refine ⟨by word, by word, by omega, fun j y hj hy => ?_⟩
  rcases Nat.lt_or_ge j (sint.nat nn) with h | h
  · have : j = sint.nat nn - 1 := by omega
    subst this; rw [hx] at hy; cases hy; first | decide | simp_all [mhWs]
  · exact Hn.2.2.2 j y h hy))

set_option hygiene false in
local macro "tl_fin" : tactic => `(tactic| (
  have hb3 : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z nn ∧ sint.Z nn ≤ sint.Z sl.len := by
    refine ⟨Hi.1, by word, by have := Hl.1; word⟩
  have hb3' : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z nn ∧ sint.Z nn ≤ sint.Z sl.cap :=
    ⟨hb3.1, hb3.2.1, by have := Hwf.2; omega⟩
  try simp only [hb3', and_self, ↓reduceIte]
  try wp_auto
  icases (ownSlice_slice i nn sl DFrac.discard bs hb3).1 $$ Hs with ⟨-, #Hmid, -⟩
  iapply HΦ
  rw [mh_trim_eq bs (sint.nat i) (sint.nat nn) hi1 Hn.2.1 Hn.2.2.1 Hn.2.2.2 hend]
  iexact Hmid))

set_option hygiene false in
local macro "tl_loop2" : tactic => `(tactic| (
  ihave HN : (∃ (nn : w64), "n" ∷ n_ptr ↦ nn ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z nn ∧ sint.nat i ≤ sint.nat nn ∧ sint.nat nn ≤ bs.length ∧
        ∀ j x, sint.nat nn ≤ j → bs[j]? = some x → mhWs x = true⌝ : IProp GF) $$ [n]
  · iexists _
    iframe
    ipureintro
    refine ⟨Hl.2, by have := Hl.1; word, by have := Hl.1; word, fun j x hj hx => ?_⟩
    exfalso
    have := (List.getElem?_eq_some_iff.mp hx).1
    have := Hl.1
    omega
  wp_for HN
  by_cases hgt : sint.Z i < sint.Z nn
  · simp only [hgt, _root_.decide_true]
    have hk : sint.nat nn - 1 < bs.length := by have := Hn.2.2.1; word
    obtain ⟨x, hx⟩ : ∃ x, bs[sint.nat nn - 1]? = some x := ⟨_, List.getElem?_eq_getElem hk⟩
    have h0 : 0 ≤ sint.Z (nn - W64 1) := by word
    have hb0 : 0 ≤ sint.Z (nn - W64 1) ∧ sint.Z (nn - W64 1) < sint.Z sl.len := by
      refine ⟨h0, ?_⟩; have := Hl.1; have := Hn.2.2.1; word
    have hxi : bs[(sint.Z (nn - W64 1)).toNat]? = some x := by
      rw [show (sint.Z (nn - W64 1)).toNat = sint.nat nn - 1 by word]; exact hx
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb0)]
    wp_apply (wp_load_slice_index sl (sint.Z (nn - W64 1)) bs DFrac.discard x h0) $$ [Hs] as -
    · iframe Hs; ipureintro; exact hxi
    try wp_auto
    wp_if_destruct
    · try wp_auto
      cleanup_bool_decide
      try wp_auto
      wp_for_post
      tl_inv2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hb0)]
      wp_apply (wp_load_slice_index sl (sint.Z (nn - W64 1)) bs DFrac.discard x h0) $$ [Hs] as -
      · iframe Hs; ipureintro; exact hxi
      try wp_auto
      cleanup_bool_decide
      by_cases h9 : x = W8 9
      · rw [decide_eq_true h9]
        cleanup_bool_decide
        try wp_auto
        wp_for_post
        tl_inv2
      · rw [decide_eq_false h9]
        cleanup_bool_decide
        try wp_auto
        cleanup_bool_decide
        try wp_auto
        have hend : sint.nat nn = sint.nat i ∨ ∃ x, bs[sint.nat nn - 1]? = some x ∧ mhWs x = false :=
          Or.inr ⟨x, hx, by simp [mhWs]; exact ⟨Hif, h9⟩⟩
        tl_fin
  · simp only [hgt, decide_false]
    try wp_auto
    rw [decide_eq_false false_neq_true]
    cleanup_bool_decide
    try wp_auto
    cleanup_bool_decide
    try wp_auto
    have hend : sint.nat nn = sint.nat i ∨ ∃ x, bs[sint.nat nn - 1]? = some x ∧ mhWs x = false :=
      Or.inl (by have := Hn.2.1; word)
    tl_fin))

theorem wp_trimLine (sl : GoSlice) (bs : List w8) :
    {{ (sl ↦*□ bs : IProp GF) }}
      (App (Val (@! net.http.trimLine)) (Val #sl))
    {{ (sl' : GoSlice), RET #sl'; sl' ↦*□ (mhTrim bs) }} := by
  wp_start as #Hs
  ihave %Hl := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ bs.length ∧
        ∀ j, j < sint.nat i → ∃ x, bs[j]? = some x ∧ mhWs x = true⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    refine ⟨by word, by word, fun j hj => ?_⟩
    exfalso; revert hj; word
  wp_for HI
  by_cases hlt : sint.Z i < sint.Z sl.len
  · simp only [hlt, _root_.decide_true]
    have hi : sint.nat i < bs.length := by have := Hl.1; word
    obtain ⟨x, hx⟩ : ∃ x, bs[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, hlt⟩)]
    wp_apply (wp_load_slice_index sl (sint.Z i) bs DFrac.discard x Hi.1) $$ [Hs] as -
    · iframe Hs; ipureintro; exact hx
    try wp_auto
    wp_if_destruct
    · try wp_auto
      cleanup_bool_decide
      try wp_auto
      wp_for_post
      tl_inv
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, hlt⟩)]
      wp_apply (wp_load_slice_index sl (sint.Z i) bs DFrac.discard x Hi.1) $$ [Hs] as -
      · iframe Hs; ipureintro; exact hx
      try wp_auto
      cleanup_bool_decide
      by_cases h9 : x = W8 9
      · rw [decide_eq_true h9]
        simp only [↓reduceIte]
        try wp_auto
        wp_for_post
        tl_inv
      · rw [decide_eq_false h9]
        cleanup_bool_decide
        try wp_auto
        cleanup_bool_decide
        try wp_auto
        have hi1 : (bs.takeWhile mhWs).length = sint.nat i :=
          mh_takeWhile_length bs _ Hi.2.2 (fun y hy => by
            rw [hx] at hy; cases hy; simp [mhWs]; exact ⟨Hif, h9⟩)
        tl_loop2
  · simp only [hlt, decide_false]
    try wp_auto
    rw [decide_eq_false false_neq_true]
    cleanup_bool_decide
    try wp_auto
    cleanup_bool_decide
    try wp_auto
    have hi1 : (bs.takeWhile mhWs).length = sint.nat i :=
      mh_takeWhile_length bs _ Hi.2.2 (fun y hy => by
        exfalso
        have := (List.getElem?_eq_some_iff.mp hy).1
        have := Hl.1
        apply hlt; word)
    tl_loop2

set_option hygiene false in
/-- The check after a `Peek(1)` that saw `c` (`Hs`), given `Hnl` (`c` is no space or tab, and the
reader back at `rc`): both comparisons fail; `Hb` the reader. -/
local macro "mh_peek_check" : tactic => `(tactic| (
  ihave %Hsl := ownSlice_len $$ Hs
  have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len := by
    have hl := Hsl.1
    simp only [List.length_singleton] at hl
    constructor
    · decide
    · have : sint.nat s.len = 1 := hl.symm
      revert this; word
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
  wp_apply (wp_load_slice_index s (sint.Z (W64 0)) [c] (DFrac.own 1) c (by decide)) $$ [Hs] as Hs
  · iframe; ipureintro; rfl
  try wp_auto
  wp_if_destruct
  · icases Hnl $$ Hs with ⟨%hc, -⟩
    exact absurd rfl hc.1
  rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
  wp_apply (wp_load_slice_index s (sint.Z (W64 0)) [c] (DFrac.own 1) c (by decide)) $$ [Hs] as Hs
  · iframe; ipureintro; rfl
  try wp_auto
  wp_if_destruct
  · icases Hnl $$ Hs with ⟨%hc, -⟩
    exact absurd rfl hc.2
  icases Hnl $$ Hs with ⟨-, Hb⟩
  try wp_auto))

set_option hygiene false in
/-- `modelReadLine` returned the stream's error `err` (`He`, `HE`): the loop returns it. -/
local macro "mh_ret_err" : tactic => `(tactic| (
  obtain ⟨i, rfl⟩ : ∃ i, err = GoInterface.ok i := by
    cases err with
    | nil => exact absurd rfl He
    | ok i => exact ⟨i, rfl⟩
  iunfold EtcdGrove.io.errAt at HE
  icases HE with ⟨(%Hen | #HEe), %Hty⟩
  · exact absurd Hen He
  try wp_auto
  wp_for_post
  iapply HΦ
  ileft
  isplitr
  · ipureintro; exact ⟨He, Hty⟩
  iunfold mimeErr
  ileft
  iexists _
  iexact HEe))

theorem mh_hdrOwn_snoc (mp : Loc) (l : List HdrLine) (ms : GMap GoString GoSlice) (K v : GoString)
    (s' : GoSlice) (hdom : ∀ k, (ms !! k).isSome = decide (k ∈ l.map Prod.fst))
    (hK : K ∉ l.map Prod.fst) :
    mp ↦$ (<[K := s']> ms) ∗
      ([∗list] kv ∈ l, ∃ s : GoSlice, ⌜ms !! kv.1 = some s⌝ ∗ s ↦* ([kv.2] : List GoString)) ∗
      s' ↦* ([v] : List GoString) ⊢ hdrOwn (GF := GF) mp (l ++ [(K, v)]) := by
  iintro ⟨Hm, Hels, Hs⟩
  iunfold hdrOwn
  iexists _
  iframe Hm
  isplitr
  · ipureintro
    intro k
    by_cases hk : k = K
    · subst hk; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), hdom k]
      simp [hk]
  iapply BigSepL.bigSepL_snoc.2
  isplitl [Hels]
  · iapply (BigSepL.bigSepL_mono (Φ := fun _ (kv : HdrLine) =>
        iprop(∃ s : GoSlice, ⌜ms !! kv.1 = some s⌝ ∗ s ↦* ([kv.2] : List GoString)))
      (fun {k x} hx => ?_)) $$ Hels
    have hne : x.1 ≠ K := by
      intro he; apply hK; rw [← he]; exact List.mem_map_of_mem (List.mem_of_getElem? hx)
    iintro ⟨%s, %hs, Hs⟩
    iexists s
    iframe Hs
    ipureintro
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hs
  · iexists s'
    iframe Hs
    ipureintro
    exact GMap.lookup_insert _ _ _

theorem mh_sprintfB_pre (sl : GoSlice) (bs : List w8) (fs : GoString)
    (hfs : fmt.fmtDirectives fs = some [⟨W8 113, false⟩]) :
    (sl ↦*□ bs : IProp GF) ⊢
      fmt.bytesOwn DFrac.discard (mhB sl bs) [interface.mkOk (go.SliceType go.byte) #sl] ∗
      fmt.argsOkB (mhB sl bs) fmt.methodVerbs fs [interface.mkOk (go.SliceType go.byte) #sl] := by
  iintro #Hs
  have hB : mhB sl bs (interface.mkOk (go.SliceType go.byte) #sl) = some (.bytes bs) := by
    simp [mhB]
  isplitl []
  · unfold fmt.bytesOwn
    iapply BigSepL.bigSepL_singleton.2
    iapply (fmt.bytesArgOwn_some hB).2
    iexists ⟨go.SliceType go.byte, #sl⟩, sl
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    · iexact Hs
  · unfold fmt.argsOkB
    iright
    iexists [⟨W8 113, false⟩]
    isplitr
    · ipureintro; exact hfs
    unfold fmt.argsOkAtB fmt.argOkAtB
    isplitl []
    · iright; ipureintro; simp [hB]
    · unfold fmt.argsOkAtB; itrivial

set_option hygiene false in
local macro "mh_skip_inv" : tactic => `(tactic| (
  iframe; iexists _; iframe; ipureintro
  have hn : sint.nat (t + W64 1) = sint.nat t + 1 := by word
  rw [hn]
  refine ⟨by word, by omega, fun j hj => ?_⟩
  rcases Nat.lt_or_ge j (sint.nat t) with h | h
  · exact Ht.2.2 j h
  · have : j = sint.nat t := by omega
    subst this; exact ⟨_, hx, by first | decide | simp_all [mhWs]⟩))

set_option hygiene false in
/-- The loop returned a `ProtocolError` of message `msg`. -/
local macro "mh_proto_post" : tactic => `(tactic| (
  isplitr
  · ipureintro; exact mh_proto_ptrTyped msg
  iunfold mimeErr
  iright
  ipureintro
  exact ⟨msg, rfl⟩))

set_option hygiene false in
/-- The new header line's insertion into the map (after the value's skip loop), then `fin`. -/
local macro "mh_ins" fin:tacticSeq : tactic => `(tactic| (
  iunfold hdrOwn at Hown
  icases Hown with ⟨%ms, Hms, %Hdom, Hels⟩
  have hKf := mh_key_fresh hok hnlt
  have hKn : ms !! hb[n].fst = none := by
    have := Hdom hb[n].fst
    rw [decide_eq_false hKf] at this
    cases h : ms !! hb[n].fst with
    | none => rfl
    | some _ => rw [h] at this; cases this
  wp_apply (wp_map_lookup1 (V := GoSlice) go.string (go.SliceType go.string) mp ms
    hb[n].fst _) $$ Hms as Hms
  rw [hKn]
  simp only [Option.getD_none]
  try wp_auto
  ihave %HvW := ownSlice_wf $$ Hv
  have hbs : 0 ≤ sint.Z t ∧ sint.Z t ≤ sint.Z (kv2.len - (i + W64 1)) ∧
      sint.Z (kv2.len - (i + W64 1)) ≤ sint.Z (kv2.cap - (i + W64 1)) := by
    refine ⟨Ht.1, ?_, ?_⟩
    · have := Ht.2.1; rw [hrl] at this; word
    · exact HvW.2
  rw [ite_eq_left_of_eq_true _ _ (eq_true hbs)]
  icases (ownSlice_slice t (kv2.len - (i + W64 1)) _ DFrac.discard (mhRtrim w)
    ⟨hbs.1, hbs.2.1, Int.le_refl _⟩).1 $$ Hv with ⟨-, #Hval, -⟩
  have hval : subslice (sint.nat t) (sint.nat (kv2.len - (i + W64 1))) (mhRtrim w) =
      mhVal w := by
    unfold subslice mhVal
    rw [← hrl, List.take_length, ← hti1, mh_drop_takeWhile]
  rw [hval]
  wp_apply (wp_bytes_to_string _ _ DFrac.discard) $$ [Hval] as -
  · iexact Hval
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  try wp_auto
  ihave Hnil := ownSlice_nil (V := GoString) (DFrac.own 1)
  ihave Hcap := ownSliceCap_nil (V := GoString)
  rw [show (zero_val GoSlice) = slice.nil from rfl]
  wp_apply (wp_slice_append (V := GoString) slice.nil [] _ _ (DFrac.own 1))
    $$ [Hnil Hcap Hsl2] as %s' ⟨Hs', -, -⟩
  · iframe Hsl2
    isplitl []
    · iexact Hnil
    · iexact Hcap
  try wp_auto
  wp_apply (wp_mapInsert go.string mp ms hb[n].fst s') $$ Hms as Hms
  try wp_auto
  wp_for_post
  ($fin)))

set_option hygiene false in
/-- A line `k:w` after the `Peek(1)` check: `trimLine`, the name and value, their checks, the
insertion (`mh_ins`), then `fin`. -/
local macro "mh_after" fin:tacticSeq : tactic => `(tactic| (
  wp_apply (wp_trimLine kv line) $$ [Hkv] as %kv2 #Hkv2
  · iexact Hkv
  rw [hw, mh_trim_line hlo.1 hlo.2.1]
  try wp_auto
  obtain ⟨line2, hL2⟩ : ∃ line2, hb[n].fst ++ W8 58 :: mhRtrim w = line2 := ⟨_, rfl⟩
  rw [hL2]
  ihave %Hkl2 := ownSlice_len $$ Hkv2
  ihave HC2 : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ line2.length ∧
        ∀ j x, j < sint.nat i → line2[j]? = some x → x ≠ W8 58⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    refine ⟨by word, by word, fun j x hj => ?_⟩
    exfalso; revert hj; word
  wp_for HC2
  by_cases hlt2 : sint.Z i < sint.Z kv2.len
  · simp only [hlt2, _root_.decide_true, ↓reduceIte, ite_true]
    have hi : sint.nat i < line2.length := by have := Hkl2.1; word
    obtain ⟨x, hx⟩ : ∃ x, line2[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, hlt2⟩)]
    wp_apply (wp_load_slice_index kv2 (sint.Z i) line2 DFrac.discard x Hi.1) $$ [Hkv2] as -
    · iframe Hkv2; ipureintro; exact hx
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_for_post
      have hj2 := mh_colon_idx hlo.2.1 hL2.symm (sint.nat i) hx Hi.2.2
      have hlen2 : line2.length = hb[n].fst.length + 1 + (mhRtrim w).length := by
        rw [← hL2]; simp; omega
      have hb1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z i ∧ sint.Z i ≤ sint.Z kv2.len := by
        refine ⟨by decide, Hi.1, ?_⟩; have := Hkl2.1; word
      ihave %Hwf2 := ownSlice_wf $$ Hkv2
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hb1.1, hb1.2.1, by omega⟩)]
      try wp_auto
      have hb2 : 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ sint.Z kv2.len ∧
          sint.Z kv2.len ≤ sint.Z kv2.len := by
        refine ⟨by word, ?_, Int.le_refl _⟩; have := Hkl2.1; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hb2.1, hb2.2.1, Hwf2.2⟩)]
      try wp_auto
      icases (ownSlice_slice (W64 0) i kv2 DFrac.discard line2 hb1).1 $$ Hkv2 with ⟨-, #Hk, -⟩
      icases (ownSlice_slice (i + W64 1) kv2.len kv2 DFrac.discard line2 hb2).1 $$ Hkv2
        with ⟨-, #Hv, -⟩
      have hK : subslice (sint.nat (W64 0)) (sint.nat i) line2 = hb[n].fst := by
        rw [← hL2, hj2, show sint.nat (W64 0) = 0 from rfl]; simp [subslice]
      have hV : subslice (sint.nat (i + W64 1)) (sint.nat kv2.len) line2 = mhRtrim w := by
        have h1 : sint.nat (i + W64 1) = hb[n].fst.length + 1 := by word
        have h2 : sint.nat kv2.len = line2.length := Hkl2.1.symm
        rw [h1, h2, ← hL2]; unfold subslice; rw [List.take_of_length_le (Nat.le_of_eq (by simp))]; simp
      rw [hK, hV]
      ihave %HkL := ownSlice_len $$ Hk
      ihave HR : (∃ (j : w64) (cv : w8), "i" ∷ i_ptr ↦ j ∗ "c" ∷ c_ptr ↦ cv ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j⌝ : IProp GF) $$ [i c]
      · iexists W64 0, _; iframe; ipureintro; decide
      wp_for HR
      by_cases hjl : sint.Z j < sint.Z (i - W64 0)
      · rw [decide_eq_true hjl]
        (try rw [decide_eq_true (rfl : (#true : val) = #true)]); cleanup_bool_decide
        have hjn : sint.nat j < hb[n].fst.length := by
          rw [← hj2]; have h := hjl; rw [show i - W64 0 = i by simp] at h; word
        obtain ⟨x, hx⟩ : ∃ x, hb[n].fst[sint.nat j]? = some x :=
          ⟨_, List.getElem?_eq_getElem hjn⟩
        wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj, hjl⟩)]
        wp_apply (wp_load_slice_index _ (sint.Z j) hb[n].fst DFrac.discard x Hj) $$ [Hk] as -
        · iframe Hk; ipureintro; exact hx
        try wp_auto
        wp_if_destruct
        · exfalso
          have hm := List.mem_of_getElem? hx
          exact (fieldByte_not_ws _ (List.all_eq_true.mp hlo.2.1 _ hm)).1 rfl
        try wp_auto
        wp_for_post
        iframe; iexists _, _; iframe; ipureintro; word
      · rw [decide_eq_false hjl]
        (try rw [decide_eq_true (rfl : (#true : val) = #true)]); cleanup_bool_decide
        try wp_auto
        wp_apply (wp_bytes_to_string _ _ DFrac.discard) $$ [Hk] as -
        · iexact Hk
        wp_apply wp_VHFN $$ Htab
        have hvn : (!hb[n].fst.isEmpty && hb[n].fst.all fieldByte) = true := by
          have : hb[n].fst.isEmpty = false := by
            cases h : hb[n].fst with
            | nil => exact absurd h hlo.1
            | cons _ _ => rfl
          rw [this, hlo.2.1]; rfl
        rw [hvn]
        try wp_auto
        wp_apply (wp_bytes_to_string _ _ DFrac.discard) $$ [Hk] as -
        · iexact Hk
        wp_apply wp_Canon
        · ipureintro; exact hlo.2.2.1
        try wp_auto
        wp_apply (wp_bytes_to_string _ _ DFrac.discard) $$ [Hv] as -
        · iexact Hv
        wp_apply wp_VHFV
        obtain ⟨vb, hvb⟩ : ∃ vb, (mhRtrim w).all (fun c =>
            decide (32 ≤ c.toNat ∧ c.toNat ≠ 127) || decide (c = W8 9)) = vb := ⟨_, rfl⟩
        rw [hvb]
        cases vb
        · -- an invalid value: a `ProtocolError`
          simp only [Bool.not_false]
          try wp_auto
          have hb3 : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z kv2.len ∧ sint.Z kv2.len ≤ sint.Z kv2.cap :=
            ⟨hb1.2.1, hb1.2.2, Hwf2.2⟩
          rw [ite_eq_left_of_eq_true _ _ (eq_true hb3)]
          try wp_auto
          icases (ownSlice_slice i kv2.len kv2 DFrac.discard line2 ⟨hb1.2.1, hb1.2.2, Int.le_refl _⟩).1
            $$ Hkv2 with ⟨-, #Hc, -⟩
          wp_apply (wp_bytes_to_string _ _ DFrac.discard) $$ [Hc] as -
          · iexact Hc
          try wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl ⟨Hsl, -⟩
          try wp_auto
          wp_apply wp_Sprintf _ _ _ _ $$ [Hsl] as %msg -
          · isplitl [Hsl]
            · iexact Hsl
            iapply fmt.argsOk_of_argsWf
            exact fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil
          try wp_auto
          wp_for_post
          iapply HΦ
          ileft
          mh_proto_post
        · simp only [Bool.not_true]
          try wp_auto
          rw [decide_eq_false (show ¬ sint.Z (mh - W64 1) < sint.Z (W64 0) by word)]
          (try rw [decide_eq_true (rfl : (#true : val) = #true)]); cleanup_bool_decide
          try wp_auto
          ihave %HvL := ownSlice_len $$ Hv
          ihave HT : (∃ (t : w64), "i" ∷ i_ptr ↦ t ∗
              "%Ht" ∷ ⌜0 ≤ sint.Z t ∧ sint.nat t ≤ (mhRtrim w).length ∧
                ∀ j, j < sint.nat t → ∃ x, (mhRtrim w)[j]? = some x ∧ mhWs x = true⌝ :
                IProp GF) $$ [i]
          · iexists W64 0
            iframe
            ipureintro
            refine ⟨by word, by word, fun j hj => ?_⟩
            exfalso; revert hj; word
          wp_for HT
          have hrl : (mhRtrim w).length = sint.nat (kv2.len - (i + W64 1)) := by
            have := Hkl2.1; word
          by_cases htl : sint.Z t < sint.Z (kv2.len - (i + W64 1))
          · rw [decide_eq_true htl]
            (try rw [decide_eq_true (rfl : (#true : val) = #true)]); cleanup_bool_decide
            have hti : sint.nat t < (mhRtrim w).length := by rw [hrl]; word
            obtain ⟨x, hx⟩ : ∃ x, (mhRtrim w)[sint.nat t]? = some x :=
              ⟨_, List.getElem?_eq_getElem hti⟩
            wp_auto
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Ht.1, htl⟩)]
            wp_apply (wp_load_slice_index _ (sint.Z t) (mhRtrim w) DFrac.discard x Ht.1) $$ [Hv] as -
            · iframe Hv; ipureintro; exact hx
            try wp_auto
            wp_if_destruct
            · try wp_auto
              (try rw [decide_eq_true (rfl : (#true : val) = #true)]); cleanup_bool_decide
              try wp_auto
              wp_for_post
              mh_skip_inv
            · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Ht.1, htl⟩)]
              wp_apply (wp_load_slice_index _ (sint.Z t) (mhRtrim w) DFrac.discard x Ht.1) $$ [Hv] as -
              · iframe Hv; ipureintro; exact hx
              try wp_auto
              (try rw [decide_eq_true (rfl : (#true : val) = #true)]); cleanup_bool_decide
              by_cases h9 : x = W8 9
              · rw [decide_eq_true h9]
                (try rw [decide_eq_true (rfl : (#true : val) = #true)]); cleanup_bool_decide
                try wp_auto
                wp_for_post
                mh_skip_inv
              · rw [decide_eq_false h9]
                (try rw [decide_eq_true (rfl : (#true : val) = #true)]); cleanup_bool_decide
                try wp_auto
                (try rw [decide_eq_true (rfl : (#true : val) = #true)]); cleanup_bool_decide
                try wp_auto
                have hti1 : ((mhRtrim w).takeWhile mhWs).length = sint.nat t :=
                  mh_takeWhile_length _ _ Ht.2.2 (fun y hy => by
                    rw [hx] at hy; cases hy; simp [mhWs]; exact ⟨Hif, h9⟩)
                mh_ins $fin
          · rw [decide_eq_false htl]
            (try rw [decide_eq_true (rfl : (#true : val) = #true)]); cleanup_bool_decide
            try wp_auto
            rw [decide_eq_false false_neq_true]
            (try rw [decide_eq_true (rfl : (#true : val) = #true)]); cleanup_bool_decide
            try wp_auto
            (try rw [decide_eq_true (rfl : (#true : val) = #true)]); cleanup_bool_decide
            try wp_auto
            have htt : sint.nat t = (mhRtrim w).length := by
              have h1 := Ht.2.1; rw [hrl] at h1 ⊢; word
            have hti1 : ((mhRtrim w).takeWhile mhWs).length = sint.nat t :=
              mh_takeWhile_length _ _ Ht.2.2 (fun y hy => by
                rw [htt, List.getElem?_eq_none (Nat.le_refl _)] at hy; cases hy)
            mh_ins $fin
    · wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      have hn := mh_succ i kv2.len Hi.1 hlt2
      rw [hn.1]
      refine ⟨hn.2, by omega, fun j y hj hy => ?_⟩
      rcases Nat.lt_or_ge j (sint.nat i) with h | h
      · exact Hi.2.2 j y h hy
      · have : j = sint.nat i := by omega
        subst this; rw [hx] at hy; cases hy; assumption
  · exfalso
    have hi : sint.nat i = line2.length := by have := Hkl2.1; word
    have hk := Hi.2.2 hb[n].fst.length (W8 58) (by rw [hi, ← hL2]; simp)
      (by rw [← hL2]; simp)
    exact hk rfl
  ))
set_option hygiene false in
/-- The header loop, from the reader at `r` (`Hb`), the map empty (`Hmp`). -/
local macro "mh_loop" : tactic => `(tactic| (
  ihave HI : (∃ (mh : w64), "maxHeaders" ∷ maxHeaders_ptr ↦ mh ∗ "Hmode" ∷ (
      (∃ n : Nat, ⌜n ≤ hb.length ∧ sint.Z mh = sint.Z maxH - n⌝ ∗ hdrOwn mp (hb.take n) ∗
        EtcdGrove.bufio.ownReader b ri S E (r ++ mhPre hb n)) ∨
      (∃ (r1 : List w8) (e1 : GoInterface) (ms : GMap GoString GoSlice), □ E r1 e1 ∗
        EtcdGrove.bufio.ownReader b ri S E r1 ∗ mp ↦$ ms)) : IProp GF) $$ [maxHeaders Hmp Hb]
  · iexists maxH
    iframe
    ileft
    iexists 0
    isplitr
    · ipureintro; simp
    rw [mh_pre_zero, List.append_nil]
    iframe Hb
    iunfold hdrOwn
    iexists ∅
    iframe Hmp
    isplitr
    · ipureintro; intro k; simp
    · simp only [List.take_zero]; iapply BigSepL.bigSepL_nil.2; iempintro
  wp_for HI
  try simp only [decide_true, ↓reduceIte]
  try wp_auto
  icases Hmode with (⟨%n, ⟨%hn, %hmh⟩, Hown, Hb⟩ | ⟨%r1, %e1, %ms, #HE1, Hb, Hms⟩)
  · ihave #HRL := wp_modelReadLine b ri S E (r ++ mhPre hb n) $$ Hrd HSb
    wp_apply HRL $$ Hb as %line %err ⟨%l, %Hl, (⟨⟨%Herr, %Hline⟩, Hb⟩ | ⟨%e, %He, #HE, Hb, %Hc⟩)⟩
    · -- a whole line
      subst Herr Hline
      ihave ⟨%q', HS, Hcl⟩ := EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb
      ihave %hq := Htl $$ %n %(l ++ [W8 10] ++ q') [HS]
      · simp only [List.append_assoc]; iexact HS
      ihave Hb := Hcl $$ HS
      rcases Nat.lt_or_ge n hb.length with hnlt | hge
      · have hlo := mh_line_ok hok hnlt
        have hmh1 : 1 ≤ sint.Z mh := by omega
        rw [mh_tl_lt hb eol rest n hnlt] at hq
        have hl : l = mhBody hb[n] :=
          mh_prefix_nl Hl (mh_body_no_nl hlo) ((List.prefix_append _ _).trans (by simpa using hq))
        subst hl
        rw [mh_dropCR_body]
        obtain ⟨line, hL⟩ : ∃ line, hb[n].fst ++ W8 58 :: W8 32 :: hb[n].snd = line := ⟨_, rfl⟩
        rw [hL]
        obtain ⟨w, hwd⟩ : ∃ w, W8 32 :: hb[n].snd = w := ⟨_, rfl⟩
        have hw : line = hb[n].fst ++ W8 58 :: w := by rw [← hL, hwd]
        try wp_auto
        wp_apply (wp_string_len (t := go.string) line) as %Hlen
        have hne : line ≠ [] := by rw [← hL]; simp
        have hne' : W64 (line.length : Int) ≠ W64 0 := by
          intro h; apply hne; apply List.eq_nil_of_length_eq_zero; revert h; word
        rw [decide_eq_false hne']
        try wp_auto
        wp_apply (wp_string_to_bytes line) as %kv ⟨Hkv, -⟩
        imod ownSlice_persist _ _ _ $$ Hkv with #Hkv
        try wp_auto
        ihave HC : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
            "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ line.length ∧
              ∀ j x, j < sint.nat i → line[j]? = some x → x ≠ W8 58⌝ : IProp GF) $$ [i]
        · iexists W64 0
          iframe
          ipureintro
          refine ⟨by word, by word, fun j x hj => ?_⟩
          exfalso; revert hj; word
        ihave %Hkl := ownSlice_len $$ Hkv
        wp_for HC
        by_cases hlt : sint.Z i < sint.Z kv.len
        · simp only [hlt, _root_.decide_true, ↓reduceIte]
          have hi : sint.nat i < line.length := by have := Hkl.1; word
          obtain ⟨x, hx⟩ : ∃ x, line[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
          wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, hlt⟩)]
          wp_apply (wp_load_slice_index kv (sint.Z i) line DFrac.discard x Hi.1) $$ [Hkv] as -
          · iframe Hkv; ipureintro; exact hx
          try wp_auto
          wp_if_destruct
          · -- the first colon, at `i`
            try wp_auto
            wp_for_post
            have hj := mh_colon_idx hlo.2.1 hw (sint.nat i) hx Hi.2.2
            have hi0 : ¬ sint.Z i < sint.Z (W64 0) := by word
            rw [decide_eq_false hi0]
            cleanup_bool_decide
            try wp_auto
            ihave #HPk2 := wp_Peek b ri S E _ $$ Hrd HSb
            wp_apply HPk2 $$ Hb as %s %err (⟨%Herr, %c, %q, %e, Hs, Hback⟩ | ⟨%Herr, #HE, Hb⟩)
            · subst Herr
              ihave Hnl : (s ↦* [c] -∗ ⌜c ≠ W8 32 ∧ c ≠ W8 9⌝ ∗ EtcdGrove.bufio.ownReader b ri S E
                  (r ++ mhPre hb n ++ mhBody hb[n] ++ [W8 10])) $$ [Hback]
              · iintro Hs
                ihave Hbb := Hback $$ Hs
                icases EtcdGrove.bufio.ownReaderBuf_open b ri S E _ (c :: q) e $$ Hbb with ⟨HS, Hcl⟩
                ihave %hc := HpkW $$ %(n + 1) %c %q %hnlt [HS]
                · rw [mh_pre_succ hb n hnlt]; simp only [List.append_assoc]; iexact HS
                ihave Hbb := Hcl $$ HS
                isplitl []
                · ipureintro; exact hc
                iapply (EtcdGrove.bufio.ownReader_buf b ri S E _).2
                iexists (c :: q), e
                iexact Hbb
              mh_peek_check
              mh_after
                have hmh' : sint.Z (mh - W64 1) = sint.Z maxH - ↑(n + 1) := by
                  have : sint.Z (mh - W64 1) = sint.Z mh - 1 := by word
                  rw [this, hmh]; push_cast; omega
                rw [← hwd, mh_val_whole hlo, List.nil_append]
                iframe
                iexists (mh - W64 1)
                iframe
                ileft
                iexists (n + 1)
                isplitr
                · ipureintro; exact ⟨by omega, hmh'⟩
                rw [mh_take_succ hb n hnlt, mh_pre_succ hb n hnlt]
                isplitl [Hms Hels Hs']
                · iapply (mh_hdrOwn_snoc mp (List.take n hb) ms hb[n].fst hb[n].snd s' Hdom hKf)
                  iframe
                · simp only [List.append_assoc]; iexact Hb
            · obtain ⟨ie, rfl⟩ : ∃ ie, err = GoInterface.ok ie := by
                cases err with
                | nil => exact absurd rfl Herr
                | ok ie => exact ⟨ie, rfl⟩
              try wp_auto
              mh_after
                have hmh' : sint.Z (mh - W64 1) = sint.Z maxH - ↑(n + 1) := by
                  have : sint.Z (mh - W64 1) = sint.Z mh - 1 := by word
                  rw [this, hmh]; push_cast; omega
                rw [← hwd, mh_val_whole hlo, List.nil_append]
                iframe
                iexists (mh - W64 1)
                iframe
                ileft
                iexists (n + 1)
                isplitr
                · ipureintro; exact ⟨by omega, hmh'⟩
                rw [mh_take_succ hb n hnlt, mh_pre_succ hb n hnlt]
                isplitl [Hms Hels Hs']
                · iapply (mh_hdrOwn_snoc mp (List.take n hb) ms hb[n].fst hb[n].snd s' Hdom hKf)
                  iframe
                · simp only [List.append_assoc]; iexact Hb
          · wp_for_post
            iframe
            iexists _
            iframe
            ipureintro
            have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
            rw [hn]
            refine ⟨by word, by omega, fun j y hj hy => ?_⟩
            rcases Nat.lt_or_ge j (sint.nat i) with h | h
            · exact Hi.2.2 j y h hy
            · have : j = sint.nat i := by omega
              subst this; rw [hx] at hy; cases hy; assumption
        · simp only [hlt, decide_false, false_neq_true, _root_.decide_true, Bool.false_eq_true,
            ↓reduceIte]
          exfalso
          have hi : sint.nat i = line.length := by have := Hkl.1; word
          have hk := Hi.2.2 hb[n].fst.length (W8 58) (by rw [hi, hw]; simp) (by rw [hw]; simp)
          exact hk rfl
      · have hn' : n = hb.length := by omega
        subst hn'
        rw [mh_tl_len] at hq
        have hl : l = eol :=
          mh_prefix_nl Hl (mh_eol_no_nl heol) ((List.prefix_append _ _).trans (by simpa using hq))
        subst hl
        rw [mh_dropCR_eol heol]
        try wp_auto
        wp_apply (wp_string_len (t := go.string) []) as %-
        try wp_auto
        wp_for_post
        iapply HΦ
        iright
        isplitr
        · ipureintro; rfl
        simp only [mh_take_len]
        iframe Hown
        rw [← mh_pre_len]
        simp only [List.append_assoc]
        iexact Hb
    · -- a line cut by an error, or the error
      rcases l with _ | ⟨a, l'⟩
      · obtain ⟨rfl, rfl⟩ : err = e ∧ line = [] := by
          rcases Hc with ⟨h, _⟩ | ⟨_, h1, h2⟩
          · exact absurd rfl h
          · exact ⟨h1, h2⟩
        mh_ret_err
      obtain ⟨rfl, rfl⟩ : err = GoInterface.nil ∧ line = a :: l' := by
        rcases Hc with ⟨_, h1, h2⟩ | ⟨h, _⟩
        · exact ⟨h1, h2⟩
        · cases h
      iunfold EtcdGrove.io.errAt at HE
      icases HE with ⟨(%Hen | #HEe), -⟩
      · exact absurd Hen He
      ihave ⟨%q', HS, Hcl⟩ := EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb
      ihave %hq := Htl $$ %n %((a :: l') ++ q') [HS]
      · simp only [List.append_assoc]; iexact HS
      ihave Hb := Hcl $$ HS
      have hlq : a :: l' <+: mhTl hb eol rest n := (List.prefix_append _ _).trans hq
      obtain ⟨line, hL⟩ : ∃ line, a :: l' = line := ⟨_, rfl⟩
      rw [hL]
      have hne : line ≠ [] := by rw [← hL]; simp
      have hcol : (∀ x ∈ line, x ≠ W8 58) ∨
          ∃ (hnlt : n < hb.length) (w : List w8), line = hb[n].fst ++ W8 58 :: w := by
        rcases Nat.lt_or_ge n hb.length with hnlt | hge
        · rw [mh_tl_lt hb eol rest n hnlt] at hlq
          have hlb := mh_prefix_no_nl Hl (mh_body_no_nl (mh_line_ok hok hnlt)) hlq
          rcases mh_cut_cases (mh_line_ok hok hnlt) hlb with h | ⟨w, hw⟩
          · left; rw [← hL]; exact h
          · right; exact ⟨hnlt, w, by rw [← hL]; exact hw⟩
        · have hn' : n = hb.length := by omega
          subst hn'
          rw [mh_tl_len] at hlq
          left; rw [← hL]; exact mh_cut_eol heol (by simp) Hl hlq
      rw [hL] at Hl
      clear hq hlq
      try wp_auto
      wp_apply (wp_string_len (t := go.string) line) as %Hlen
      have hne' : W64 (line.length : Int) ≠ W64 0 := by
        intro h; apply hne; apply List.eq_nil_of_length_eq_zero; revert h; word
      rw [decide_eq_false hne']
      try wp_auto
      wp_apply (wp_string_to_bytes line) as %kv ⟨Hkv, -⟩
      imod ownSlice_persist _ _ _ $$ Hkv with #Hkv
      try wp_auto
      ihave HC : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ line.length ∧
            ∀ j x, j < sint.nat i → line[j]? = some x → x ≠ W8 58⌝ : IProp GF) $$ [i]
      · iexists W64 0
        iframe
        ipureintro
        refine ⟨by word, by word, fun j x hj => ?_⟩
        exfalso; revert hj; word
      ihave %Hkl := ownSlice_len $$ Hkv
      wp_for HC
      by_cases hlt : sint.Z i < sint.Z kv.len
      · simp only [hlt, _root_.decide_true, ↓reduceIte]
        have hi : sint.nat i < line.length := by have := Hkl.1; word
        obtain ⟨x, hx⟩ : ∃ x, line[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
        wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, hlt⟩)]
        wp_apply (wp_load_slice_index kv (sint.Z i) line DFrac.discard x Hi.1) $$ [Hkv] as -
        · iframe Hkv; ipureintro; exact hx
        try wp_auto
        wp_if_destruct
        · -- the first colon, at `i`
          try wp_auto
          wp_for_post
          rcases hcol with hno | ⟨hnlt, w, hw⟩
          · exact absurd rfl (hno _ (List.mem_of_getElem? hx))
          have hlo := mh_line_ok hok hnlt
          have hmh1 : 1 ≤ sint.Z mh := by omega
          have hj := mh_colon_idx hlo.2.1 hw (sint.nat i) hx Hi.2.2
          have hi0 : ¬ sint.Z i < sint.Z (W64 0) := by word
          rw [decide_eq_false hi0]
          cleanup_bool_decide
          try wp_auto
          ihave #HPk2 := wp_Peek b ri S E _ $$ Hrd HSb
          wp_apply HPk2 $$ Hb as %s %err (⟨%Herr, %c, %q, %e2, Hs, Hback⟩ | ⟨%Herr, #HE2, Hb⟩)
          · -- nothing follows the error
            ihave Hbb := Hback $$ Hs
            icases EtcdGrove.bufio.ownReaderBuf_open b ri S E _ (c :: q) e2 $$ Hbb with ⟨HS, -⟩
            ihave %h := Hfin $$ %_ %_ %_ HEe HS
            exfalso
            have h' := h (List.prefix_append _ _)
            have := congrArg List.length h'
            simp at this
          · obtain ⟨ie, rfl⟩ : ∃ ie, err = GoInterface.ok ie := by
              cases err with
              | nil => exact absurd rfl Herr
              | ok ie => exact ⟨ie, rfl⟩
            try wp_auto
            mh_after
              iframe
              iexists (mh - W64 1)
              iframe
              iright
              iexists _, _, _
              iframe HEe Hb Hms
        · wp_for_post
          iframe
          iexists _
          iframe
          ipureintro
          have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
          rw [hn]
          refine ⟨by word, by omega, fun j y hj hy => ?_⟩
          rcases Nat.lt_or_ge j (sint.nat i) with h | h
          · exact Hi.2.2 j y h hy
          · have : j = sint.nat i := by omega
            subst this; rw [hx] at hy; cases hy; assumption
      · simp only [hlt, decide_false, false_neq_true, _root_.decide_true, Bool.false_eq_true,
          ↓reduceIte]
        try wp_auto
        rcases hcol with hno | ⟨hnlt, w, hw⟩
        rotate_left
        · exfalso
          have hi : sint.nat i = line.length := by have := Hkl.1; word
          have hk := Hi.2.2 hb[n].fst.length (W8 58) (by rw [hi, hw]; simp) (by rw [hw]; simp)
          exact hk rfl
        -- no colon: a `ProtocolError`
        try rw [decide_eq_true (show sint.Z (W64 (-1)) < sint.Z (W64 0) by decide)]
        cleanup_bool_decide
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        try wp_auto
        wp_apply (wp_SprintfB (mhB kv line) DFrac.discard _ _ _ _) $$ [Hsl] as %msg -
        · isplitl [Hsl]
          · iexact Hsl
          iapply (mh_sprintfB_pre kv line _ (by decide))
          iexact Hkv
        try wp_auto
        wp_for_post
        iapply HΦ
        ileft
        mh_proto_post
  · ihave #HRL := wp_modelReadLine b ri S E r1 $$ Hrd HSb
    wp_apply HRL $$ Hb as %line %err ⟨%l, %Hl, (⟨⟨%Herr, %Hline⟩, Hb⟩ | ⟨%e, %He, #HE, Hb, %Hc⟩)⟩
    · icases EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb with ⟨%q', HS, -⟩
      ihave %h := Hfin $$ %r1 %_ %e1 HE1 HS
      exfalso
      have h' := h (by simp only [List.append_assoc]; exact List.prefix_append _ _)
      have := congrArg List.length h'
      simp at this
    rcases l with _ | ⟨a, l'⟩
    rotate_left
    · icases EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb with ⟨%q', HS, -⟩
      ihave %h := Hfin $$ %r1 %_ %e1 HE1 HS
      exfalso
      have h' := h (by simp only [List.append_assoc]; exact List.prefix_append _ _)
      have := congrArg List.length h'
      simp at this
    obtain ⟨rfl, rfl⟩ : err = e ∧ line = [] := by
      rcases Hc with ⟨h, _⟩ | ⟨_, h1, h2⟩
      · exact absurd rfl h
      · exact ⟨h1, h2⟩
    mh_ret_err))

set_option maxHeartbeats 8000000 in
theorem modelReadMIMEHeader.wp_proof
    (wp_Peek : EtcdGrove.bufio.Reader.Peek.spec (GF := GF) (hG := hG))
    (wp_modelReadLine : modelReadLine.spec (GF := GF) (hG := hG))
    (wp_Canon : net.textproto.CanonicalMIMEHeaderKey.spec (GF := GF) (hG := hG))
    (wp_VHFN : vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldName.spec (GF := GF) (hG := hG))
    (wp_VHFV : vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldValue.spec (GF := GF) (hG := hG))
    (wp_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_SprintfB : SprintfBytes.law (GF := GF) (hG := hG)) :
    modelReadMIMEHeader.spec (GF := GF) (hG := hG) := by
  intro b ri S E r hb eol rest maxH hok heol hmax
  iintro #Henv #Hrd #HSb #HSp #Hfin
  ihave #Htab := httpEnv_tokenTable $$ Henv
  ihave #Henv' := Henv
  iunfold httpEnv at Henv'
  icases Henv' with ⟨-, -, #Hfmt, -⟩
  wp_start as Hb
  wp_auto
  rw [go.make1_underlying, go.is_underlying (t := net.textproto.MIMEHeader.ty)]
  wp_apply (wp_map_make1 (K := GoString) (V := GoSlice)) as %mp Hmp
  try wp_auto
  ihave #HPk := wp_Peek b ri S E r $$ Hrd HSb
  -- what the stream holds after `n` whole lines
  ihave #Htl : (□ ∀ (n : Nat) (q : List w8), S (r ++ mhPre hb n ++ q) -∗ ⌜q <+: mhTl hb eol rest n⌝ :
      IProp GF) $$ []
  · imodintro
    iintro %n %q HS
    ihave %h := HSp $$ HS
    ipureintro
    have h' := h (by rw [List.append_assoc]; exact List.prefix_append _ _)
    rw [List.append_assoc r (hdrWire hb eol), mh_split hb eol rest n] at h'
    exact mh_law_tl h'
  -- a `Peek(1)` after `n` whole lines sees no space or tab
  ihave #HpkW : (□ ∀ (n : Nat) (c : w8) (q : List w8), ⌜n ≤ hb.length⌝ -∗
      S (r ++ mhPre hb n ++ c :: q) -∗ ⌜c ≠ W8 32 ∧ c ≠ W8 9⌝ : IProp GF) $$ []
  · imodintro
    iintro %n %c %q %hn HS
    ihave %h := Htl $$ %n %(c :: q) HS
    ipureintro
    obtain ⟨T', hT⟩ := mh_head_of_prefix h
    exact mh_tl_head hok heol hn hT
  ihave #HPk := wp_Peek b ri S E r $$ Hrd HSb
  wp_apply HPk $$ Hb as %s %err (⟨%Herr, %c, %q, %e, Hs, Hback⟩ | ⟨%Herr, #HE, Hb⟩)
  · subst Herr
    ihave Hnl : (s ↦* [c] -∗ ⌜c ≠ W8 32 ∧ c ≠ W8 9⌝ ∗ EtcdGrove.bufio.ownReader b ri S E r) $$ [Hback]
    · iintro Hs
      ihave Hbb := Hback $$ Hs
      icases EtcdGrove.bufio.ownReaderBuf_open b ri S E r (c :: q) e $$ Hbb with ⟨HS, Hcl⟩
      ihave %hc := HpkW $$ %0 %c %q %(Nat.zero_le _) [HS]
      · rw [mh_pre_zero, List.append_nil]; iexact HS
      ihave Hbb := Hcl $$ HS
      isplitl []
      · ipureintro; exact hc
      iapply (EtcdGrove.bufio.ownReader_buf b ri S E r).2
      iexists (c :: q), e
      iexact Hbb
    mh_peek_check
    iclear HPk
    mh_loop
  · obtain ⟨i, rfl⟩ : ∃ i, err = GoInterface.ok i := by
      cases err with
      | nil => exact absurd rfl Herr
      | ok i => exact ⟨i, rfl⟩
    try wp_auto
    iclear HPk HE
    mh_loop

end proof

end net.http
end Perennial
