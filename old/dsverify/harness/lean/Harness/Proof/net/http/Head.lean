/-
The request head of the lab's model of `net/http`: `readHead` and `parseRequestLine` on a
connection whose dialers write `httpReqP p Pb` (`Proto.lean`), for a well-formed path `p`
(`wfPath`): `readHead` reads exactly `connectHead p`, and `parseRequestLine` of it gives
`("CONNECT", p, true)`.
-/
module

public import Harness.Proof.net.http.Mux
public import Harness.Proof.net.TCPConn__Read

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.http

/-! ## Well-formed paths and their heads -/

/-- `connectHead`'s request-line prefix. -/
abbrev headPre : GoString := go!"CONNECT "
/-- `connectHead`'s suffix: the protocol and the blank line. -/
abbrev headSuf : GoString := go!" HTTP/1.0\n\n"

/-- A path a client may request with `connectHead`: nonempty, with no space, `'\n'` or `'\r'`,
and short enough that its head fits `maxHead` (4096 bytes). -/
def wfPath (p : GoString) : Prop :=
  p ≠ [] ∧ (∀ b ∈ p, b ≠ W8 32 ∧ b ≠ W8 10 ∧ b ≠ W8 13) ∧ (connectHead p).length ≤ 4096

theorem connectHead_eq (p : GoString) : connectHead p = headPre ++ p ++ headSuf := rfl

theorem headPre_length : headPre.length = 8 := rfl
theorem headSuf_length : headSuf.length = 11 := rfl

theorem connectHead_length (p : GoString) : (connectHead p).length = p.length + 19 := by
  rw [connectHead_eq, List.length_append, List.length_append, headPre_length, headSuf_length]
  omega

theorem headPre_get (i : Nat) (h : i < 8) (b : w8) (hb : headPre[i]? = some b) :
    b ≠ W8 10 ∧ b ≠ W8 13 := by
  revert b; revert i; decide

theorem headSuf_get (j : Nat) (h : j < 11) (b : w8) (hb : headSuf[j]? = some b) :
    (b = W8 10 → 9 ≤ j) := by
  revert b; revert j; decide

/-- A `'\n'` of `connectHead p` is one of its last two bytes. -/
theorem connectHead_nl {p : GoString} (hp : wfPath p) (i : Nat)
    (hi : (connectHead p)[i]? = some (W8 10)) : (connectHead p).length ≤ i + 2 := by
  rw [connectHead_length]
  rw [connectHead_eq] at hi
  have hlt : i < (headPre ++ p ++ headSuf).length := by
    rcases Nat.lt_or_ge i (headPre ++ p ++ headSuf).length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hi; cases hi
  simp only [List.length_append, headPre_length, headSuf_length] at hlt
  by_cases h1 : i < 8
  · rw [List.append_assoc, List.getElem?_append_left (by rw [headPre_length]; omega)] at hi
    exact absurd rfl (headPre_get i h1 _ hi).1
  by_cases h2 : i < 8 + p.length
  · rw [List.append_assoc, List.getElem?_append_right (by rw [headPre_length]; omega),
      List.getElem?_append_left (by rw [headPre_length]; omega)] at hi
    exact absurd rfl (hp.2.1 _ (List.mem_of_getElem? hi)).2.1
  · rw [List.getElem?_append_right (by simp only [List.length_append, headPre_length]; omega)]
      at hi
    have := headSuf_get _ (by simp only [List.length_append, headPre_length]; omega) _ hi rfl
    simp only [List.length_append, headPre_length] at this
    omega

theorem connectHead_get_end {p : GoString} (k : Nat) (hk : k < 3) :
    (connectHead p)[(connectHead p).length - 3 + k]? =
      some ([W8 48, W8 10, W8 10][k]'(by simp; omega)) := by
  rw [connectHead_length, connectHead_eq,
    List.getElem?_append_right (by simp only [List.length_append, headPre_length]; omega)]
  simp only [List.length_append, headPre_length]
  rw [show p.length + 19 - 3 + k - (8 + p.length) = 8 + k by omega]
  rcases k with _ | _ | _ | k
  · rfl
  · rfl
  · rfl
  · omega

theorem headPre_sp (i : Nat) (h : i < 8) : headPre[i]? = some (W8 32) ↔ i = 7 := by
  revert i; decide

theorem headSuf_sp (j : Nat) (h : j < 9) : headSuf[j]? = some (W8 32) ↔ j = 0 := by
  revert j; decide

/-- The spaces of `connectHead p`'s request line are at `7` and `8 + |p|`. -/
theorem connectHead_sp {p : GoString} (hp : wfPath p) (i : Nat)
    (hi : i < (connectHead p).length - 2) (b : w8) (hb : (connectHead p)[i]? = some b) :
    b = W8 32 ↔ (i = 7 ∨ i = 8 + p.length) := by
  rw [connectHead_length] at hi
  rw [connectHead_eq] at hb
  by_cases h1 : i < 8
  · rw [List.append_assoc, List.getElem?_append_left (by rw [headPre_length]; omega)] at hb
    have := headPre_sp i h1
    constructor
    · intro h; subst h; exact Or.inl (this.1 hb)
    · rintro (h | h)
      · rw [this.2 h] at hb; cases hb; rfl
      · omega
  by_cases h2 : i < 8 + p.length
  · rw [List.append_assoc, List.getElem?_append_right (by rw [headPre_length]; omega),
      List.getElem?_append_left (by rw [headPre_length]; omega)] at hb
    have := (hp.2.1 _ (List.mem_of_getElem? hb)).1
    constructor
    · intro h; exact absurd h this
    · rintro (h | h) <;> omega
  · rw [List.getElem?_append_right (by simp only [List.length_append, headPre_length]; omega)]
      at hb
    simp only [List.length_append, headPre_length] at hb
    have := headSuf_sp (i - (8 + p.length)) (by omega)
    constructor
    · intro h; subst h; have := this.1 hb; omega
    · rintro (h | h)
      · omega
      · rw [this.2 (by omega)] at hb; cases hb; rfl

/-- The invariant of `parseRequestLine`'s scan for spaces in a line of length `E` holding
`connectHead p`'s request line (`P = |p|`): the spaces before `i` found. -/
def spInv (E P i sp1 sp2 : Int) : Prop :=
  0 ≤ i ∧ i ≤ E ∧ ((7 < i ∧ sp1 = 7) ∨ (i ≤ 7 ∧ sp1 = -1)) ∧
    ((8 + P < i ∧ sp2 = 8 + P) ∨ (i ≤ 8 + P ∧ sp2 = -1))

theorem subslice_connect1 (p : GoString) :
    subslice 0 7 (subslice 0 (p.length + 17) (connectHead p)) = go!"CONNECT" := by
  rw [connectHead_eq]
  simp only [subslice, List.drop_zero, List.take_take, List.append_assoc]
  rw [List.take_append_of_le_length (by rw [headPre_length]; omega)]
  rfl

theorem subslice_connect2 (p : GoString) :
    subslice 8 (8 + p.length) (subslice 0 (p.length + 17) (connectHead p)) = p := by
  rw [connectHead_eq]
  simp only [subslice, List.drop_zero, List.take_take]
  rw [show min (8 + p.length) (p.length + 17) = (headPre ++ p).length by
    simp; omega]
  rw [List.take_left]
  rw [show 8 = headPre.length from rfl, List.drop_left]

theorem prefix_get {R H : List w8} (hR : R <+: H) {i : Nat} (hi : i < R.length) :
    R[i]? = H[i]? := by
  obtain ⟨t, rfl⟩ := hR
  rw [List.getElem?_append_left hi]

theorem prefix_ne_length {R H : List w8} (hR : R <+: H) (hne : R ≠ H) : R.length < H.length := by
  rcases Nat.lt_or_ge R.length H.length with h | h
  · exact h
  · exact absurd (hR.eq_of_length (Nat.le_antisymm hR.length_le h)) hne

theorem sint_nat_eq (x : w64) : sint.nat x = (sint.Z x).toNat := rfl

/-- A strict prefix of `connectHead p` of length at least 2 that ends in `'\n'` has its
`'0'` before it: no blank line ends it. -/
theorem prefix_noend {p : GoString} (hp : wfPath p) {R : List w8} (hR : R <+: connectHead p)
    (hne : R ≠ connectHead p) (h2 : 2 ≤ R.length) (v1 v2 : w8)
    (hv1 : R[R.length - 1]? = some v1) (hv2 : R[R.length - 2]? = some v2) (h10 : v1 = W8 10) :
    v2 ≠ W8 10 ∧ v2 ≠ W8 13 := by
  subst h10
  have hlt := prefix_ne_length hR hne
  rw [prefix_get hR (by omega)] at hv1 hv2
  have hL := connectHead_nl hp _ hv1
  have hk := connectHead_get_end (p := p) 0 (by omega)
  rw [show (connectHead p).length - 3 + 0 = R.length - 2 by omega, hv2] at hk
  cases hk
  simp only [List.getElem_cons_zero]
  exact ⟨by decide, by decide⟩

/-- The byte read after a strict prefix `R` of `connectHead p`, when the bytes read are a
prefix of a sequence the dialer's protocol allows, extends `R` within `connectHead p`. -/
theorem extend_prefix {H R ext : List w8} {b : w8} (hlt : R.length < H.length)
    (hx : R ++ [b] <+: ext) (he : ext <+: H ∨ H <+: ext) : R ++ [b] <+: H := by
  rcases he with he | he
  · exact hx.trans he
  · exact List.prefix_of_prefix_length_le hx he (by simp; omega)

/-! ## `readHead` -/

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.http.Assumptions]

set_option goose.wp.extras true

/-- A bounds-checked load of byte `j` of a slice. -/
theorem wp_load_byte_checked (s : GoSlice) (L : List w8) (dq : DFrac) (i : w64) (j : Nat) (v : w8)
    (hi : sint.Z i = j) (hv : L[j]? = some v) :
    {{ (s ↦*{dq} L : IProp GF) }}
      (App (Val (GoInstruction (GoLoad go.byte)))
        (if 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len then #(sliceIndexRef w8 (sint.Z i) s)
          else Panic "slice index out of bounds"))
    {{ RET #v; s ↦*{dq} L }} := by
  iintro %Φ Hs HΦ
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have hj : j < L.length := by
    rcases Nat.lt_or_ge j L.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hv; cases hv
  rw [ite_eq_left (by rw [sint_nat_eq] at Hl; omega)]
  iapply wp_load_slice_index s (sint.Z i) L dq v (by omega) $$ [Hs] HΦ
  iframe Hs
  ipureintro; rw [hi]; simpa using hv

/-- A bounds-checked load of byte `j` of a slice whose length is `n`. -/
theorem wp_load_byte_checked' (s : GoSlice) (n : w64) (hn : s.len = n) (L : List w8) (dq : DFrac)
    (i : w64) (j : Nat) (v : w8) (hi : sint.Z i = j) (hv : L[j]? = some v) :
    {{ (s ↦*{dq} L : IProp GF) }}
      (App (Val (GoInstruction (GoLoad go.byte)))
        (if 0 ≤ sint.Z i ∧ sint.Z i < sint.Z n then #(sliceIndexRef w8 (sint.Z i) s)
          else Panic "slice index out of bounds"))
    {{ RET #v; s ↦*{dq} L }} := by
  subst hn
  exact wp_load_byte_checked s L dq i j v hi hv

/-- What the acceptor reads, while it has read a strict prefix of `connectHead p`, stays a
prefix of `connectHead p`. -/
theorem recv_head_prefix (cid : w64) (p : GoString) (Pb : Proto GF) (R : List w8) (x : w8)
    (hlt : R.length < (connectHead p).length) :
    recvTok cid true (httpReqP p Pb) (R ++ [x]) ⊢
      recvTok cid true (httpReqP p Pb) (R ++ [x]) ∗ ⌜R ++ [x] <+: connectHead p⌝ := by
  iintro Hrecv
  ihave ⟨Hrecv, #Hp⟩ := recvTok_proto $$ Hrecv
  iframe Hrecv
  unfold protoPrefix httpReqP
  icases Hp with (%h0 | ⟨%ext, %hx, #Hext⟩)
  · simp at h0
  icases Hext with (%he | ⟨%rest, %he, -⟩)
  · ipureintro; exact extend_prefix hlt hx (Or.inl he)
  · ipureintro; exact extend_prefix hlt hx (Or.inr (by rw [he]; exact List.prefix_append _ _))

/-- `readHead(c)` on the acceptor's end `c` of `cid`, nothing read yet, whose dialers write
`httpReqP p Pb` with `p` well-formed: the head `connectHead p` (exactly: read up to its blank
line), or a read error. -/
abbrev readHead.spec : Prop :=
  ∀ (c : Loc) (cid : w64) (p : GoString) (Pb : Proto GF), wfPath p →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ net.ownTCPConn c cid true ∗
      recvTok cid true (httpReqP p Pb) [] }}
    (App (Val (@! net.http.readHead))
      (Val #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)))
  {{ (s : GoSlice) (err : GoInterface), RET (PairV #s #err);
      (⌜err = interface.nil⌝ ∗ s ↦* connectHead p ∗
        recvTok cid true (httpReqP p Pb) (connectHead p)) ∨
      (⌜err ≠ interface.nil⌝ ∗ ∃ R, recvTok cid true (httpReqP p Pb) R) }}

theorem readHead.wp_proof : readHead.spec (GF := GF) (hG := hG) := by
  intro c cid p Pb hp
  wp_start as ⟨#Hc, Hrecv⟩
  ihave #Hnet := net_init_of_http $$ Hpkg
  have hL := connectHead_length p
  have hL4 := hp.2.2
  wp_auto
  wp_apply (wp_slice_make3 (V := w8) (W64 0) (W64 64) (by constructor <;> decide))
    as %hs0 ⟨Hh, Hhcap, -⟩
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %bs0 ⟨Hb, -⟩
  · ipureintro; decide
  ihave HI : (∃ (hs : GoSlice) (R bs : List w8),
      "head" ∷ head_ptr ↦ hs ∗ "Hh" ∷ hs ↦* R ∗ "Hhcap" ∷ ownSliceCap w8 hs (DFrac.own 1) ∗
      "Hrecv" ∷ recvTok cid true (httpReqP p Pb) R ∗ "Hb" ∷ bs0 ↦* bs ∗
      "%HR" ∷ ⌜R <+: connectHead p ∧ R ≠ connectHead p ∧ bs.length = 1⌝ : IProp GF)
      $$ [head Hh Hhcap Hrecv Hb]
  · iexists hs0, [], _
    iframe
    ipureintro
    refine ⟨List.nil_prefix, ?_, rfl⟩
    intro h; have := congrArg List.length h; simp at this; omega
  wp_for HI
  ihave %Hhl := ownSlice_len _ _ _ $$ Hh
  have hRlt := prefix_ne_length HR.1 HR.2.1
  wp_if_destruct
  · exfalso
    have : sint.Z hs.len < 4096 := by rw [sint_nat_eq] at Hhl; omega
    word
  wp_apply net.TCPConn.Read.wp_proof c cid true bs0 bs (httpReqP p Pb) R
    $$ [$Hnet $Hc $Hrecv $Hb] as %n %err ⟨%data, %code, %Hd, Hb, Hrecv, -⟩
  rcases err with ei | _
  · obtain ⟨rfl, -, -, hdn, -⟩ := Hd
    rw [hdn (by simp)]
    wp_auto
    wp_for_post
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    iexists _; iexact Hrecv
  obtain ⟨-, hdl, -, -, hne⟩ := Hd
  obtain ⟨x, rfl⟩ : ∃ x, data = [x] := by
    have hne' := hne rfl (by intro h; rw [h] at HR; simp at HR)
    match data, hdl, hne' with
    | [x], _, _ => exact ⟨x, rfl⟩
    | [], _, h => exact absurd rfl h
    | _ :: _ :: _, h, _ => simp at h; omega
  rw [show List.drop [x].length bs = [] from List.drop_eq_nil_of_le (by simp; omega),
    List.append_nil]
  ihave ⟨Hrecv, %hR'⟩ := recv_head_prefix cid p Pb R x hRlt $$ Hrecv
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  wp_auto
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z bs0.len by
    rw [sint_nat_eq] at Hbl; simp at Hbl; word)]
  wp_apply wp_load_slice_index bs0 (sint.Z (W64 0)) [x] _ x (by decide) $$ [$Hb] as Hb
  · ipureintro; rfl
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [x]
  wp_auto
  rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.byte #x)] = 1 from rfl]
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Htmp, -⟩
  wp_auto
  wp_apply wp_slice_append (V := w8) hs R _ [x] (DFrac.own 1) $$ [$Hh $Hhcap $Htmp]
    as %hs' ⟨Hh, Hhcap, -⟩
  ihave %Hhl' := ownSlice_len _ _ _ $$ Hh
  have hN : sint.Z hs'.len = (R.length + 1 : Nat) := by
    rw [sint_nat_eq] at Hhl'; simp at Hhl'; omega
  have hNle : R.length + 1 ≤ 4096 := by have := hR'.length_le; simp at this; omega
  have hi1 : sint.Z (hs'.len - W64 1) = ((R.length + 1 : Nat) : Int) - 1 := by word
  have hi2 : 2 ≤ R.length + 1 →
      sint.Z (hs'.len - W64 2) = ((R.length + 1 : Nat) : Int) - 2 := by intro; word
  have hi3 : 3 ≤ R.length + 1 →
      sint.Z (hs'.len - W64 3) = ((R.length + 1 : Nat) : Int) - 3 := by intro; word
  by_cases heq : R ++ [x] = connectHead p
  · -- the head is complete: it ends in a blank line
    have hlen : R.length + 1 = (connectHead p).length := by
      rw [← heq]; simp
    have hv1 : (R ++ [x])[R.length]? = some (W8 10) := by
      have := connectHead_get_end (p := p) 2 (by omega)
      rw [show (connectHead p).length - 3 + 2 = R.length by omega] at this
      rw [heq, this]; rfl
    have hv2 : (R ++ [x])[R.length - 1]? = some (W8 10) := by
      have := connectHead_get_end (p := p) 1 (by omega)
      rw [show (connectHead p).length - 3 + 1 = R.length - 1 by omega] at this
      rw [heq, this]; rfl
    wp_if_destruct
    · wp_apply wp_load_byte_checked hs' (R ++ [x]) _ _ R.length (W8 10)
        (by rw [hi1]; omega) hv1 $$ Hh as Hh
      wp_apply wp_load_byte_checked hs' (R ++ [x]) _ _ (R.length - 1) (W8 10)
        (by rw [hi2 (by omega)]; omega) hv2 $$ Hh as Hh
      wp_for_post
      iapply HΦ
      ileft
      rw [heq]
      iframe
      ipureintro; rfl
    · exfalso
      have h2 : sint.Z (W64 2) = 2 := by word
      omega
  -- a strict prefix: no blank line ends it, read on
  have hlt' := prefix_ne_length hR' heq
  have hx1 : (R ++ [x])[R.length]? = some x := by simp
  have hcont : ∀ v2 : w8, (R ++ [x])[R.length - 1]? = some v2 → x = W8 10 → 1 ≤ R.length →
      v2 ≠ W8 10 ∧ v2 ≠ W8 13 := by
    intro v2 hv2 hx h1
    refine prefix_noend hp hR' heq (by simp only [List.length_append, List.length_singleton]; omega)
      x v2 (by simp) ?_ hx
    rw [show (R ++ [x]).length - 2 = R.length - 1 by simp]; exact hv2
  by_cases hx : x = W8 10
  · have hR1 : 1 ≤ R.length := by
      rcases R with _ | ⟨r, R⟩
      · exfalso
        have := hR'.length_le; simp at this
        have hk := connectHead_nl hp 0 (by rw [← prefix_get hR' (by simp)]; simp [hx])
        omega
      · simp
    obtain ⟨v2, hv2⟩ : ∃ v, (R ++ [x])[R.length - 1]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
    have hv2' := hcont v2 hv2 hx hR1
    wp_if_destruct
    all_goals try (
      wp_apply wp_load_byte_checked hs' (R ++ [x]) _ _ R.length x (by rw [hi1]; omega) hx1
        $$ Hh as Hh
      simp only [show decide (x = W8 10) = true from by simp [hx]]
      wp_auto
      wp_apply wp_load_byte_checked hs' (R ++ [x]) _ _ (R.length - 1) v2
        (by rw [hi2 (by omega)]; omega) hv2 $$ Hh as Hh
      wp_if_destruct <;> try exact absurd rfl hv2'.1)
    all_goals wp_if_destruct
    all_goals try (
      wp_apply wp_load_byte_checked hs' (R ++ [x]) _ _ R.length x (by rw [hi1]; omega) hx1
        $$ Hh as Hh
      simp only [show decide (x = W8 10) = true from by simp [hx]]
      wp_auto
      wp_apply wp_load_byte_checked hs' (R ++ [x]) _ _ (R.length - 1) v2
        (by rw [hi2 (by omega)]; omega) hv2 $$ Hh as Hh
      wp_if_destruct <;> try exact absurd rfl hv2'.2)
    all_goals (
      wp_for_post
      iframe
      iexists hs', R ++ [x], [x]
      iframe
      ipureintro
      exact ⟨hR', heq, rfl⟩)
  · wp_if_destruct
    all_goals try (
      wp_apply wp_load_byte_checked hs' (R ++ [x]) _ _ R.length x (by rw [hi1]; omega) hx1
        $$ Hh as Hh
      wp_if_destruct <;> try exact absurd rfl hx)
    all_goals wp_if_destruct
    all_goals try (
      wp_apply wp_load_byte_checked hs' (R ++ [x]) _ _ R.length x (by rw [hi1]; omega) hx1
        $$ Hh as Hh
      wp_if_destruct <;> try exact absurd rfl hx)
    all_goals (
      wp_for_post
      iframe
      iexists hs', R ++ [x], [x]
      iframe
      ipureintro
      exact ⟨hR', heq, rfl⟩)

/-- `parseRequestLine(head)` on `connectHead p` (`p` well-formed): `("CONNECT", p, true)`. -/
abbrev parseRequestLine.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (p : GoString), wfPath p →
  {{ (s ↦*{dq} connectHead p : IProp GF) }}
    (App (Val (@! net.http.parseRequestLine)) (Val #s))
  {{ RET (PairV (PairV #(go!"CONNECT") #p) #true); s ↦*{dq} connectHead p }}

theorem parseRequestLine.wp_proof : parseRequestLine.spec (GF := GF) (hG := hG) := by
  intro s dq p hp
  wp_start as Hs
  have hL := connectHead_length p
  have hL4 := hp.2.2
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  have hsl : sint.Z s.len = ((connectHead p).length : Int) := by rw [Hsl.1, sint_nat_eq]; omega
  have hE := connectHead_get_end (p := p) 1 (by omega)
  rw [show (connectHead p).length - 3 + 1 = (connectHead p).length - 2 by omega] at hE
  wp_auto
  ihave HI : (∃ (e : w64), "Hend" ∷ end_ptr ↦ e ∗
      "%He" ∷ ⌜0 ≤ sint.Z e ∧ sint.Z e ≤ ((connectHead p).length - 2 : Nat)⌝ : IProp GF) $$ [«end»]
  · iexists W64 0; iframe; ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · obtain ⟨v, hv⟩ : ∃ v, (connectHead p)[(sint.Z e).toNat]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply wp_load_byte_checked s (connectHead p) dq e (sint.Z e).toNat v (by omega) hv
      $$ Hs as Hs
    by_cases hv10 : v = W8 10
    · -- the line's end
      subst hv10
      have he : sint.Z e = ((connectHead p).length - 2 : Nat) := by
        have := connectHead_nl hp _ hv; omega
      simp only [_root_.decide_true, Bool.not_true]
      rw [ite_eq_right (by simp [intoVal_eq_iff]), ite_eq_left trivial]
      wp_auto
      have hE2 : 2 ≤ (connectHead p).length := by omega
      rw [ite_eq_left ⟨by word, by word, by omega⟩]
      ihave ⟨H0, Hline, Hrest⟩ := (ownSlice_slice (W64 0) e s dq (connectHead p)
        ⟨by word, by word, by omega⟩).1 $$ Hs
      have hLl : subslice (sint.nat (W64 0)) (sint.nat e) (connectHead p) =
          (connectHead p).take ((connectHead p).length - 2) := by
        simp only [subslice, sint_nat_eq, he]; simp
      have hlnlen : sint.Z (slice.slice s w8 (W64 0) e).len =
          ((connectHead p).length - 2 : Nat) := by
        simp only [slice.slice]; word
      have hLget : ∀ i, i < (connectHead p).length - 2 →
          (subslice (sint.nat (W64 0)) (sint.nat e) (connectHead p))[i]? = (connectHead p)[i]? := by
        intro i hi; rw [hLl, List.getElem?_take_of_lt hi]
      have h48 := connectHead_get_end (p := p) 0 (by omega)
      rw [show (connectHead p).length - 3 + 0 = (connectHead p).length - 2 - 1 by omega] at h48
      wp_auto
      wp_if_destruct
      · wp_apply wp_load_byte_checked' (slice.slice s w8 (W64 0) e) (e - W64 0) rfl _ dq
          (e - W64 0 - W64 1) ((connectHead p).length - 2 - 1) (W8 48)
          (by have : sint.Z e ≥ 17 := by omega
              rw [show ((connectHead p).length - 2 - 1 : Nat) = ((connectHead p).length - 2 : Nat) - (1 : Int) by omega, ← he]
              word)
          (by rw [hLget _ (by omega), h48]; rfl) $$ Hline as Hline
        have hP := hp.1
        have hP1 : 1 ≤ p.length := by
          rcases p with _ | ⟨_, _⟩
          · exact absurd rfl hP
          · simp
        ihave HI : (∃ (i sp1 sp2 : w64), "Hi" ∷ i_ptr ↦ i ∗ "Hsp1" ∷ sp1_ptr ↦ sp1 ∗
            "Hsp2" ∷ sp2_ptr ↦ sp2 ∗
            "%Hinv" ∷ ⌜spInv ((connectHead p).length - 2 : Nat) p.length (sint.Z i) (sint.Z sp1)
              (sint.Z sp2)⌝ : IProp GF) $$ [i sp1 sp2]
        · iexists _, _, _
          iframe
          ipureintro
          unfold spInv
          have h0 : sint.Z (W64 0) = 0 := by word
          have hm : sint.Z (W64 (-1)) = -1 := by word
          omega
        wp_for HI
        obtain ⟨Hi0, HiE, Hs1, Hs2⟩ := Hinv
        have hlen' : sint.Z (e - W64 0) = ((connectHead p).length - 2 : Nat) := by
          clear Hs1 Hs2; rw [← he]; word
        split
        · rename_i hlt
          have hlt' : sint.Z i < ((connectHead p).length - 2 : Nat) := by
            rw [← hlen']; simpa using hlt
          obtain ⟨v, hv⟩ : ∃ v, (connectHead p)[(sint.Z i).toNat]? = some v :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have hsp := connectHead_sp hp (sint.Z i).toNat (by omega) v hv
          wp_auto
          wp_apply wp_load_byte_checked' (slice.slice s w8 (W64 0) e) (e - W64 0) rfl _ dq
            i (sint.Z i).toNat v (by omega)
            (by rw [subslice, List.drop_zero, List.getElem?_take_of_lt
                  (by rw [sint_nat_eq, he]; simp; omega)]; exact hv) $$ Hline
            as Hline
          have hi1 : sint.Z (i + W64 1) = sint.Z i + 1 := by clear Hs1 Hs2; word
          have h0 : sint.Z (W64 0) = 0 := by word
          wp_if_destruct
          · have hi78 := hsp.1 rfl
            wp_if_destruct
            · -- the first space
              have hi7 : sint.Z i = 7 := by omega
              wp_for_post
              iframe
              iexists i + W64 1, i, sp2
              iframe
              ipureintro
              unfold spInv
              omega
            · -- the second space
              have hiP : sint.Z i = 8 + (p.length : Int) := by omega
              wp_if_destruct
              · wp_for_post
                iframe
                iexists i + W64 1, sp1, i
                iframe
                ipureintro
                unfold spInv
                omega
              · exfalso; omega
          · -- not a space
            have hn7 : sint.Z i ≠ 7 := by
              intro h; exact Hif (hsp.2 (Or.inl (by omega)))
            have hnP : sint.Z i ≠ 8 + (p.length : Int) := by
              intro h; exact Hif (hsp.2 (Or.inr (by omega)))
            wp_for_post
            iframe
            iexists i + W64 1, sp1, sp2
            iframe
            ipureintro
            unfold spInv
            omega
        · rename_i hlt
          have hiE : sint.Z i = ((connectHead p).length - 2 : Nat) := by
            have : ¬ sint.Z i < sint.Z (e - W64 0) := by simpa using hlt
            omega
          have hsp1 : sint.Z sp1 = 7 := by omega
          have hsp2 : sint.Z sp2 = 8 + (p.length : Int) := by omega
          have h0 : sint.Z (W64 0) = 0 := by word
          have hsp11 : sint.Z (sp1 + W64 1) = 8 := by clear Hs1 Hs2; word
          wp_auto
          wp_if_destruct
          · exfalso; omega
          wp_if_destruct
          · exfalso; omega
          wp_if_destruct
          · exfalso
            have : sint.Z (e - W64 0 - W64 1) = ((connectHead p).length - 2 : Nat) - 1 := by
              clear Hs1 Hs2; rw [← hlen']; word
            omega
          have hcap : sint.Z (s.cap - W64 0) = sint.Z s.cap := by clear Hs1 Hs2; word
          rw [ite_eq_left ⟨by omega, by omega, by omega⟩]
          have hlnl : sint.Z (slice.slice s w8 (W64 0) e).len = ((connectHead p).length - 2 : Nat) := by
            simp only [slice.slice]; exact hlen'
          have hz : sint.nat (W64 0) = 0 := rfl
          rw [hz]
          have hsp1' := ownSlice_slice (GF := GF) (W64 0) sp1 (slice.slice s w8 (W64 0) e) dq
            (subslice 0 (sint.nat e) (connectHead p)) ⟨by omega, by omega, by omega⟩
          rw [hz] at hsp1'
          ihave ⟨Ha, Hb, Hc⟩ := hsp1'.1 $$ Hline
          wp_apply wp_bytes_to_string $$ Hb as Hb
          ihave Hline := hsp1'.2 $$ [Ha Hb Hc]
          · iframe
          have hsp2' := ownSlice_slice (GF := GF) (sp1 + W64 1) sp2 (slice.slice s w8 (W64 0) e) dq
            (subslice 0 (sint.nat e) (connectHead p)) ⟨by omega, by omega, by omega⟩
          rw [ite_eq_left ⟨by omega, by omega, by omega⟩]
          ihave ⟨Ha, Hb, Hc⟩ := hsp2'.1 $$ Hline
          wp_apply wp_bytes_to_string $$ Hb as Hb
          ihave Hline := hsp2'.2 $$ [Ha Hb Hc]
          · iframe
          have hs0' := ownSlice_slice (GF := GF) (W64 0) e s dq (connectHead p)
            ⟨by word, by word, by omega⟩
          rw [hz] at hs0'
          ihave Hs := hs0'.2 $$ [H0 Hline Hrest]
          · iframe
          have n1 : sint.nat sp1 = 7 := by rw [sint_nat_eq]; omega
          have n2 : sint.nat (sp1 + W64 1) = 8 := by rw [sint_nat_eq]; omega
          have n3 : sint.nat sp2 = 8 + p.length := by rw [sint_nat_eq]; omega
          have n4 : sint.nat e = p.length + 17 := by rw [sint_nat_eq]; omega
          rw [n1, n2, n3, n4, subslice_connect1, subslice_connect2]
          iapply HΦ
          iexact Hs
      · exfalso; word
    · simp only [show decide (v = W8 10) = false from decide_eq_false hv10, Bool.not_false,
        _root_.decide_true, ite_true]
      wp_auto
      wp_for_post
      iframe
      iexists e + W64 1
      iframe
      ipureintro
      have hne : (sint.Z e).toNat ≠ (connectHead p).length - 2 := by
        intro h; rw [h, hE] at hv; cases hv; exact hv10 rfl
      constructor <;> word
  · exfalso; omega

end proofs

end net.http

end Perennial
