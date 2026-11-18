/-
The proofs of the framing helpers' specs (`WireSpec.lean`): `readFull`, `readFrame`,
`writeFrame`, `encodeMsg`, `decodeMsg` (`wire.go`) and `lastDot` (`server.go`).
-/
module

public import Harness.Proof.net.rpc.WireSpec
public import Perennial.Proof.encoding.binary.Base
public import Perennial.Golang.Theory.Unsafe
public import Harness.NetLib

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.rpc

/-! ## `lastDotIdx` -/

theorem find_range_reverse_none (p : Nat → Bool) (n : Nat) (h : ∀ j < n, p j = false) :
    (List.range n).reverse.find? p = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.find?_cons, h n (by omega)]
    exact ih (fun j hj => h j (by omega))

theorem find_range_reverse_some (p : Nat → Bool) (n k : Nat) (hk : k < n) (hp : p k = true)
    (h : ∀ j, k < j → j < n → p j = false) :
    (List.range n).reverse.find? p = some k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.find?_cons]
    by_cases hkn : k = n
    · subst hkn; simp [hp]
    · rw [h n (by omega) (by omega)]
      exact ih (by omega) (fun j h1 h2 => h j h1 (by omega))

theorem lastDotIdx_none (s : GoString) (h : ∀ j < s.length, s[j]? ≠ some (W8 46)) :
    lastDotIdx s = none := by
  unfold lastDotIdx
  exact find_range_reverse_none _ _ (fun j hj => by simpa using h j hj)

theorem lastDotIdx_some (s : GoString) (k : Nat) (hk : k < s.length) (hd : s[k]? = some (W8 46))
    (h : ∀ j, k < j → j < s.length → s[j]? ≠ some (W8 46)) :
    lastDotIdx s = some k := by
  unfold lastDotIdx
  exact find_range_reverse_some _ _ _ hk (by simpa using hd)
    (fun j h1 h2 => by simpa using h j h1 h2)

section bounds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The bytes of a non-empty byte points-to lie in `(0, maxAddr]`. -/
theorem bytesPointsto_bound (l : Loc) (dq : DFrac) (bs : List w8) (h : bs ≠ []) :
    bytesPointsto (GF := GF) l dq bs ⊢ ⌜0 < l.addr ∧ l.addr + bs.length ≤ maxAddr⌝ := by
  induction bs generalizing l with
  | nil => exact absurd rfl h
  | cons b bs ih =>
    unfold bytesPointsto
    iintro ⟨Hb, Hbs⟩
    icases heapPointsto_pos l dq _ $$ Hb with %H1
    icases heapPointsto_lt_maxAddr l dq _ $$ Hb with %H2
    cases bs with
    | nil => ipureintro; simp; omega
    | cons b' bs' =>
      icases ih (l +ₗ 1) (by simp) $$ Hbs with %H3
      ipureintro
      simp only [Loc.add, List.length_cons] at H3 ⊢
      omega

/-- A byte slice is shorter than the address space (`maxAddr = 2 ^ 47`). -/
theorem ownSlice_bytes_len (s : GoSlice) (dq : DFrac) (vs : List w8) :
    (s ↦*{dq} vs : IProp GF) ⊢ ⌜vs.length ≤ 2 ^ 47⌝ := by
  by_cases hne : vs = []
  · subst hne; iintro _; ipureintro; simp
  iintro H
  icases ownSlice_ptr_pos s vs dq hne $$ H with %Hl
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) s vs dq Hl $$ H
    with ⟨Hb, -⟩
  have hne' : vs.flatMap encode ≠ [] := by
    cases vs with
    | nil => exact absurd rfl hne
    | cons v vs => simp [List.flatMap_cons]
  icases bytesPointsto_bound _ _ _ hne' $$ Hb with %Hbd
  ipureintro
  have hlen : (vs.flatMap (encode (V := w8))).length = vs.length := by
    simp
  rw [hlen] at Hbd
  simp only [maxAddr] at Hbd
  omega

/-- Split a slice holding `data ++ rest` at `len(data)`: its suffix `b[len(data):len(b)]` holds
`rest`, and gives back the whole slice with any `rest'` of `rest`'s length. -/
theorem ownSlice_drop_acc {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (b : GoSlice) (dq : DFrac) (data rest : List V) :
    (b ↦*{dq} (data ++ rest) : IProp GF) ⊢
      ⌜sint.Z (W64 data.length) = data.length ∧ sint.Z b.len = data.length + rest.length⌝ ∗
      slice.slice b V (W64 data.length) b.len ↦*{dq} rest ∗
      (∀ rest' : List V, ⌜rest'.length = rest.length⌝ -∗
        slice.slice b V (W64 data.length) b.len ↦*{dq} rest' -∗ b ↦*{dq} (data ++ rest')) := by
  iintro Hb
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  have h63 : sint.Z b.len < 2 ^ 63 := by word
  have hlen : data.length + rest.length = (sint.Z b.len).toNat := by
    rw [← List.length_append]; exact Hl.1
  have hZ : sint.Z (W64 data.length) = data.length := sint_Z_W64_length (by omega)
  have hN : sint.nat (W64 data.length) = data.length := by
    show (sint.Z (W64 data.length)).toNat = _; rw [hZ]; rfl
  have h0 : sint.Z (W64 0) = 0 := rfl
  ihave Hsplit := (ownSlice_split_all (W64 data.length) b dq _
    ⟨by rw [hZ]; omega, by rw [hZ]; omega⟩).1 $$ Hb
  rw [hN, List.take_left' rfl, List.drop_left' rfl]
  icases Hsplit with ⟨Hpre, Hrest⟩
  isplitr
  · ipureintro; exact ⟨hZ, by omega⟩
  iframe Hrest
  iintro %rest' %Hr Hrest
  iapply ownSlice_trivial_slice_2
  iapply ownSlice_combine (W64 data.length) b dq data rest' (W64 0) b.len
    ⟨by rw [hN]; rfl, by rw [h0]; omega, by rw [h0, hZ]; omega, by rw [hZ]; omega⟩ $$ Hpre Hrest

/-- A sub-slice `p[lo:hi]` of a slice, and the way back. -/
theorem ownSlice_sub_acc {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (lo hi : w64) (p : GoSlice) (dq : DFrac) (vs : List V)
    (hb : 0 ≤ sint.Z lo ∧ sint.Z lo ≤ sint.Z hi ∧ sint.Z hi ≤ sint.Z p.len) :
    (p ↦*{dq} vs : IProp GF) ⊢
      slice.slice p V lo hi ↦*{dq} subslice (sint.nat lo) (sint.nat hi) vs ∗
      (slice.slice p V lo hi ↦*{dq} subslice (sint.nat lo) (sint.nat hi) vs -∗ p ↦*{dq} vs) := by
  iintro Hp
  icases (ownSlice_slice lo hi p dq vs hb).1 $$ Hp with ⟨H0, H1, H2⟩
  iframe H1
  iintro H1
  iapply (ownSlice_slice lo hi p dq vs hb).2
  iframe

end bounds

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions] [RpcKit]

set_option goose.wp.extras true

theorem readFull.wp_proof : readFull.spec (GF := GF) (hG := hG) := by
  intro cv cid side P R n
  wp_start as ⟨#Hc, Hrecv, %Hn⟩
  unfold connIface
  icases Hc with ⟨%c, %Hcv, #Hc⟩
  subst Hcv
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) n) as %bs0 ⟨Hb, -⟩
  · ipureintro; word
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  ihave HI : (∃ (off : w64) (data : List w8), "off" ∷ off_ptr ↦ off ∗
      "Hb" ∷ bs0 ↦* (data ++ List.replicate (uint.nat n - data.length) (zero_val w8)) ∗
      "Hrecv" ∷ recvTok cid side P (R ++ data) ∗
      "%Hoff" ∷ ⌜off = W64 data.length ∧ data.length ≤ uint.nat n⌝ : IProp GF) $$ [off Hb Hrecv]
  · iexists W64 0, []
    simp only [List.append_nil, List.nil_append, List.length_nil, Nat.sub_zero]
    have : sint.nat n = uint.nat n := by word
    rw [this]
    iframe
    ipureintro; constructor <;> first | rfl | omega
  wp_for HI
  wp_if_destruct
  · ihave %Hw := ownSlice_wf _ _ _ $$ Hb
    ihave ⟨%Hsz, Hsuf, Hback⟩ := ownSlice_drop_acc bs0 _ data _ $$ Hb
    rw [← Hoff.1]
    rw [ite_eq_left (by rw [Hoff.1]; omega)]
    wp_auto
    wp_apply net.TCPConn.Read.wp_proof c cid side _ _ P (R ++ data) $$ [$Hpkg $Hc $Hrecv $Hsuf]
      as %k %err ⟨%d, %code, %Hd, Hsuf, Hrecv, #Herr⟩
    obtain ⟨rfl, Hdl, Hnil, Herr, Hne⟩ := Hd
    rw [List.drop_replicate] at *
    simp only [List.length_replicate] at Hdl
    have hl : (d ++ List.replicate (uint.nat n - data.length - d.length) (zero_val w8)).length =
        (List.replicate (uint.nat n - data.length) (zero_val w8)).length := by simp; omega
    ihave Hb := Hback $$ %_ %hl Hsuf
    rw [List.append_assoc] at *
    rcases err with ei | _
    · icases connErr_errAny _ _ _ $$ [Hpkg Herr] with (%Hn | ⟨#Ha, %Hns⟩)
      · isplitl [Hpkg]; iexact Hpkg; iexact Herr
      · cases Hn
      have hd : d = [] := Herr (by simp)
      subst hd
      wp_auto
      wp_for_post
      iapply HΦ
      iexists data
      simp only [List.append_nil] at *
      iframe Hrecv
      iright
      iframe Ha
      ipureintro; exact ⟨by simp, Hns⟩
    · wp_auto
      wp_for_post
      iframe
      iexists W64 (data ++ d).length, data ++ d
      simp only [List.length_append, Nat.sub_sub, List.append_assoc]
      have hoff : off + W64 (d.length : Int) = W64 ((data.length + d.length : Nat) : Int) := by
        rw [Hoff.1]; push_cast; word
      rw [hoff]
      iframe
      ipureintro
      simp only [true_and]; omega
  · have hd : data.length = uint.nat n := by
      have h1 : uint.Z off = data.length := by rw [Hoff.1]; word
      have h2 : (uint.nat n : Int) = uint.Z n := by word
      have := Hoff.2
      omega
    rw [hd, Nat.sub_self, List.replicate_zero, List.append_nil]
    iapply HΦ
    iexists data
    iframe Hrecv
    ileft
    iframe Hb
    ipureintro; exact ⟨rfl, hd⟩

open encoding.binary in
theorem wp_putU64 (b : GoSlice) (vs : List w8) (x : w64) :
    {{ (b ↦* vs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (Val (@! net.rpc.putU64)) (Val #b)) (Val #x))
    {{ (r : GoSlice), RET #r; r ↦* (vs ++ u64Le x) ∗ ownSliceCap w8 r (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) (u64Le x)
  wp_auto
  isplitl []
  · ipureintro; rw [u64Le_8]; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_apply wp_slice_append (V := w8) b vs _ (u64Le x) (DFrac.own 1) $$ [$Hb $Hcap $Hsl]
    as %r ⟨Hr, Hrcap, -⟩
  iapply HΦ
  iframe

open encoding.binary in
theorem wp_getU64 (b : GoSlice) (dq : DFrac) (bs : List w8) (hl : bs.length = 8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! net.rpc.getU64)) (Val #b))
    {{ RET #(leToU64 bs); b ↦*{dq} bs }} := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩ :
      ∃ w0 w1 w2 w3 w4 w5 w6 w7, bs = [w0, w1, w2, w3, w4, w5, w6, w7] := by
    match bs, hl with
    | [w0, w1, w2, w3, w4, w5, w6, w7], _ => exact ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w0 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w1 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w2 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w3 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w4 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w5 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w6 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w7 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  rw [leToU64_8]
  iapply HΦ $$ Hb

theorem writeFrame.wp_proof : writeFrame.spec (GF := GF) (hG := hG) := by
  intro cv cid side P W p dq pl
  wp_start as ⟨#Hc, Hsend, #HP, Hp⟩
  unfold connIface
  icases Hc with ⟨%c, %Hcv, #Hc⟩
  subst Hcv
  ihave %Hpl := ownSlice_len _ _ _ $$ Hp
  ihave %Hpb := ownSlice_bytes_len _ _ _ $$ Hp
  have hlen : p.len = W64 (pl.length : Int) := by
    have := Hpl.2; rw [Hpl.1]; word
  wp_auto
  wp_apply (wp_slice_make3 (V := w8) (W64 0) (W64 8 + p.len) (by rw [hlen]; constructor <;> word))
    as %b0 ⟨Hb0, Hb0cap, -⟩
  rw [List.replicate_zero]
  wp_apply wp_putU64 b0 [] p.len $$ [$Hb0 $Hb0cap] as %b1 ⟨Hb1, Hb1cap⟩
  wp_apply wp_slice_append (V := w8) b1 _ p pl dq $$ [$Hb1 $Hb1cap $Hp] as %b2 ⟨Hb2, -, Hp⟩
  rw [List.nil_append, hlen, show u64Le (W64 (pl.length : Int)) ++ pl = frameOf pl from rfl]
  wp_apply net.TCPConn.Write.wp_proof c cid side b2 (frameOf pl) (DFrac.own 1) P W
    $$ [$Hpkg $Hc $Hsend $HP $Hb2] as %nw %err ⟨%k, %code, %Hk, -, Hsend, #Herr⟩
  icases connErr_errAny _ _ _ $$ [Hpkg Herr] with (%Hn | ⟨#Ha, %Hns⟩)
  · isplitl [Hpkg]; iexact Hpkg; iexact Herr
  · iapply HΦ
    iexists k
    iframe Hsend Hp
    isplitr
    · ipureintro; subst Hn; exact ⟨Hk.2.1, Hk.2.2.2, notServerErr_nil⟩
    ileft; ipureintro; exact Hn
  · iapply HΦ
    iexists k
    iframe Hsend Hp
    isplitr
    · ipureintro; exact ⟨Hk.2.1, Hk.2.2.2, Hns⟩
    iright; iexact Ha

theorem readFrame.wp_proof : readFrame.spec (GF := GF) (hG := hG) := by
  intro cv cid side P R
  wp_start as ⟨#Hc, Hrecv⟩
  ihave #Hinit := net.rpc.isInit_access $$ Hpkg2
  icases Hinit with ⟨-, -, #HerrFrame, -⟩
  icases newVar_errMsg' _ _ $$ HerrFrame with ⟨%eF, #HeF, #HmF, %HnF⟩
  ihave %HeFne := errMsg_ne_nil _ _ $$ HmF
  wp_auto
  wp_apply readFull.wp_proof cv cid side P R (W64 8) $$ [$Hpkg $Hc $Hrecv] as %h %err ⟨%hd, Hrecv, Hres⟩
  · ipureintro; decide
  icases Hres with (⟨%Hok, Hh⟩ | ⟨%Hne, #Ha⟩)
  rotate_left
  · rcases err with ei | _
    · wp_auto
      iapply HΦ
      iexists hd
      iframe Hrecv
      iright; iframe Ha; ipureintro; exact Hne
    · exact absurd rfl Hne.1
  obtain ⟨rfl, Hhd⟩ := Hok
  wp_auto
  wp_apply wp_getU64 h _ hd Hhd $$ Hh as Hh
  wp_if_destruct
  · iapply HΦ
    iexists hd
    iframe Hrecv
    iright
    isplitr
    · ipureintro; exact ⟨HeFne, HnF⟩
    iapply errMsg_errAny; iexact HmF
  have hn : uint.Z (leToU64 hd) ≤ 2 ^ 26 := by
    have : uint.Z (W64 67108864) = 67108864 := by decide
    omega
  wp_apply readFull.wp_proof cv cid side P (R ++ hd) (leToU64 hd) $$ [$Hpkg $Hc $Hrecv]
    as %b %err ⟨%d2, Hrecv, Hres⟩
  · ipureintro; omega
  iapply HΦ
  iexists hd ++ d2
  rw [List.append_assoc]
  iframe Hrecv
  icases Hres with (⟨%Hok, Hb⟩ | ⟨%Hne, #Ha⟩)
  · ileft
    isplitr
    · ipureintro; exact Hok.1
    iexists d2
    iframe Hb
    ipureintro
    have hl : d2.length < 2 ^ 63 := by rw [Hok.2]; word
    refine ⟨?_, hl⟩
    unfold frameOf
    congr 1
    rw [← leToU64_le hd Hhd]
    congr 1
    rw [Hok.2]; word
  · iright; iframe Ha; ipureintro; exact Hne

theorem encodeMsg.wp_proof : encodeMsg.spec (GF := GF) (hG := hG) := by
  intro seq str body dq bs
  wp_start as Hbody
  ihave %Hbl := ownSlice_len _ _ _ $$ Hbody
  ihave %Hbb := ownSlice_bytes_len _ _ _ $$ Hbody
  wp_auto
  wp_apply wp_string_to_bytes str as %sb ⟨Hsb, -⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hsb
  ihave %Hsbb := ownSlice_bytes_len _ _ _ $$ Hsb
  have hsb : sb.len = W64 (str.length : Int) := by
    have := Hsl.2; rw [Hsl.1]; word
  have hbl : body.len = W64 (bs.length : Int) := by
    have := Hbl.2; rw [Hbl.1]; word
  wp_apply (wp_slice_make3 (V := w8) (W64 0) (W64 16 + sb.len + body.len)
    (by rw [hsb, hbl]; constructor <;> word)) as %b0 ⟨Hb0, Hb0cap, -⟩
  rw [List.replicate_zero]
  wp_apply wp_putU64 b0 [] seq $$ [$Hb0 $Hb0cap] as %b1 ⟨Hb1, Hb1cap⟩
  wp_apply wp_putU64 b1 _ sb.len $$ [$Hb1 $Hb1cap] as %b2 ⟨Hb2, Hb2cap⟩
  wp_apply wp_slice_append (V := w8) b2 _ sb str (DFrac.own 1) $$ [$Hb2 $Hb2cap $Hsb]
    as %b3 ⟨Hb3, Hb3cap, -⟩
  wp_apply wp_slice_append (V := w8) b3 _ body bs dq $$ [$Hb3 $Hb3cap $Hbody]
    as %b4 ⟨Hb4, -, Hbody⟩
  iapply HΦ
  rw [hsb]
  iframe

theorem decodeMsg.wp_proof : decodeMsg.spec (GF := GF) (hG := hG) := by
  intro p dq bs
  wp_start as Hp
  ihave %Hpl := ownSlice_len _ _ _ $$ Hp
  ihave %Hpw := ownSlice_wf _ _ _ $$ Hp
  ihave %Hpb := ownSlice_bytes_len _ _ _ $$ Hp
  have hpl : p.len = W64 (bs.length : Int) := by
    have := Hpl.2; rw [Hpl.1]; word
  wp_auto
  wp_if_destruct
  · iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  have hge : 16 ≤ bs.length := by
    have : uint.Z p.len = bs.length := by rw [hpl]; word
    have : uint.Z (W64 16) = 16 := by decide
    omega
  rw [ite_eq_left ⟨by decide, by decide, by word⟩]
  ihave ⟨H08, Hback⟩ := ownSlice_sub_acc (W64 0) (W64 8) p dq bs
    ⟨by decide, by decide, by rw [hpl]; word⟩ $$ Hp
  have h0 : sint.nat (W64 0) = 0 := rfl
  have h8 : sint.nat (W64 8) = 8 := rfl
  have h16 : sint.nat (W64 16) = 16 := rfl
  rw [h0, h8]
  wp_apply wp_getU64 _ dq _ (by simp [subslice]; omega) $$ H08 as H08
  ihave Hp := Hback $$ H08
  rw [ite_eq_left ⟨by decide, by decide, by word⟩]
  ihave ⟨H816, Hback⟩ := ownSlice_sub_acc (W64 8) (W64 16) p dq bs
    ⟨by decide, by decide, by rw [hpl]; word⟩ $$ Hp
  rw [h8, h16]
  wp_apply wp_getU64 _ dq _ (by simp [subslice]; omega) $$ H816 as H816
  ihave Hp := Hback $$ H816
  wp_if_destruct
  · iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  generalize hseq : leToU64 (subslice 0 8 bs) = sq at *
  generalize hnn : leToU64 (subslice 8 16 bs) = nn at *
  have hN : uint.Z nn ≤ bs.length - 16 := by
    have h1 : uint.Z p.len = bs.length := by rw [hpl]; word
    have h2 : uint.Z (p.len - W64 16) = uint.Z p.len - 16 := by
      have : uint.Z (W64 16) = 16 := by decide
      have : uint.Z (W64 16) ≤ uint.Z p.len := by omega
      word
    omega
  have hhi : sint.nat (W64 16 + nn) = 16 + uint.nat nn := by word
  have hhiZ : sint.Z (W64 16 + nn) = 16 + uint.Z nn := by word
  have hb : 0 ≤ sint.Z (W64 16) ∧ sint.Z (W64 16) ≤ sint.Z (W64 16 + nn) ∧
      sint.Z (W64 16 + nn) ≤ sint.Z p.len := by
    have h1 : sint.Z p.len = bs.length := by rw [hpl]; word
    have : sint.Z (W64 16) = 16 := by decide
    have := uint_Z_nonneg nn
    refine ⟨by omega, by omega, ?_⟩
    rw [hhiZ, h1]; omega
  rw [ite_eq_left ⟨hb.1, hb.2.1, by omega⟩]
  icases (ownSlice_slice (W64 16) (W64 16 + nn) p dq bs hb).1 $$ Hp with ⟨-, Hstr, Hbody⟩
  wp_apply wp_bytes_to_string $$ Hstr as -
  rw [ite_eq_left ⟨by omega, by omega, by omega⟩]
  wp_auto
  iapply HΦ
  simp only [↓reduceIte]
  iexists _
  iframe Hbody
  ipureintro
  rw [hhi]
  have hNn : uint.nat nn + 16 ≤ bs.length := by
    have : (uint.nat nn : Int) = uint.Z nn := by word
    omega
  have hsl : (subslice 16 (16 + uint.nat nn) bs).length = uint.nat nn := by
    rw [subslice_length _ _ _ (by omega)]; omega
  refine ⟨?_, by rw [hsl]; word⟩
  unfold msgOf
  rw [hsl, show W64 ((uint.nat nn : Nat) : Int) = nn by word, ← hseq, ← hnn,
    leToU64_le _ (by simp [subslice]; omega), leToU64_le _ (by simp [subslice]; omega),
    subslice_app_contig _ _ _ _ (by omega) (by omega),
    subslice_app_contig _ _ _ _ (by omega) (by omega), subslice_from_start,
    List.take_append_drop]

theorem lastDot.wp_proof : lastDot.spec (GF := GF) (hG := hG) := by
  intro str
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜-1 ≤ sint.Z i ∧ sint.Z i < str.length ∧
        ∀ j : Nat, sint.Z i < j → j < str.length → str[j]? ≠ some (W8 46)⌝ : IProp GF) $$ [i]
  · iexists _
    iframe
    ipureintro
    have h : sint.Z (W64 (str.length : Int) - W64 1) = str.length - 1 := by word
    rw [h]
    refine ⟨by omega, by omega, fun j h1 h2 => by omega⟩
  wp_for HI
  wp_if_destruct
  · have hi0 : 0 ≤ sint.Z i := by have : sint.Z (W64 0) = 0 := rfl; omega
    have hsn : (sint.nat i : Int) = sint.Z i := by
      show ((sint.Z i).toNat : Int) = _; omega
    have hlt : sint.nat i < str.length := by omega
    obtain ⟨b, hb⟩ : ∃ b, str[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [ite_eq_left hi0, hb]
    wp_auto
    wp_if_destruct
    · wp_for_post
      iapply HΦ
      ipureintro
      rw [lastDotIdx_some str (sint.nat i) hlt hb (fun j h1 h2 =>
        Hi.2.2 j (by omega) h2)]
      refine ⟨by word, by omega⟩
    · wp_for_post
      iframe
      iexists i - W64 1
      iframe
      ipureintro
      have h1 : sint.Z (i - W64 1) = sint.Z i - 1 := by word
      rw [h1]
      refine ⟨by omega, by omega, fun j hj1 hj2 => ?_⟩
      by_cases hj : (j : Int) = sint.Z i
      · have : j = sint.nat i := by omega
        subst this; rw [hb]; intro h; apply Hif; simpa using h
      · exact Hi.2.2 j (by omega) hj2
  · have hi : sint.Z i = -1 := by have : sint.Z (W64 0) = 0 := rfl; omega
    iapply HΦ
    ipureintro
    rw [lastDotIdx_none str (fun j hj => Hi.2.2 j (by omega) hj)]
    decide

end proofs

end net.rpc

end Perennial
