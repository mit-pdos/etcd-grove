/-
The specs and proofs of the grpc model's framing helpers (`wire.go`): `readFull`, `readFrame`,
`writeFrame`, `encodeMsg`, `decodeMsg` (and `lastSlash`, `server.go`), over the `net` model's
specs and the pure wire format of `Proto.lean`. The framing is the net/rpc model's (the same
Go code), so the specs and proofs are those of `Harness/Proof/net/rpc/{WireSpec,Wire}.lean` for
this package's functions; a payload has a tag before the sequence number.

* `readFull(c, n)`: `n` more bytes of the stream (all read bytes are consumed, also on an error).
* `readFrame(c)`: the next frame `frameOf p` of the stream and its payload `p` (on an error,
  some bytes may have been consumed).
* `writeFrame(c, p)`: appends `frameOf p` to the stream (a prefix of it on an error).
* Errors of these three: the `net` model's or `errFrame`, with some `Error()` (`errAny`).
* `encodeMsg(tag, seq, s, body)`: a fresh slice holding `msgOf tag seq s body`.
* `decodeMsg(p)`: `(tag, seq, s, body, true)` with `p = msgOf tag seq s body` (`body` a
  sub-slice of `p`), or `ok = false`.
-/
module

public import Harness.Proof.grpc.Proto
public import Harness.Proof.net.rpc.Wire

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn
open net.rpc (frameOf framesOf connIface errAny errMsg notServerErr connErr_errAny newVar_errMsg'
  errMsg_ne_nil errMsg_errAny notServerErr_nil ownSlice_bytes_len ownSlice_drop_acc
  ownSlice_sub_acc lastDotIdx_some lastDotIdx_none)

namespace google_golang_org.grpc

/-! ## Pure facts -/

/-- `msgOf` is injective (for strings shorter than `2 ^ 63`). -/
theorem msgOf_inj {t1 t2 seq1 seq2 : w64} {s1 s2 : GoString} {b1 b2 : List w8}
    (h1 : s1.length < 2 ^ 63) (h2 : s2.length < 2 ^ 63)
    (h : msgOf t1 seq1 s1 b1 = msgOf t2 seq2 s2 b2) :
    t1 = t2 ∧ seq1 = seq2 ∧ s1 = s2 ∧ b1 = b2 := by
  simp only [msgOf, List.append_assoc] at h
  obtain ⟨ht, h⟩ := List.append_inj h (by simp [u64Le_length])
  obtain ⟨hs, h⟩ := List.append_inj h (by simp [u64Le_length])
  obtain ⟨hn, h⟩ := List.append_inj h (by simp [u64Le_length])
  have hl : s1.length = s2.length :=
    net.rpc.W64_natCast_inj (by omega) (by omega) (u64Le_inj hn)
  obtain ⟨hs', hb⟩ := List.append_inj h hl
  exact ⟨u64Le_inj ht, u64Le_inj hs, hs', hb⟩

/-- The length of a payload. -/
theorem msgOf_length (tag seq : w64) (s : GoString) (body : List w8) :
    (msgOf tag seq s body).length = 24 + s.length + body.length := by
  simp [msgOf, u64Le_length]; omega

/-- The index of the last `'/'` of `s` (`lastSlash`). -/
def lastSlashIdx (s : GoString) : Option Nat :=
  ((List.range s.length).reverse.find? (fun i => s[i]? = some (W8 47)))

theorem lastSlashIdx_none (s : GoString) (h : ∀ j < s.length, s[j]? ≠ some (W8 47)) :
    lastSlashIdx s = none := by
  unfold lastSlashIdx
  exact net.rpc.find_range_reverse_none _ _ (fun j hj => by simpa using h j hj)

theorem lastSlashIdx_some (s : GoString) (k : Nat) (hk : k < s.length) (hd : s[k]? = some (W8 47))
    (h : ∀ j, k < j → j < s.length → s[j]? ≠ some (W8 47)) :
    lastSlashIdx s = some k := by
  unfold lastSlashIdx
  exact net.rpc.find_range_reverse_some _ _ _ hk (by simpa using hd)
    (fun j h1 h2 => by simpa using h j h1 h2)

/-! ## The specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [google_golang_org.grpc.Assumptions]
variable [google_golang_org.protobuf.proto.PbKit]

/-- `readFull(c, n)`: see the file header. -/
abbrev readFull.spec : Prop :=
  ∀ (cv : GoInterface) (cid : w64) (side : Bool) (P : Proto GF) (R : List w8) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ connIface cv cid side ∗ recvTok cid side P R ∗
      ⌜uint.Z n < 2 ^ 63⌝ }}
    (App (App (Val (@! google_golang_org.grpc.readFull)) (Val #cv)) (Val #n))
  {{ (b : GoSlice) (err : GoInterface), RET (PairV #b #err);
      ∃ data : List w8, recvTok cid side P (R ++ data) ∗
      ((⌜err = interface.nil ∧ data.length = uint.nat n⌝ ∗ b ↦* data) ∨
        (⌜err ≠ interface.nil ∧ notServerErr err⌝ ∗ errAny err)) }}

/-- `readFrame(c)`: see the file header. -/
abbrev readFrame.spec : Prop :=
  ∀ (cv : GoInterface) (cid : w64) (side : Bool) (P : Proto GF) (R : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗
      connIface cv cid side ∗ recvTok cid side P R }}
    (App (Val (@! google_golang_org.grpc.readFrame)) (Val #cv))
  {{ (p : GoSlice) (err : GoInterface), RET (PairV #p #err);
      ∃ data : List w8, recvTok cid side P (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ pl : List w8, ⌜data = frameOf pl ∧ pl.length < 2 ^ 63⌝ ∗
          p ↦* pl) ∨
        (⌜err ≠ interface.nil ∧ notServerErr err⌝ ∗ errAny err)) }}

/-- `writeFrame(c, p)`: see the file header. -/
abbrev writeFrame.spec : Prop :=
  ∀ (cv : GoInterface) (cid : w64) (side : Bool) (P : Proto GF) (W : List w8) (p : GoSlice)
    (dq : DFrac) (pl : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ connIface cv cid side ∗ sendTok cid side P W ∗
      □ P cid (W ++ frameOf pl) ∗ p ↦*{dq} pl }}
    (App (App (Val (@! google_golang_org.grpc.writeFrame)) (Val #cv)) (Val #p))
  {{ (err : GoInterface), RET #err;
      ∃ k : Nat, ⌜k ≤ (frameOf pl).length ∧ (err = interface.nil → k = (frameOf pl).length) ∧
        notServerErr err⌝ ∗ (⌜err = interface.nil⌝ ∨ errAny err) ∗
      sendTok cid side P (W ++ (frameOf pl).take k) ∗ p ↦*{dq} pl }}

/-- `encodeMsg(tag, seq, s, body)`: see the file header. -/
abbrev encodeMsg.spec : Prop :=
  ∀ (tag seq : w64) (s : GoString) (body : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ body ↦*{dq} bs }}
    (App (App (App (App (Val (@! google_golang_org.grpc.encodeMsg)) (Val #tag)) (Val #seq))
      (Val #s)) (Val #body))
  {{ (r : GoSlice), RET #r; r ↦* msgOf tag seq s bs ∗ body ↦*{dq} bs }}

/-- `decodeMsg(p)`: see the file header. -/
abbrev decodeMsg.spec : Prop :=
  ∀ (p : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ p ↦*{dq} bs }}
    (App (Val (@! google_golang_org.grpc.decodeMsg)) (Val #p))
  {{ (tag seq : w64) (s : GoString) (body : GoSlice) (ok : Bool),
      RET (PairV (PairV (PairV (PairV #tag #seq) #s) #body) #ok);
      if ok then ∃ b : List w8, ⌜bs = msgOf tag seq s b ∧ s.length < 2 ^ 63⌝ ∗ body ↦*{dq} b
      else iprop(True) }}

/-- `lastSlash(s)`: the index of `s`'s last `'/'` (`lastSlashIdx`), or `-1`. -/
abbrev lastSlash.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.lastSlash)) (Val #s))
  {{ (i : w64), RET #i;
      ⌜match lastSlashIdx s with
        | some j => uint.nat i = j ∧ sint.Z i = j
        | none => sint.Z i = -1⌝ }}

end spec

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [google_golang_org.grpc.Assumptions]
variable [google_golang_org.protobuf.proto.PbKit]

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
      (App (App (Val (@! google_golang_org.grpc.putU64)) (Val #b)) (Val #x))
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
      (App (Val (@! google_golang_org.grpc.getU64)) (Val #b))
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
  ihave #Hinit := isInit_access $$ Hpkg2
  icases Hinit with ⟨#HerrFrame, -⟩
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
  have hn : uint.Z (leToU64 hd) ≤ 2 ^ 32 := by
    have : uint.Z (W64 4294967296) = 4294967296 := by decide
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
  intro tag seq str body dq bs
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
  wp_apply (wp_slice_make3 (V := w8) (W64 0) (W64 24 + sb.len + body.len)
    (by rw [hsb, hbl]; constructor <;> word)) as %b0 ⟨Hb0, Hb0cap, -⟩
  rw [List.replicate_zero]
  wp_apply wp_putU64 b0 [] tag $$ [$Hb0 $Hb0cap] as %b1 ⟨Hb1, Hb1cap⟩
  wp_apply wp_putU64 b1 _ seq $$ [$Hb1 $Hb1cap] as %b1' ⟨Hb1', Hb1cap'⟩
  wp_apply wp_putU64 b1' _ sb.len $$ [$Hb1' $Hb1cap'] as %b2 ⟨Hb2, Hb2cap⟩
  wp_apply wp_slice_append (V := w8) b2 _ sb str (DFrac.own 1) $$ [$Hb2 $Hb2cap $Hsb]
    as %b3 ⟨Hb3, Hb3cap, -⟩
  wp_apply wp_slice_append (V := w8) b3 _ body bs dq $$ [$Hb3 $Hb3cap $Hbody]
    as %b4 ⟨Hb4, -, Hbody⟩
  iapply HΦ
  rw [hsb]
  unfold msgOf
  simp only [List.nil_append]
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
  have hge : 24 ≤ bs.length := by
    have : uint.Z p.len = bs.length := by rw [hpl]; word
    have : uint.Z (W64 24) = 24 := by decide
    omega
  rw [ite_eq_left ⟨by decide, by decide, by word⟩]
  ihave ⟨H08, Hback⟩ := ownSlice_sub_acc (W64 0) (W64 8) p dq bs
    ⟨by decide, by decide, by rw [hpl]; word⟩ $$ Hp
  have h0 : sint.nat (W64 0) = 0 := rfl
  have h8 : sint.nat (W64 8) = 8 := rfl
  have h16 : sint.nat (W64 16) = 16 := rfl
  have h24 : sint.nat (W64 24) = 24 := rfl
  rw [h0, h8]
  wp_apply wp_getU64 _ dq _ (by simp [subslice]; omega) $$ H08 as H08
  ihave Hp := Hback $$ H08
  rw [ite_eq_left ⟨by decide, by decide, by word⟩]
  ihave ⟨H816, Hback⟩ := ownSlice_sub_acc (W64 8) (W64 16) p dq bs
    ⟨by decide, by decide, by rw [hpl]; word⟩ $$ Hp
  rw [h8, h16]
  wp_apply wp_getU64 _ dq _ (by simp [subslice]; omega) $$ H816 as H816
  ihave Hp := Hback $$ H816
  rw [ite_eq_left ⟨by decide, by decide, by word⟩]
  ihave ⟨H1624, Hback⟩ := ownSlice_sub_acc (W64 16) (W64 24) p dq bs
    ⟨by decide, by decide, by rw [hpl]; word⟩ $$ Hp
  rw [h16, h24]
  wp_apply wp_getU64 _ dq _ (by simp [subslice]; omega) $$ H1624 as H1624
  ihave Hp := Hback $$ H1624
  wp_if_destruct
  · iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  generalize htag : leToU64 (subslice 0 8 bs) = tg at *
  generalize hseq : leToU64 (subslice 8 16 bs) = sq at *
  generalize hnn : leToU64 (subslice 16 24 bs) = nn at *
  have hN : uint.Z nn ≤ bs.length - 24 := by
    have h1 : uint.Z p.len = bs.length := by rw [hpl]; word
    have h2 : uint.Z (p.len - W64 24) = uint.Z p.len - 24 := by
      have : uint.Z (W64 24) = 24 := by decide
      have : uint.Z (W64 24) ≤ uint.Z p.len := by omega
      word
    omega
  have hhi : sint.nat (W64 24 + nn) = 24 + uint.nat nn := by word
  have hhiZ : sint.Z (W64 24 + nn) = 24 + uint.Z nn := by word
  have hb : 0 ≤ sint.Z (W64 24) ∧ sint.Z (W64 24) ≤ sint.Z (W64 24 + nn) ∧
      sint.Z (W64 24 + nn) ≤ sint.Z p.len := by
    have h1 : sint.Z p.len = bs.length := by rw [hpl]; word
    have : sint.Z (W64 24) = 24 := by decide
    have := uint_Z_nonneg nn
    refine ⟨by omega, by omega, ?_⟩
    rw [hhiZ, h1]; omega
  rw [ite_eq_left ⟨hb.1, hb.2.1, by omega⟩]
  icases (ownSlice_slice (W64 24) (W64 24 + nn) p dq bs hb).1 $$ Hp with ⟨-, Hstr, Hbody⟩
  wp_apply wp_bytes_to_string $$ Hstr as -
  rw [ite_eq_left ⟨by omega, by omega, by omega⟩]
  wp_auto
  iapply HΦ
  simp only [↓reduceIte]
  iexists _
  iframe Hbody
  ipureintro
  rw [hhi]
  have hNn : uint.nat nn + 24 ≤ bs.length := by
    have : (uint.nat nn : Int) = uint.Z nn := by word
    omega
  have hsl : (subslice 24 (24 + uint.nat nn) bs).length = uint.nat nn := by
    rw [subslice_length _ _ _ (by omega)]; omega
  refine ⟨?_, by rw [hsl]; word⟩
  unfold msgOf
  rw [hsl, show W64 ((uint.nat nn : Nat) : Int) = nn by word, ← htag, ← hseq, ← hnn,
    leToU64_le _ (by simp [subslice]; omega), leToU64_le _ (by simp [subslice]; omega),
    leToU64_le _ (by simp [subslice]; omega),
    subslice_app_contig _ _ _ _ (by omega) (by omega),
    subslice_app_contig _ _ _ _ (by omega) (by omega),
    subslice_app_contig _ _ _ _ (by omega) (by omega), subslice_from_start,
    List.take_append_drop]

theorem lastSlash.wp_proof : lastSlash.spec (GF := GF) (hG := hG) := by
  intro str
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜-1 ≤ sint.Z i ∧ sint.Z i < str.length ∧
        ∀ j : Nat, sint.Z i < j → j < str.length → str[j]? ≠ some (W8 47)⌝ : IProp GF) $$ [i]
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
      rw [lastSlashIdx_some str (sint.nat i) hlt hb (fun j h1 h2 =>
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
    rw [lastSlashIdx_none str (fun j hj => Hi.2.2 j (by omega) hj)]
    decide

end proofs

end google_golang_org.grpc

end Perennial
