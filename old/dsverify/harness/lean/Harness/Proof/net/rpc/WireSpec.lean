/-
The specs of the lab's `net/rpc` model's framing helpers (`wire.go`; `notes/craq-net.md`, "rpc
specs"), stated over the `net` model's specs (`Spec/net/TCPConn__{Read,Write}`) and the pure wire
format of `Proto.lean`; proved in `Wire.lean`. Also the pure facts readers use to parse a stream
written as frames (a frame's length prefix determines it, `msgOf` is injective).

* `readFull(c, n)`: `n` more bytes of the stream (all read bytes are consumed, also on an error);
  `n < 2 ^ 63` (`make` panics otherwise).
* `readFrame(c)`: the next frame `frameOf p` of the stream and its payload `p` (on an error,
  some bytes may have been consumed).
* `writeFrame(c, p)`: appends `frameOf p` to the stream (a prefix of it on an error), with the
  stream's protocol of the result.
* An error of these three is the `net` model's (`connErr`: `io.EOF` or an `*OpError`) or
  `errFrame` (`errors.New`): never a `ServerError` (`notServerErr`), and its dynamic type
  implements `error` with some `Error()` (`errAny`). The laws giving these facts of `errors.New`
  and `newVar` errors, `*OpError`s and `connErr` are below (`newVar_errMsg`, `opErr_errAny`,
  `connErr_errAny`).
* `encodeMsg(seq, s, body)`: a fresh slice holding `msgOf seq s body`.
* `decodeMsg(p)`: `(seq, s, body, true)` with `p = msgOf seq s body` (`body` a sub-slice of
  `p`), or `ok = false`.
-/
module

public import Harness.Proof.net.rpc.Defs
public import Harness.Proof.net.rpc.Base
public import Harness.Proof.net.TCPConn__Read
public import Harness.Proof.net.TCPConn__Write

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std NetConn

namespace net.rpc

/-! ## Pure facts (proved here) -/

/-- The length of a frame. -/
theorem frameOf_length (p : List w8) : (frameOf p).length = 8 + p.length := by
  simp [frameOf, u64Le_length]

theorem framesOf_nil : framesOf [] = [] := rfl

theorem framesOf_cons (p : List w8) (ps : List (List w8)) :
    framesOf (p :: ps) = frameOf p ++ framesOf ps := by
  simp [framesOf]

theorem framesOf_append (ps qs : List (List w8)) :
    framesOf (ps ++ qs) = framesOf ps ++ framesOf qs := by
  simp [framesOf]

theorem framesOf_concat (ps : List (List w8)) (p : List w8) :
    framesOf (ps ++ [p]) = framesOf ps ++ frameOf p := by
  simp [framesOf]

/-- The frames of a prefix of the payloads are a prefix of the frames. -/
theorem framesOf_take_prefix (ps : List (List w8)) (k : Nat) :
    framesOf (ps.take k) <+: framesOf ps := by
  conv => rhs; rw [← List.take_append_drop k ps]
  rw [framesOf_append]; exact List.prefix_append _ _

/-- `W64` is injective below `2 ^ 64`. -/
theorem W64_natCast_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : (W64 a : w64) = W64 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp [W64] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- Two frames at the start of a stream agree (payloads shorter than `2 ^ 63`). -/
theorem frameOf_prefix_eq {p p' x y : List w8} (hp : p.length < 2 ^ 63)
    (hp' : p'.length < 2 ^ 63) (h : frameOf p ++ x <+: frameOf p' ++ y) : p = p' := by
  obtain ⟨t, ht⟩ := h
  simp only [frameOf, List.append_assoc] at ht
  obtain ⟨h1, h2⟩ := List.append_inj ht (by simp [u64Le_length])
  have hl : p.length = p'.length :=
    W64_natCast_inj (by omega) (by omega) (u64Le_inj h1)
  exact (List.append_inj h2 hl).1

/-- A stream of whole frames `framesOf qs` followed by a frame `frameOf p` that is a prefix of
frames `framesOf ps` (each payload shorter than `2 ^ 63`): `qs` are `ps`'s first frames and `p`
is the next. -/
theorem framesOf_next {qs ps : List (List w8)} {p : List w8}
    (hqs : ∀ q ∈ qs, q.length < 2 ^ 63)
    (hps : ∀ q ∈ ps, q.length < 2 ^ 63) (hp : p.length < 2 ^ 63)
    (h : framesOf qs ++ frameOf p <+: framesOf ps) :
    ps.take qs.length = qs ∧ ps[qs.length]? = some p := by
  induction qs generalizing ps with
  | nil =>
    cases ps with
    | nil =>
      exfalso
      have := h.length_le
      simp [framesOf_nil, frameOf_length] at this
    | cons p' ps' =>
      rw [framesOf_cons] at h
      have := frameOf_prefix_eq (x := []) hp (hps p' (by simp)) (by simpa [framesOf_nil] using h)
      subst this; simp
  | cons q qs ih =>
    cases ps with
    | nil =>
      exfalso
      have := h.length_le
      simp [framesOf_nil, framesOf_cons, frameOf_length] at this
    | cons p' ps' =>
      rw [framesOf_cons, framesOf_cons, List.append_assoc] at h
      have hq : q = p' := frameOf_prefix_eq (hqs q (by simp)) (hps p' (by simp)) h
      subst hq
      rw [List.prefix_append_right_inj] at h
      obtain ⟨h1, h2⟩ := ih (fun q' hq' => hqs q' (by simp [hq'])) (fun q' hq' => hps q' (by simp [hq'])) h
      simp [h1, h2]

/-- `framesOf_next` after a common head (a response stream starts with `connectedBytes`). -/
theorem framesOf_next_hd {hd : List w8} {qs ps : List (List w8)} {p : List w8}
    (hqs : ∀ q ∈ qs, q.length < 2 ^ 63)
    (hps : ∀ q ∈ ps, q.length < 2 ^ 63) (hp : p.length < 2 ^ 63)
    (h : hd ++ framesOf qs ++ frameOf p <+: hd ++ framesOf ps) :
    ps.take qs.length = qs ∧ ps[qs.length]? = some p := by
  rw [List.append_assoc, List.prefix_append_right_inj] at h
  exact framesOf_next hqs hps hp h

/-- `msgOf` is injective (for strings shorter than `2 ^ 63`). -/
theorem msgOf_inj {seq1 seq2 : w64} {s1 s2 : GoString} {b1 b2 : List w8}
    (h1 : s1.length < 2 ^ 63) (h2 : s2.length < 2 ^ 63)
    (h : msgOf seq1 s1 b1 = msgOf seq2 s2 b2) : seq1 = seq2 ∧ s1 = s2 ∧ b1 = b2 := by
  simp only [msgOf, List.append_assoc] at h
  obtain ⟨hs, h⟩ := List.append_inj h (by simp [u64Le_length])
  obtain ⟨hn, h⟩ := List.append_inj h (by simp [u64Le_length])
  have hl : s1.length = s2.length := W64_natCast_inj (by omega) (by omega) (u64Le_inj hn)
  obtain ⟨hs', hb⟩ := List.append_inj h hl
  exact ⟨u64Le_inj hs, hs', hb⟩

/-- The length of a message. -/
theorem msgOf_length (seq : w64) (s : GoString) (body : List w8) :
    (msgOf seq s body).length = 16 + s.length + body.length := by
  simp [msgOf, u64Le_length]; omega

/-! ## The errors' identity -/

section errs
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- An error whose dynamic type is a pointer type is not a `ServerError`. -/
theorem notServerErr_ptr (T : go.GoType) (v : val) :
    notServerErr (interface.mkOk (go.GoType.PointerType T) v) := by
  intro e h
  simp only [interface.mkOk, GoInterface.ok.injEq] at h
  subst h
  unfold net.rpc.ServerError.ty
  simp

theorem notServerErr_nil : notServerErr interface.nil := by
  intro e h; cases h

/-- A pointer error (`errors.New`'s) is not a `ServerError`. -/
theorem notServerErr_pointerError (e : GoInterfaceOk) (h : errors.IsPointerError e) :
    notServerErr (interface.ok e) := by
  obtain ⟨T, l, hT, hv⟩ := h
  have : e = ⟨go.GoType.PointerType T, #l⟩ := by cases e; simp_all
  subst this
  exact notServerErr_ptr T #l

end errs

section errmsg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `*errors.errorString` implements `error`. -/
theorem errorString_isError [errors.Assumptions] :
    go.typeSetContains (go.GoType.PointerType errors.errorString.ty) go.error = true := by
  go_type_set

/-- `errors.New`'s result (`errors.New.spec`'s postcondition) has its message and is not a
`ServerError`. -/
theorem newErr_errMsg (e : GoInterfaceOk) (msg : GoString)
    (ht : go.typeSetContains e.ty go.error = true) :
    (⌜errors.IsPointerError e⌝ ∗
      □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
        WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }}) ⊢
      errMsg (interface.ok e) msg ∗ ⌜notServerErr (interface.ok e)⌝ := by
  iintro ⟨%Hp, #H⟩
  isplitl
  · unfold errMsg
    iexists e
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact ht
    iexact H
  · ipureintro; exact notServerErr_pointerError e Hp

/-- A package variable made by `errors.New` holds an error with its message, not a
`ServerError`. -/
theorem newVar_errMsg [errors.Assumptions] (X msg : GoString) (e : GoInterface) :
    (errors.newVar (GF := GF) X msg ∗ globalAddr X ↦□ e) ⊢
      errMsg e msg ∗ ⌜notServerErr e⌝ := by
  unfold errors.newVar
  iintro ⟨⟨%x, #Hx, #H⟩, #He⟩
  icombine Hx He gives %h
  subst h
  isplitl
  · unfold errMsg
    iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact errorString_isError
    iexact H
  · ipureintro; exact notServerErr_ptr _ _

/-- `newVar_errMsg` with the variable's value. -/
theorem newVar_errMsg' [errors.Assumptions] (X msg : GoString) :
    errors.newVar (GF := GF) X msg ⊢
      ∃ e : GoInterface, globalAddr X ↦□ e ∗ errMsg e msg ∗ ⌜notServerErr e⌝ := by
  unfold errors.newVar
  iintro ⟨%x, #Hx, #H⟩
  iexists _
  iframe Hx
  isplitl
  · unfold errMsg
    iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact errorString_isError
    iexact H
  · ipureintro; exact notServerErr_ptr _ _

end errmsg

section neterrs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

/-- An `*OpError` has some message and is not a `ServerError`. -/
theorem opErr_errAny (op : GoString) (code : w64) (err : GoInterface) :
    net.opErr (GF := GF) op code err ⊢ errAny err ∗ ⌜notServerErr err⌝ := by
  unfold net.opErr
  iintro ⟨%e, %inner, %h, -⟩
  subst h
  isplitl
  · unfold errAny
    iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; go_type_set
    imodintro
    iintro %Φ HΦ
    wp_method_call
    unfold net.OpError.Error.impl
    wp_call
    wp_apply net.wp_arbitraryString as %s -
    iapply HΦ
  · ipureintro; exact notServerErr_ptr _ _

/-- The `net` model's error of a connection operation: `nil`, or one with some message that is
not a `ServerError`. -/
theorem connErr_errAny (op : GoString) (code : w64) (err : GoInterface) :
    (isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.connErr op code err) ⊢
      ⌜err = interface.nil⌝ ∨ (errAny err ∗ ⌜notServerErr err⌝) := by
  unfold net.connErr
  iintro ⟨#Hpkg, Herr⟩
  by_cases h0 : code = NetConn.errNone
  · simp only [h0, ite_true]
    ileft; iexact Herr
  simp only [h0, ite_false]
  iright
  by_cases h1 : code = NetConn.errEOF
  · simp only [h1, ite_true]
    icases Herr with ⟨-, #He⟩
    ihave #Hio := net.io_init_of_net $$ Hpkg
    ihave #Hv := io.eof_of_init $$ Hio
    ihave ⟨#Hm, %Hn⟩ := newVar_errMsg _ _ _ $$ [Hv He]
    · isplitl [Hv]; iexact Hv; iexact He
    isplitl
    · iapply errMsg_errAny; iexact Hm
    · ipureintro; exact Hn
  · simp only [h1, ite_false]
    iapply opErr_errAny; iexact Herr

end neterrs

/-! ## The specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions] [RpcKit]

/-- `readFull(c, n)`: see the file header. -/
abbrev readFull.spec : Prop :=
  ∀ (cv : GoInterface) (cid : w64) (side : Bool) (P : Proto GF) (R : List w8) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ connIface cv cid side ∗ recvTok cid side P R ∗
      ⌜uint.Z n < 2 ^ 63⌝ }}
    (App (App (Val (@! net.rpc.readFull)) (Val #cv)) (Val #n))
  {{ (b : GoSlice) (err : GoInterface), RET (PairV #b #err);
      ∃ data : List w8, recvTok cid side P (R ++ data) ∗
      ((⌜err = interface.nil ∧ data.length = uint.nat n⌝ ∗ b ↦* data) ∨
        (⌜err ≠ interface.nil ∧ notServerErr err⌝ ∗ errAny err)) }}

/-- `readFrame(c)`: see the file header. -/
abbrev readFrame.spec : Prop :=
  ∀ (cv : GoInterface) (cid : w64) (side : Bool) (P : Proto GF) (R : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗
      connIface cv cid side ∗ recvTok cid side P R }}
    (App (Val (@! net.rpc.readFrame)) (Val #cv))
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
    (App (App (Val (@! net.rpc.writeFrame)) (Val #cv)) (Val #p))
  {{ (err : GoInterface), RET #err;
      ∃ k : Nat, ⌜k ≤ (frameOf pl).length ∧ (err = interface.nil → k = (frameOf pl).length) ∧
        notServerErr err⌝ ∗ (⌜err = interface.nil⌝ ∨ errAny err) ∗
      sendTok cid side P (W ++ (frameOf pl).take k) ∗ p ↦*{dq} pl }}

/-- `encodeMsg(seq, s, body)`: see the file header. -/
abbrev encodeMsg.spec : Prop :=
  ∀ (seq : w64) (s : GoString) (body : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ body ↦*{dq} bs }}
    (App (App (App (Val (@! net.rpc.encodeMsg)) (Val #seq)) (Val #s)) (Val #body))
  {{ (r : GoSlice), RET #r; r ↦* msgOf seq s bs ∗ body ↦*{dq} bs }}

/-- `decodeMsg(p)`: see the file header. -/
abbrev decodeMsg.spec : Prop :=
  ∀ (p : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ p ↦*{dq} bs }}
    (App (Val (@! net.rpc.decodeMsg)) (Val #p))
  {{ (seq : w64) (s : GoString) (body : GoSlice) (ok : Bool),
      RET (PairV (PairV (PairV #seq #s) #body) #ok);
      if ok then ∃ b : List w8, ⌜bs = msgOf seq s b ∧ s.length < 2 ^ 63⌝ ∗ body ↦*{dq} b
      else iprop(True) }}

/-- `lastDot(s)`: the index of `s`'s last `'.'` (`lastDotIdx`), or `-1`. -/
abbrev lastDot.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc }}
    (App (Val (@! net.rpc.lastDot)) (Val #s))
  {{ (i : w64), RET #i;
      ⌜match lastDotIdx s with
        | some j => uint.nat i = j ∧ sint.Z i = j
        | none => sint.Z i = -1⌝ }}

end spec

end net.rpc

end Perennial
