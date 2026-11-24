/-
The vocabulary of the specs of net/http's request reading (`readRequest` and what it calls, the model
`models/net/http`), beside `Defs.lean`'s:

* `pathByte c`: `c` is a byte the model's `modelPathByte` accepts, one net/url leaves alone in a path
  (RFC 3986's unreserved bytes and `$&+,/:;=@`);
* `reqPath s`: `s` starts with `/` and has only such bytes: the request URIs on which the model's
  `modelParseRequestURI` computes `url.ParseRequestURI`'s result itself (the URL with path `s`);
* `parseReqLine l`: what `parseRequestLine(l)` returns, the method, the request URI and the protocol
  (the two `modelCutByte`s at `' '`) and `true`, or empties and `false`;
* `connectReqVal path u m cl nb`, `connectReqv req path`: the request `readRequestLimit` returns for
  net/rpc's `CONNECT path HTTP/1.0` request: method, request URI, version, the URL `u` (its `Path`
  `path`, nothing else), an empty header map `m`, no body (`NoBody`'s value `nb`, `ContentLength`
  `0`), no `Host`, its `Close` `cl` (`shouldClose`'s);
* `errMsgOk e`: `e` is an error whose `Error()` returns some string (`fmt.stringMethodSpec`), what
  `readRequestLimit` asks of its stream's errors (it calls `Error()` on the header reader's).
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

/-- See the file header. -/
def pathByte (c : w8) : Bool :=
  decide ((97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
    (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨
    c ∈ [W8 45, W8 95, W8 46, W8 126, W8 36, W8 38, W8 43, W8 44, W8 47, W8 58, W8 59, W8 61, W8 64])

/-- See the file header. -/
def reqPath (s : List w8) : Prop := s.head? = some (W8 47) ∧ ∀ c ∈ s, pathByte c = true

/-- See the file header. -/
def parseReqLine (l : List w8) : List w8 × List w8 × List w8 × Bool :=
  let c1 := cutByte l (W8 32)
  let c2 := cutByte c1.2.1 (W8 32)
  if c1.2.2 && c2.2.2 then (c1.1, c2.1, c2.2.1, true) else ([], [], [], false)

section req
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- See the file header. -/
def connectReqVal (path : List w8) (u m : Loc) (cl : Bool) (nb : net.http.noBody) : net.http.Request :=
  { (_root_.Perennial.zero_val net.http.Request) with
    Method' := go!"CONNECT", URL' := u, Proto' := go!"HTTP/1.0", ProtoMajor' := W64 1,
    ProtoMinor' := W64 0, Header' := m, Body' := interface.mkOk net.http.noBody.ty #nb,
    ContentLength' := W64 0, Close' := cl, Host' := [], RequestURI' := path, Trailer' := map.nil }

end req

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def connectReqv (req : Loc) (path : List w8) : IProp GF :=
  iprop(∃ (u m : Loc) (cl : Bool) (nb : net.http.noBody), req ↦ connectReqVal path u m cl nb ∗
    u ↦ { (_root_.Perennial.zero_val net.url.URL) with Path' := path } ∗
    m ↦$ (∅ : GMap GoString GoSlice))

/-- See the file header. -/
def errMsgOk (e : GoInterface) : IProp GF :=
  iprop(∃ ii : GoInterfaceOk, ⌜e = interface.ok ii⌝ ∗ fmt.stringMethodSpec ii go!"Error")

instance errMsgOk_persistent (e : GoInterface) : Persistent (errMsgOk (GF := GF) e) := by
  unfold errMsgOk; infer_instance

end preds

section errs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

open Iris.ProgramLogic Iris.ProofMode

/-- An error whose `Error()` returns a fixed string (`errors.New`'s, `errors.newVar`'s) has
`errMsgOk`. -/
theorem errMsgOk_of_wp (ii : GoInterfaceOk) (s : GoString) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #s -∗
      WP (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #())) {{ Φ }}) ⊢
      errMsgOk (interface.ok ii) := by
  iintro #H
  unfold errMsgOk
  iexists ii
  isplitr
  · ipureintro; rfl
  rw [fmt.stringMethodSpec_unfold]
  imodintro
  iintro %Φ HΦ
  iapply H
  inext
  iapply HΦ

/-- A `textproto.ProtocolError`'s `Error()` returns its message. -/
theorem protocolError_msg (msg : GoString) :
    ⊢ fmt.stringMethodSpec (GF := GF) ⟨net.textproto.ProtocolError.ty, #msg⟩ go!"Error" := by
  unfold fmt.stringMethodSpec
  iintro !>
  iintro %Φ HΦ
  rw [method_unfold (t := net.textproto.ProtocolError.ty) (m := go!"Error")]
  wp_auto
  iapply HΦ

/-- The header reader's errors have an `Error()` method. -/
theorem mimeErr_msg (E : List w8 → GoInterface → IProp GF) (err : GoInterface) :
    (□ ∀ (r : List w8) (e : GoInterface), E r e -∗ errMsgOk e) ∗ mimeErr E err ⊢ errMsgOk err := by
  iintro ⟨#Herrs, #Hm⟩
  iunfold mimeErr at Hm
  icases Hm with (⟨%r, #HE⟩ | %Hp)
  · iapply Herrs $$ HE
  · obtain ⟨msg, rfl⟩ := Hp
    iunfold errMsgOk
    iexists ⟨net.textproto.ProtocolError.ty, #msg⟩
    isplitr
    · ipureintro; rfl
    iapply protocolError_msg

end errs

end net.http
end Perennial
