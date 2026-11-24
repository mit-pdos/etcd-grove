/-
The vocabulary of the net/http model's specs (`Net/Spec/net/http/`; the model `models/net/http`,
translated by project models-net), for `ReadResponse` on net/rpc's `CONNECT` answer (2026-11-23):

* `httpEnv` (persistent): the package state the parse reads: `bufio`'s, `io`'s, `fmt`'s (the
  `badStringError`s) and `strconv`'s (`Atoi`) initialization, httpguts' token table (`tokenTable`,
  `ValidHeaderFieldName`'s), `strings`' initialization (`ParseHTTPVersion`'s `HasPrefix`), net/http's
  `errTooLarge` (an `errors.New` error, `readRequestLimit`'s) and `NoBody` (the body of a response with
  none). net/http has no package initialization proof yet
  (`notes/dsverify-net-port-plan.md`, phase 5 item 2, 5): a client takes `httpEnv` as a premise.
* `cutByte s c`, `trimLeftByte s c`: what the model's `modelCutByte` and `modelTrimLeftByte` return
  (`strings.Cut(s, string(c))`, `strings.TrimLeft(s, string(c))`, `textproto_model.go`).
* `fieldByte c`: `c` may be in a header field name (textproto's `validHeaderFieldByte`, RFC 7230's
  `tchar`); `canonQuick s`: textproto's `CanonicalMIMEHeaderKey`'s quick check accepts `s` as it is
  (it returns `s` without canonicalizing it: a byte that is no `tchar`, or every letter upper case
  at the start and after each `-` and lower case elsewhere).
* `statusLine`: the status line of net/rpc's answer (`connectAns` without its two `"\n"`);
  `badStatusLine`, `badHdr`: the status line and the header lines of net/http's `400` answer
  (`net.rpc.badReqAns`).
* Header blocks (`modelReadMIMEHeader`): `HdrLine`, a header line's name and value; `hdrLineOk kv`,
  a line the model reads as it is (the name a canonical token, `canonQuick`; the value printable
  ASCII, `valByte`, without a space at its ends); `hdrBlockOk hb`, lines with distinct names, each
  `hdrLineOk`; `hdrWire hb eol`, the block's bytes: each line `k: v\r\n`, then the empty line
  `eol ++ "\n"` (`eol` `""` or `"\r"`); `hdrOwn m hb`, the map `m` the model built of the block
  (each name to the one-value slice of its value); `hdrVals ms k`, the values of `k`'s slice in the
  header map `ms`, if it has one (what `shouldClose` reads of `"Connection"`); `mimeErr E err`, the
  errors `modelReadMIMEHeader` returns (the stream's or a `textproto.ProtocolError`, whose message
  starts with `"malformed MIME header"`).
-/
module

public import Net.GeneratedProof.net.http
public import Net.Proof.net.rpc.Proto
public import Proof.bufio.Defs
public import Perennial.Proof.fmt
public import Perennial.Proof.strconv
public import Perennial.Proof.internal.stringslite.Base
public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section pure

/-- See the file header. -/
def cutByte (s : List w8) (c : w8) : List w8 × List w8 × Bool :=
  match s.findIdx? (· = c) with
  | some i => (s.take i, s.drop (i + 1), true)
  | none => (s, [], false)

/-- See the file header. -/
def trimLeftByte (s : List w8) (c : w8) : List w8 := s.dropWhile (· = c)

/-- `strings.Cut(s, string(c))` is `cutByte s c`. -/
theorem cut_single (s : List w8) (c : w8) : internal.stringslite.cut s [c] = cutByte s c := by
  unfold internal.stringslite.cut cutByte
  rcases internal.bytealg.index_cases s [c] with ⟨i, hi, hp, hmin⟩ | ⟨hi, hn⟩
  · have hf : s.findIdx? (· = c) = some i := by
      rw [List.findIdx?_eq_some_iff_getElem]
      have hp' := (internal.bytealg.singleton_prefix_drop s c i).1 hp
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 hp'
      refine ⟨hlt, by simpa using heq, fun j hj => ?_⟩
      have := hmin j hj
      rw [internal.bytealg.singleton_prefix_drop, List.getElem?_eq_getElem (by omega)] at this
      simpa using this
    rw [hi, hf]; simp
  · have hf : s.findIdx? (· = c) = none := by
      rw [List.findIdx?_eq_none_iff]
      intro x hx
      simp only [decide_eq_false_iff_not]
      intro hxc
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      apply hn j
      rw [internal.bytealg.singleton_prefix_drop, List.getElem?_eq_getElem hj]
      simpa using hxc
    rw [hi, hf]; simp

/-- `strings.TrimLeft(s, string(c))` is `trimLeftByte s c`. -/
theorem trimLeft_single (s : List w8) (c : w8) :
    strings.trimLeft s [c] = trimLeftByte s c := by
  unfold strings.trimLeft trimLeftByte
  congr 1
  funext b
  simp

/-- See the file header (RFC 7230's `tchar`). -/
def fieldByte (c : w8) : Bool :=
  decide ((48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨
  (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
  c ∈ [W8 33, W8 35, W8 36, W8 37, W8 38, W8 39, W8 42, W8 43, W8 45, W8 46, W8 94, W8 95,
    W8 96, W8 124, W8 126])

/-- `CanonicalMIMEHeaderKey`'s quick check from the rest `s`, `upper` whether the next letter
should be upper case. -/
def canonQuickFrom : List w8 → Bool → Bool
  | [], _ => true
  | c :: s, upper =>
    if fieldByte c = false then true
    else if upper = true ∧ 97 ≤ c.toNat ∧ c.toNat ≤ 122 then false
    else if upper = false ∧ 65 ≤ c.toNat ∧ c.toNat ≤ 90 then false
    else canonQuickFrom s (decide (c = W8 45))

/-- See the file header. -/
def canonQuick (s : List w8) : Bool := canonQuickFrom s true

/-- A line without its `"\r"` before the `"\n"` (`modelReadLine`). -/
def dropCR (l : List w8) : List w8 :=
  if l.getLast? = some (W8 13) then l.dropLast else l

/-- See the file header. -/
def statusLine : List w8 := go!"HTTP/1.0 200 Connected to Go RPC"

theorem connectAns_eq : net.rpc.connectAns = statusLine ++ [W8 10, W8 10] := by decide

/-- See the file header. -/
abbrev HdrLine := List w8 × List w8

/-- A header value's byte the model reads as it is: printable ASCII or a space. -/
def valByte (c : w8) : Bool := decide (32 ≤ c.toNat ∧ c.toNat ≤ 126)

/-- See the file header. -/
def hdrLineOk (kv : HdrLine) : Prop :=
  kv.1 ≠ [] ∧ kv.1.all fieldByte = true ∧ canonQuick kv.1 = true ∧ kv.2.all valByte = true ∧
    kv.2.head? ≠ some (W8 32) ∧ kv.2.getLast? ≠ some (W8 32)

instance (kv : HdrLine) : Decidable (hdrLineOk kv) := by unfold hdrLineOk; infer_instance

/-- See the file header. -/
def hdrBlockOk (hb : List HdrLine) : Prop :=
  (hb.map Prod.fst).Nodup ∧ ∀ kv ∈ hb, hdrLineOk kv

instance (hb : List HdrLine) : Decidable (hdrBlockOk hb) := by unfold hdrBlockOk; infer_instance

/-- A header line's bytes: `k: v\r\n`. -/
def hdrLineWire (kv : HdrLine) : List w8 := kv.1 ++ [W8 58, W8 32] ++ kv.2 ++ [W8 13, W8 10]

/-- See the file header. -/
def hdrWire (hb : List HdrLine) (eol : List w8) : List w8 :=
  hb.flatMap hdrLineWire ++ eol ++ [W8 10]

/-- See the file header. -/
def badStatusLine : List w8 := go!"HTTP/1.1 400 Bad Request"

/-- See the file header. -/
def badHdr : List HdrLine :=
  [(go!"Content-Type", go!"text/plain; charset=utf-8"), (go!"Connection", go!"close")]

theorem badHdr_ok : hdrBlockOk badHdr := by decide

theorem badReqAns_eq : net.rpc.badReqAns =
    badStatusLine ++ [W8 13, W8 10] ++ hdrWire badHdr [W8 13] ++ go!"400 Bad Request" := by decide

end pure

end net.http

namespace vendor.golang_org.x.net.http.httpguts

section env
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- httpguts' `isTokenTable` holds, for each byte `c`, whether it is RFC 7230's `tchar`
(`net.http.fieldByte c`), as its initializer (an array literal, translated) sets it; nothing writes
it after (persistent). httpguts has no package initialization proof yet: part of net/http's
`httpEnv`, a premise. -/
def tokenTable : IProp GF :=
  iprop(∃ t : GoArray Bool 256, globalAddr vendor.golang_org.x.net.http.httpguts.isTokenTable ↦□ t ∗
    ⌜∀ c : w8, t.arr[c.toNat]? = some (net.http.fieldByte c)⌝)

instance tokenTable_persistent : Persistent (tokenTable (GF := GF)) := by
  unfold tokenTable; infer_instance

end env

end vendor.golang_org.x.net.http.httpguts

namespace net.http

section env
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def httpEnv : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
    isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ isPkgInit (PROP := IProp GF) pkg_id.strconv ∗
    (vendor.golang_org.x.net.http.httpguts.tokenTable ∗ isPkgInit (PROP := IProp GF) pkg_id.strings ∗
      ∃ l : Loc, globalAddr net.http.errTooLarge ↦□
        interface.mkOk (go.GoType.PointerType errors.errorString.ty) #l) ∗
    ∃ nb : net.http.noBody, globalAddr net.http.NoBody ↦□ nb)

theorem httpEnv_tokenTable : httpEnv (GF := GF) ⊢ vendor.golang_org.x.net.http.httpguts.tokenTable := by
  iintro H
  iunfold httpEnv at H
  icases H with ⟨-, -, -, -, ⟨#Ht, -⟩, -⟩
  iexact Ht

theorem httpEnv_strings : httpEnv (GF := GF) ⊢ isPkgInit (PROP := IProp GF) pkg_id.strings := by
  iintro H
  iunfold httpEnv at H
  icases H with ⟨-, -, -, -, ⟨-, #Hs, -⟩, -⟩
  iexact Hs

instance httpEnv_persistent : Persistent (httpEnv (GF := GF)) := by
  unfold httpEnv; infer_instance

end env

section req
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- A request `rqv` as `readTransfer` leaves one without a body: `Body` `NoBody` (`nb`, its value),
`ContentLength` `0`, `Trailer` `nil`. -/
def reqNoBody (rqv : net.http.Request) (nb : net.http.noBody) : net.http.Request :=
  { rqv with Body' := interface.mkOk net.http.noBody.ty #nb, ContentLength' := W64 0,
             Trailer' := map.nil }

end req

section hdr
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def hdrOwn (m : Loc) (hb : List HdrLine) : IProp GF :=
  iprop(∃ ms : GMap GoString GoSlice, m ↦$ ms ∗
    ⌜∀ k, (ms !! k).isSome = decide (k ∈ hb.map Prod.fst)⌝ ∗
    [∗list] kv ∈ hb, ∃ s : GoSlice, ⌜ms !! kv.1 = some s⌝ ∗ s ↦* ([kv.2] : List GoString))

/-- See the file header. -/
def hdrVals (ms : GMap GoString GoSlice) (k : GoString) : IProp GF :=
  match ms !! k with
  | none => iprop(True)
  | some s => iprop(∃ vs : List GoString, s ↦* vs)

/-- The errors `modelReadMIMEHeader` returns: the stream's (with `E`'s evidence at some position)
or a `textproto.ProtocolError` (a malformed line, or one cut by the stream's error), whose message
starts with `"malformed MIME header"`. -/
def mimeErr (E : List w8 → GoInterface → IProp GF) (err : GoInterface) : IProp GF :=
  iprop((∃ r : List w8, □ E r err) ∨
    ⌜∃ msg : GoString, err = interface.mkOk net.textproto.ProtocolError.ty #msg ∧
      go!"malformed MIME header" <+: msg⌝)

instance mimeErr_persistent (E : List w8 → GoInterface → IProp GF) (err : GoInterface) :
    Persistent (mimeErr E err) := by
  unfold mimeErr; infer_instance

end hdr

section tokens

/-- What the model's `modelIndexByte s c` (`strings.IndexByte`) returns: the index of the first `c`
in `s`, or `-1`. -/
def idxByte (s : List w8) (c : w8) : w64 :=
  match s.findIdx? (· = c) with
  | some i => W64 (i : Int)
  | none => W64 (-1)

/-- What the model's `modelLowerASCII b` (httpguts' `lowerASCII`) returns. -/
def lowerASCII (b : w8) : w8 := if W8 65 ≤ b ∧ b ≤ W8 90 then b + W8 32 else b

/-- A space or a tab (httpguts' `isOWS`). -/
def isOWS (b : w8) : Bool := decide (b = W8 32) || decide (b = W8 9)

/-- What the model's `modelTrimOWS x` (httpguts' `trimOWS`) returns: `x` without the spaces and tabs
at its ends. -/
def trimOWS (s : List w8) : List w8 := ((s.dropWhile isOWS).reverse.dropWhile isOWS).reverse

end tokens

end net.http
end Perennial
