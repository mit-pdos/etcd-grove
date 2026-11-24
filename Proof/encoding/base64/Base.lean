/-
Lean-first (no Rocq counterpart).

The package initialization instance of the standard library's `encoding/base64` (Perennial does
not translate it; the k8s-apiserver project's `Code/encoding/base64.toml` translates the types and,
with their bodies, what the initializer and `EncodeToString` run), and the one thing the proofs read of it: `StdEncoding`
(`base64.go`, `NewEncoding(encodeStd)`) holds a fixed `*Encoding` whose `EncodeToString` returns
the standard base64 encoding `stdEnc` of its argument's bytes (the auth plan's E2x, 2026-10-26:
`EtcdServer.UserAdd` and `UserChangePassword` put a password's hash in their request
`base64.StdEncoding.EncodeToString`-encoded). Stated as the method call's own WP on the loaded
pointer. Until 2026-11-20 the fact was the trust-boundary axiom `StdEncoding_init` and `stdEnc` was
opaque; now the package's initializer and `EncodeToString` are translated with their bodies
(`Code/encoding/base64.toml`) and proved (`Proof/encoding/base64/`), and `stdEnc` is base64
(`b64Enc`) over the standard alphabet. Until 2026-10-26 the instance (fact `True`) was in
`k8s_io/apiserver/pkg/storage/etcd3/Base.lean`. Restated in stage 7e-2 (`notes/k8s-7e-2-draft.md`
§5.4, attacked T15): also `RawURLEncoding` (`storage.EncodeContinue`'s continue token), whose
`EncodeToString` returns `rawUrlEnc` of its argument's bytes; the fact is the two parts,
`stdEncInit` and `rawUrlEncInit`.
-/
module

public import GeneratedProof.encoding.base64
public import Proof.internal.byteorder.Base
public import Perennial.Proof.strconv.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace encoding.base64

open Iris Iris.BI

/-- **Base64** (RFC 4648 §4) of a byte string over the 64-symbol alphabet `alpha`: each 3-byte
group becomes the 4 symbols of its four 6-bit pieces, most significant first; a final group of 1
or 2 bytes becomes 2 or 3 symbols (its bits padded with zeros on the right), followed by 2 or 1
copies of the padding byte `pad` when there is one (`none`: no padding, `NoPadding`). -/
def b64Enc (alpha : List w8) (pad : Option w8) : List w8 → List w8
  | b0 :: b1 :: b2 :: rest =>
    alpha.getD (b0 >>> 2).toNat 0 :: alpha.getD (((b0 &&& 3) <<< 4) ||| (b1 >>> 4)).toNat 0 ::
      alpha.getD (((b1 &&& 15) <<< 2) ||| (b2 >>> 6)).toNat 0 :: alpha.getD (b2 &&& 63).toNat 0 ::
      b64Enc alpha pad rest
  | [b0, b1] =>
    [alpha.getD (b0 >>> 2).toNat 0, alpha.getD (((b0 &&& 3) <<< 4) ||| (b1 >>> 4)).toNat 0,
      alpha.getD ((b1 &&& 15) <<< 2).toNat 0] ++ pad.toList
  | [b0] => [alpha.getD (b0 >>> 2).toNat 0, alpha.getD ((b0 &&& 3) <<< 4).toNat 0] ++ pad.toList ++ pad.toList
  | [] => []

/-- `StdEncoding`'s alphabet (`base64.go`'s `NewEncoding` argument). -/
def stdAlphabet : GoString := go!"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

/-- `URLEncoding`'s alphabet. -/
def urlAlphabet : GoString := go!"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"

/-- **base64's standard encoding** (`StdEncoding.EncodeToString`, RFC 4648 with padding `=`) of a
byte string. (Opaque until 2026-11-20, when the package's initializer and `EncodeToString` were
proved over the real code, `Proof/encoding/base64/`.) -/
def stdEnc (d : List w8) : GoString := b64Enc stdAlphabet (some 61) d

/-- **base64's URL encoding without padding** (`RawURLEncoding.EncodeToString`) of a byte
string. -/
def rawUrlEnc (d : List w8) : GoString := b64Enc urlAlphabet none d

/-- **base64's standard encoding without padding** (`RawStdEncoding.EncodeToString`) of a byte
string (phase 7 S2 core, 2026-11-23: grpc's `encodeBinHeader`). -/
def rawStdEnc (d : List w8) : GoString := b64Enc stdAlphabet none d

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`encoding/base64`'s fact, `StdEncoding`'s part**: `StdEncoding` holds a fixed pointer `e` (Go
never writes the variable after initialization), on which `EncodeToString(src)` returns `stdEnc` of
`src`'s bytes, reading and keeping the slice (`(*Encoding).EncodeToString`:
`make([]byte, enc.EncodedLen(len(src)))`, `enc.Encode(buf, src)`, `string(buf)`; no panic, no write
to `src`). -/
abbrev stdEncInit : IProp GF :=
  iprop(∃ e : Loc, globalAddr StdEncoding ↦□ e ∗
    □ ∀ (sl : GoSlice) (dq : DFrac) (d : List w8) (Φ : val → IProp GF),
      sl ↦*{dq} d -∗ ▷ (sl ↦*{dq} d -∗ Φ #(stdEnc d)) -∗
      WP (App (Val #(methods (go.GoType.PointerType Encoding.ty) go!"EncodeToString" #e)) (Val #sl))
        {{ Φ }})

/-- **`encoding/base64`'s fact, `RawURLEncoding`'s part** (stage 7e-2): `RawURLEncoding =
URLEncoding.WithPadding(NoPadding)` holds a fixed pointer, on which `EncodeToString(src)` returns
`rawUrlEnc` of `src`'s bytes, reading and keeping the slice. -/
abbrev rawUrlEncInit : IProp GF :=
  iprop(∃ e : Loc, globalAddr RawURLEncoding ↦□ e ∗
    □ ∀ (sl : GoSlice) (dq : DFrac) (d : List w8) (Φ : val → IProp GF),
      sl ↦*{dq} d -∗ ▷ (sl ↦*{dq} d -∗ Φ #(rawUrlEnc d)) -∗
      WP (App (Val #(methods (go.GoType.PointerType Encoding.ty) go!"EncodeToString" #e)) (Val #sl))
        {{ Φ }})

/-- **`encoding/base64`'s fact, `StdEncoding`'s decoder** (prove-authcrypto, 2026-11-21; the auth
store's `selectPassword`): on `StdEncoding`'s fixed pointer, `DecodeString(s)` returns a fresh slice
and an error, the error `nil` when `s` is the standard encoding `stdEnc` of some bytes
(`(*Encoding).DecodeString`: `make([]byte, enc.DecodedLen(len(s)))`, `enc.Decode(dbuf, []byte(s))`,
`dbuf[:n]`; no panic on any input). -/
abbrev stdDecInit : IProp GF :=
  iprop(∃ e : Loc, globalAddr StdEncoding ↦□ e ∗
    □ ∀ (s : GoString) (Φ : val → IProp GF),
      ▷ (∀ (b : GoSlice) (err : GoInterface) (bs : List w8), b ↦* bs -∗
          ⌜(∃ x : List w8, s = stdEnc x) → err = GoInterface.nil⌝ -∗ Φ (PairV #b #err)) -∗
      WP (App (Val #(methods (go.GoType.PointerType Encoding.ty) go!"DecodeString" #e)) (Val #s))
        {{ Φ }})

/-- **`encoding/base64`'s fact**: the three parts. -/
abbrev base64Init : IProp GF := iprop(stdEncInit ∗ rawUrlEncInit ∗ stdDecInit)

instance encoding_base64_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.encoding.base64 :=
  define_is_pkg_init base64Init
instance encoding_base64_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.encoding.base64 :=
  build_get_is_pkg_init_wf

/-- The fact, from the package's `isPkgInit`. -/
theorem base64Init_access :
    isPkgInit (PROP := IProp GF) pkg_id.encoding.base64 ⊢ base64Init (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.encoding.base64

theorem stdEncInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.encoding.base64 ⊢ stdEncInit (GF := GF) := by
  iintro #H
  ihave ⟨#H1, -⟩ := base64Init_access $$ H
  iexact H1

theorem rawUrlEncInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.encoding.base64 ⊢ rawUrlEncInit (GF := GF) := by
  iintro #H
  ihave ⟨-, #H2, -⟩ := base64Init_access $$ H
  iexact H2

theorem stdDecInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.encoding.base64 ⊢ stdDecInit (GF := GF) := by
  iintro #H
  ihave ⟨-, -, #H3⟩ := base64Init_access $$ H
  iexact H3

end init

end encoding.base64
end Perennial
