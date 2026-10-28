/-
Lean-first (no Rocq counterpart).

The package initialization instance of the standard library's `encoding/base64` (names only:
Perennial does not translate it, `notes/perennial-changes.md`; the k8s-apiserver project's
`Code/encoding/base64.toml`), and the one thing the proofs read of it: `StdEncoding`
(`base64.go`, `NewEncoding(encodeStd)`) holds a fixed `*Encoding` whose `EncodeToString` returns
the standard base64 encoding `stdEnc` of its argument's bytes (the auth plan's E2x, 2026-10-26:
`EtcdServer.UserAdd` and `UserChangePassword` put a password's hash in their request
`base64.StdEncoding.EncodeToString`-encoded). Stated as the method call's own WP on the loaded
pointer, since `Encoding` is an axiomatized type (its methods are not even named). The fact is
established by the trust-boundary axiom `StdEncoding_init` (`Proof/encoding/base64/Init.lean`,
`etc/gen-init.py`). Until 2026-10-26 the instance (fact `True`) was in
`k8s_io/apiserver/pkg/storage/etcd3/Base.lean`.
-/
module

public import GeneratedProof.encoding.base64

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace encoding.base64

open Iris Iris.BI

/-- **base64's standard encoding** (`StdEncoding.EncodeToString`, RFC 4648 with padding) of a
byte string. Opaque: what the proofs need is only that `selectPassword`'s decoding of such an
encoding has no error (its trust boundary, the auth plan's E2u), not the encoding itself. -/
opaque stdEnc : List w8 → GoString

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`encoding/base64`'s fact**: `StdEncoding` holds a fixed pointer `e` (Go never writes the
variable after initialization), on which `EncodeToString(src)` returns `stdEnc` of `src`'s bytes,
reading and keeping the slice (`(*Encoding).EncodeToString`: `make([]byte, enc.EncodedLen(len(src)))`,
`enc.Encode(buf, src)`, `string(buf)`; no panic, no write to `src`). -/
abbrev base64Init : IProp GF :=
  iprop(∃ e : Loc, globalAddr StdEncoding ↦□ e ∗
    □ ∀ (sl : GoSlice) (dq : DFrac) (d : List w8) (Φ : val → IProp GF),
      sl ↦*{dq} d -∗ ▷ (sl ↦*{dq} d -∗ Φ #(stdEnc d)) -∗
      WP (App (Val #(methods (go.GoType.PointerType Encoding.ty) go!"EncodeToString" #e)) (Val #sl))
        {{ Φ }})

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

end init

end encoding.base64
end Perennial
