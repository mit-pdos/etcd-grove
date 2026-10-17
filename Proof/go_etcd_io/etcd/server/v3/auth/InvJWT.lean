/-
**The JWT token provider** (`server/v3/auth/jwt.go`, PR etcd#21909): the vocabulary of the proof of
`tokenJWT.info`. Lean-first (no Rocq counterpart).

**The provider** (`jwtProviderRO t vo`): what `info` reads of the `*tokenJWT` `t`, all fixed
since `newTokenProviderJWT` built it (not translated: an assumption about the constructor, as
the store's `authInv` is about `NewAuthStore`'s): its logger (not nil), `signMethod` and `key`
(which the key function `keyFunc` reads) and `verifyOnly`, `vo` (set when the options give a
public key and no private key).

**What `info` returns** (`jwtInfoOk vo rev a ok`): `(nil, false)`, or `(a, true)` with an auth
info `a` (`authInfoRO a`, not nil) whose `Revision` is `rev`, the store's revision `info` was
passed, when the provider is verify-only. That is the PR's change: before it, `info` returned the
token's `revision` claim in every case.

**Trust boundary** (`wp_convert_float64_uint64`): Go's conversion `uint64(f)` of a `float64` `f`
returns (some `uint64`; the value is implementation-defined when `f` is out of range, but the
conversion never panics). Perennial's model has no step for a float-to-integer conversion (its
floats are opaque bit patterns, `FloatOps`), so the proof of `info` assumes this one, here; the
general fix (the conversions in `FloatOps`, uninterpreted like `int64ToFloat64`) belongs in
Perennial (`notes/STATUS.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section fields
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&t.<f>` (a `*tokenJWT`) -/
abbrev jF (f : GoString) (t : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.auth.tokenJWT f t

end fields

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The JWT provider** `t` (persistent): not nil, its logger (not nil), `signMethod`, `key` and
`verifyOnly` (`vo`) read-only. -/
def jwtProviderRO (t : Loc) (vo : Bool) : IProp GF :=
  iprop(⌜t ≠ null⌝ ∗ (∃ lg : Loc, jF go!"lg" t ↦□ lg ∗ ⌜lg ≠ null⌝) ∗
    (∃ sm : GoInterface, jF go!"signMethod" t ↦□ sm) ∗ (∃ k : GoInterface, jF go!"key" t ↦□ k) ∗
    jF go!"verifyOnly" t ↦□ vo)

instance jwtProviderRO_persistent (t : Loc) (vo : Bool) :
    Persistent (jwtProviderRO (GF := GF) t vo) := by
  unfold jwtProviderRO; infer_instance

/-- **What `info` returns**: `(nil, false)`, or `(a, true)` with `a` not nil, its `Revision` the
store's `rev` when the provider is verify-only. -/
def jwtInfoOk (vo : Bool) (rev : w64) (a : Loc) (ok : Bool) : IProp GF :=
  iprop(⌜ok = false ∧ a = null⌝ ∨
    (⌜ok = true ∧ a ≠ null⌝ ∗ (⌜vo = false⌝ ∨ aiF go!"Revision" a ↦□ rev)))

instance jwtInfoOk_persistent (vo : Bool) (rev : w64) (a : Loc) (ok : Bool) :
    Persistent (jwtInfoOk (GF := GF) vo rev a ok) := by
  unfold jwtInfoOk; infer_instance

/-- **Trust boundary**: `uint64(f)` of a `float64` returns (see the file header). -/
axiom wp_convert_float64_uint64 (f : w64) :
  {{ (True : IProp GF) }}
    (App (Val (GoInstruction (Convert go.float64 go.uint64))) (Val #f))
  {{ (r : w64), RET #r; True }}

end defs

end auth
end EtcdGrove
end Perennial
