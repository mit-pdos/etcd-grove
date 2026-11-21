/-
`strings.ToLower(s)` (names-only in Perennial: `notes/perennial-changes.md`, "strings.ToLower has no
spec"): the spec says that it returns, without panicking, a string, and (etcdstorage, 2026-11-20)
when that string is a given ASCII word with no upper-case letter: exactly when `s` lower-cases to it
rune by rune (`strings.lowersTo`, `Proof/strings/Lower.lean`, whose header gives Go's rule and the
measurement; `notes/axiom-review/getenv-etcd-verify.md`). The trust boundary: an
axiom, `Proof/strings/ToLower.lean`. True of Go: `ToLower` is total on every string (an ASCII
fast path, else `strings.Map(unicode.ToLower, s)`, which decodes the string rune by rune, an invalid
UTF-8 byte as `utf8.RuneError`, and builds the result with a `strings.Builder`); it has no panic of
its own, and its only failure is running out of memory, which the model does not consider anywhere. Needed by bbolt's `internal/common.Verify`
(`getEnvVerify`, `IsVerificationEnabled`). Stated for any `hlc`, like `os.Getenv`'s, so that bbolt's
specs can call it. Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.strings.Base
public import Proof.strings.Lower

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev strings.ToLower.spec : Prop :=
  ∀ (s : GoString),
  {{ (True : IProp GF) }}
    (App (Val (@! strings.ToLower)) (Val #s))
  {{ (r : GoString), RET #r;
      ⌜∀ w : GoString, strings.lowerWord w → (r = w ↔ strings.lowersTo s w = true)⌝ }}

end spec

end EtcdGrove
end Perennial
