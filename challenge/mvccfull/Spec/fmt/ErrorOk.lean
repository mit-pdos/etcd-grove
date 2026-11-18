/-
`fmtErrorOk err`: `err` is an error value Go's `fmt` formats by calling its `Error()`, needing
nothing. A `fmt`-level predicate shared by the specs of loggers and formatters (first used by
bbolt's logger contract, `Spec/go_etcd_io/bbolt/Logger.lean`), beside `fmt.argOk`
(`Spec/fmt/Errorf.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.fmt.Base
public import Spec.fmt.Errorf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The signature `() string` of `Error` and `String`, as goose writes it in method sets. -/
def noArgStringSig : go.signature := go.signature.Signature [] false [go.string]

/-- **`err` is an error value `fmt` formats by calling its `Error()`, needing nothing** (round 8,
review 7 M4: the shared `fmt`-level predicate; it belongs in the repository's `Spec/fmt/`, beside
`fmt.argOk`). Its dynamic type has `Error() string` (Go's `case error`, by signature) and no
`Format`, and `Error()` returns some string needing nothing, persistently. Producers: a law for
`errors.New`'s `*errorString` (`errors.wp_New_errorString`, whose type facts are goose's method
sets); `fmt.Errorf.spec`'s post, restated to give it (`*fmt.wrapError`/`*errorString`); the
OsFs-backed `os`/`syscall`/`unix` specs' error posts (`*fs.PathError`, `syscall.Errno`), once
their `Error` methods are translated (D20' infrastructure). Persistent. -/
def fmtErrorOk : GoInterface → IProp GF
  | .nil => iprop(False)
  | .ok ii => iprop(⌜methodSet ii.ty !! go!"Format" = none ∧
      methodSet ii.ty !! go!"Error" = some noArgStringSig⌝ ∗ fmt.stringMethodSpec ii go!"Error")

end defs

end EtcdGrove
end Perennial
