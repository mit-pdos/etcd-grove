/-
`strconv.ParseInt(s, base, bitSize)` (names-only in Perennial): the integer `s` spells, or an
error. The spec says it returns some integer and error (for client-go's store, whose resource
version metric parses it, `parseRVForMetricsWithTruncation`), and, since 2026-11-04 (K2 of
`notes/k8s-compactor-plan.md`, U2, the user's approval), that it reads back what `FormatInt` writes:
on `fmtInt m 10` at base 10 and bit size 64 it returns `m` and no error (Go: `ParseInt` accepts an
optional sign and decimal digits, and every `int64`'s decimal form fits 64 bits). Proved
(`Proof/strconv/ParseInt.lean`) over Perennial's translation of Go's (stdlib2, 2026-11-21; until then
a trust-boundary axiom), which reads package variables (its errors) and is specified for a base in
`2..36` and a bit size in `0..64`: hence the package's `isPkgInit` and those premises, which the
callers (all at base 10 and bit size 64) discharge. Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.strconv.Base
public import Proof.strconv.FormatIntDefs
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev strconv.ParseInt.spec : Prop :=
  ∀ (s : GoString) (base bitSize : w64),
  2 ≤ sint.Z base → sint.Z base ≤ 36 → 0 ≤ sint.Z bitSize → sint.Z bitSize ≤ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
    (App (App (App (Val (@! strconv.ParseInt)) (Val #s)) (Val #base)) (Val #bitSize))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ⌜∀ m : w64, s = fmtInt m (W64 10) → base = W64 10 → bitSize = W64 64 →
        n = m ∧ err = GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
