/-
`strings.Cut(s, sep)` (Perennial's `strings`, without a body or spec): the text before and after
the first occurrence of `sep` in `s` and `true`, or `s`, `""` and `false` (`cutL`). Stage 7e-3b
(`notes/k8s-7e-3b-plan.md`): the driver's `splitKey` calls it. Taken as a hypothesis by the proofs
that call it; not yet a trust-boundary axiom (to be reviewed with 7e-2's Draft). Lean-first (no
Rocq counterpart).
-/
module

public import Perennial.Code.strings
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- `strings.Cut(s, sep)`: `strings.Index(s, sep)` is the first `i` at which `sep` occurs (`0` for
an empty `sep`); `s[:i]`, `s[i+len(sep):]`, `true`; or `s`, `""`, `false` if there is none. -/
def cutL (s sep : GoString) : GoString × GoString × Bool :=
  match (List.range (s.length + 1)).find? (fun i => sep.isPrefixOf (s.drop i)) with
  | some i => (s.take i, s.drop (i + sep.length), true)
  | none => (s, [], false)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev strings.Cut.spec : Prop :=
  ∀ (s sep : GoString),
  {{ (True : IProp GF) }}
    (App (App (Val #(functions _root_.Perennial.strings.Cut [])) (Val #s)) (Val #sep))
  {{ RET (PairV (PairV #(cutL s sep).1 #(cutL s sep).2.1) #(cutL s sep).2.2); True }}

end spec

end EtcdGrove
end Perennial
