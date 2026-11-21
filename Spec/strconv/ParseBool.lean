/-
`strconv.ParseBool(str)`: the boolean `str` spells, or an error; the spec says it returns some
boolean and error. Proved (`Proof/strconv/ParseBool.lean`) over Perennial's translation of Go's
(2026-11-20; until then a trust-boundary axiom, with no premise): on an error it reads `strconv`'s
`ErrSyntax`, so it needs `strconv`'s `isPkgInit` (the initializer that calls it has it). Lean-first
(no Rocq counterpart).
-/
module

public import Perennial.Code.strconv
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
abbrev strconv.ParseBool.spec : Prop :=
  ∀ (str : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
    (App (Val (@! strconv.ParseBool)) (Val #str))
  {{ (b : Bool) (err : GoInterface), RET (PairV #b #err); True }}

end spec

end EtcdGrove
end Perennial
