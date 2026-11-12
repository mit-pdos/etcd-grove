/-
`strconv.ParseBool(str)` (names-only in Perennial): the boolean `str` spells, or an error; the
spec says it returns some boolean and error. The trust boundary: an axiom, `Proof/strconv/ParseBool.lean`. Lean-first (no Rocq
counterpart).
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
  {{ (True : IProp GF) }}
    (App (Val (@! strconv.ParseBool)) (Val #str))
  {{ (b : Bool) (err : GoInterface), RET (PairV #b #err); True }}

end spec

end EtcdGrove
end Perennial
