/-
`jdec_ConfigChangeContext(b, i, p, e)` (jsongen's decoder of a `ConfigChangeContext`, membership's
`json_model_gen.go`) at the JSON of an object `ms` whose members the decoded subset covers in order
from `r` (`membership.ccFold ms r = some r'`), with distinct keys not decoded before (`seen`): `*p`
goes from `r` to `r'` (`membership.ccOwn`), the index after the object; `*e` untouched.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.JsonDecOwn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

open go_etcd_io.etcd.server.v3.etcdserver.api in
/-- See the file header. -/
abbrev membership.jdec_ConfigChangeContext.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (ms : List (List w8 × membership.JVal)) (r r' : membership.CcM) (seen : List GoString)
    (rest : List w8),
  (ms.map Prod.fst).Nodup → (∀ k ∈ ms.map Prod.fst, k ∉ seen) →
  membership.ccFold ms r = some r' →
  bs.drop (uint.nat i) = membership.jobj ms ++ rest →
  {{ (b ↦*{dq} bs ∗ membership.ccOwn p r seen : IProp GF) }}
    (App (App (App (App (Val (@! membership.jdec_ConfigChangeContext)) (Val #b)) (Val #i)) (Val #p))
      (Val #e))
  {{ RET #(W64 ((uint.nat i + (membership.jobj ms).length : Nat) : Int));
      b ↦*{dq} bs ∗ ∃ seen', membership.ccOwn p r' seen' }}

end spec

end EtcdGrove
end Perennial
