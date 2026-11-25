/-
`jdecMember_ConfigChangeContext(b, i, key, p, e)` (jsongen's decoder of one member of a
`ConfigChangeContext`'s JSON object, membership's `json_model_gen.go`) at a member `key: v` the
decoded subset covers (`membership.ccSet key v r = some r'`: an exact field name, a value of its kind)
and not yet decoded: `*p` goes from `r` to `r'` (`membership.ccOwn`), the index after the value;
`*e` untouched. The value is followed by `,` or `}`.
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
abbrev membership.jdecMember_ConfigChangeContext.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (key : GoString) (p e : Loc)
    (r r' : membership.CcM) (seen : List GoString) (v : membership.JVal) (c : w8)
    (rest : List w8),
  key ∉ seen → membership.ccSet key v r = some r' →
  bs.drop (uint.nat i) = v.json ++ c :: rest → (c = 44#8 ∨ c = 125#8) →
  {{ (b ↦*{dq} bs ∗ membership.ccOwn p r seen : IProp GF) }}
    (App (App (App (App (App (Val (@! membership.jdecMember_ConfigChangeContext)) (Val #b)) (Val #i))
      (Val #key)) (Val #p)) (Val #e))
  {{ RET #(W64 ((uint.nat i + v.json.length : Nat) : Int));
      b ↦*{dq} bs ∗ membership.ccOwn p r' (key :: seen) }}

end spec

end EtcdGrove
end Perennial
