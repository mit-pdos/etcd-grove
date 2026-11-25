/-
`jdec_S_string(b, i, p, e)` (jsongen's decoder of a `[]string`, membership's `json_model_gen.go`) at a
URL list's value (`membership.strsOf v = some xs`: an array of plain strings, or `null`) into a nil
slice: `*p` a slice holding `xs` (nil for `null`), the index after the value; `*e` untouched.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.JsonDec
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.membership

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
abbrev membership.jdec_S_string.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc) (v : membership.JVal)
    (xs : List GoString) (rest : List w8),
  membership.strsOf v = some xs →
  bs.drop (uint.nat i) = v.json ++ rest →
  {{ (b ↦*{dq} bs ∗ p ↦ slice.nil : IProp GF) }}
    (App (App (App (App (Val (@! membership.jdec_S_string)) (Val #b)) (Val #i)) (Val #p)) (Val #e))
  {{ RET #(W64 ((uint.nat i + v.json.length : Nat) : Int));
      b ↦*{dq} bs ∗ ∃ s : GoSlice, p ↦ s ∗ s ↦* xs }}

end spec

end EtcdGrove
end Perennial
