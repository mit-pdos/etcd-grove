/-
`jenc_S_string(b, v, d)` (jsongen's encoder of a `[]string`, membership's `json_model_gen.go`), below the
cycle-detection depth: `b` with `null` (a nil `v`) or the JSON array of `v`'s strings after it, no error.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Json
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
abbrev membership.jenc_S_string.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (v : GoSlice) (dq : DFrac) (xs : List GoString) (d : w64),
  uint.Z d < 1000 →
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ v ↦*{dq} xs : IProp GF) }}
    (App (App (App (Val (@! membership.jenc_S_string)) (Val #b)) (Val #v)) (Val #d))
  {{ (b' : GoSlice), RET (PairV #b' #GoInterface.nil);
      b' ↦* (bs ++ membership.jsonStrSlice (decide (v = slice.nil)) xs) ∗
      ownSliceCap w8 b' (DFrac.own 1) ∗ v ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
