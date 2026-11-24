/-
`jenc_ConfigChangeContext(b, v, d)` (jsongen's encoder of a `ConfigChangeContext`), at a small depth:
`b` with `ccJson v` after it, no error.
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
abbrev membership.jenc_ConfigChangeContext.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (c : membership.ConfigChangeContext) (dp dc : DFrac)
    (ps cs : List GoString) (d : w64),
  uint.Z d < 999 →
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) ∗
      c.Member'.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ c.Member'.Attributes'.ClientURLs' ↦*{dc} cs : IProp GF) }}
    (App (App (App (Val (@! membership.jenc_ConfigChangeContext)) (Val #b)) (Val #c)) (Val #d))
  {{ (b' : GoSlice), RET (PairV #b' #GoInterface.nil);
      b' ↦* (bs ++ membership.ccJson c ps cs) ∗ ownSliceCap w8 b' (DFrac.own 1) ∗
      c.Member'.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ c.Member'.Attributes'.ClientURLs' ↦*{dc} cs }}

end spec

end EtcdGrove
end Perennial
