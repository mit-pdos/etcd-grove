/-
`ConfigChangeContext.JSONModelMarshal(v)` at `v` a `ConfigChangeContext`: fresh bytes `ccJson c`, no error.
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
abbrev membership.ConfigChangeContext.JSONModelMarshal.spec : Prop :=
  ∀ (jr c : membership.ConfigChangeContext) (dp dc : DFrac) (ps cs : List GoString),
  {{ (c.Member'.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ c.Member'.Attributes'.ClientURLs' ↦*{dc} cs : IProp GF) }}
    (App (Val (jr @!! membership.ConfigChangeContext.ty @!! go!"JSONModelMarshal"))
      (Val #(interface.mkOk membership.ConfigChangeContext.ty #c)))
  {{ (s : GoSlice), RET (PairV #s #GoInterface.nil);
      s ↦* membership.ccJson c ps cs ∗ ownSliceCap w8 s (DFrac.own 1) ∗
      c.Member'.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ c.Member'.Attributes'.ClientURLs' ↦*{dc} cs }}

end spec

end EtcdGrove
end Perennial
