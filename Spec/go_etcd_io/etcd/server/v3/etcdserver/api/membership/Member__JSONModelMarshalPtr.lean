/-
`(*Member).JSONModelMarshalPtr(v)` at `v` a non-nil `*Member` (the encoding/json model's per-type
route): fresh bytes `memberJson` of the pointee, no error.
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
abbrev membership.Member.JSONModelMarshalPtr.spec : Prop :=
  ∀ (jr l : Loc) (q : DFrac) (m : membership.Member) (dp dc : DFrac) (ps cs : List GoString),
  {{ (l ↦{q} m ∗ m.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ m.Attributes'.ClientURLs' ↦*{dc} cs : IProp GF) }}
    (App (Val (jr @!! go.GoType.PointerType membership.Member.ty @!! go!"JSONModelMarshalPtr"))
      (Val #(interface.mkOk (go.GoType.PointerType membership.Member.ty) #l)))
  {{ (s : GoSlice), RET (PairV #s #GoInterface.nil);
      s ↦* membership.memberJson m ps cs ∗ ownSliceCap w8 s (DFrac.own 1) ∗ l ↦{q} m ∗
      m.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ m.Attributes'.ClientURLs' ↦*{dc} cs }}

end spec

end EtcdGrove
end Perennial
