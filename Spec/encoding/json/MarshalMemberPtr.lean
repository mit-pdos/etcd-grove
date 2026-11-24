/-
`json.Marshal` of a `*membership.Member` (boxed in `any`): `bootstrapRaftFromCluster`'s
`json.Marshal((*cl).Member(id))` (`bootstrap.go:553` at the etcd pin `edc800c6f`; claim #34 stage 4,
2026-11-25). No error; the fresh bytes `membership.memberJson m ps cs` of the pointee (the encoding/json
model's dispatch to the generated `JSONModelMarshalPtr`), the record and its URL slices read at any
fraction and given back. Proved as `MarshalMember.lean`'s value case
(`Proof/encoding/json/MarshalMemberPtr.lean`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Json

@[expose] public section

set_option linter.unusedSectionVars false

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
abbrev encoding.json.MarshalMemberPtr.spec : Prop :=
  ∀ (l : Loc) (q : DFrac) (m : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member)
    (dp dc : DFrac) (ps cs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ l ↦{q} m ∗
      m.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ m.Attributes'.ClientURLs' ↦*{dc} cs }}
    (App (Val (@! _root_.Perennial.encoding.json.Marshal))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member.ty) #l)))
  {{ (sl : GoSlice), RET (PairV #sl #GoInterface.nil);
      l ↦{q} m ∗ m.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ m.Attributes'.ClientURLs' ↦*{dc} cs ∗
      sl ↦* membership.memberJson m ps cs }}

end spec

end EtcdGrove
end Perennial
