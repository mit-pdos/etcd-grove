/-
`json.Marshal` of a `membership.Member` passed by value (boxed in
`any`): `EtcdServer.AddMember`'s and `UpdateMember`'s `json.Marshal(memb)`. No error; the fresh bytes `membership.memberJson m ps cs`
(`Proof/.../membership/Json.lean`: the JSON encoding/json writes, a function of the value and of its
two URL slices' strings, which are read under any fraction and given back).

Proved (#24 J2, 2026-11-23; a trust-boundary axiom until then, the smallest form "some fresh bytes",
the user's decision of 2026-11-20): `encoding/json` is the model's (`models/encoding/json`), whose
`Marshal` dispatches the value to its type's `JSONModelMarshal` (jsongen's same-package method,
membership's `json_model_gen.go`), which writes it with `models.lab/jsoncodec`'s encoders. The claim
that these are real encoding/json's bytes (Go 1.27.3, JSONv2's `v2_encode.go` with v1's options) is
the model's (`examples/models/jsonetcd/jsonmodel_forks.py`, `models/jsoncodec/jsoncodec_test.go`);
the post now names the bytes, as #34's bootstrap needs (`ctxs = json.Marshal` of each member). The
earlier evidence for the axiom: `examples/authmedjson/`, `notes/axiom-review/json-marshal-member.md`.
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
abbrev encoding.json.MarshalMember.spec : Prop :=
  ∀ (m : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member) (dp dc : DFrac) (ps cs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗
      m.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ m.Attributes'.ClientURLs' ↦*{dc} cs }}
    (App (Val (@! _root_.Perennial.encoding.json.Marshal))
      (Val #(interface.mkOk go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member.ty #m)))
  {{ (sl : GoSlice), RET (PairV #sl #GoInterface.nil);
      m.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ m.Attributes'.ClientURLs' ↦*{dc} cs ∗ sl ↦* membership.memberJson m ps cs }}

end spec

end EtcdGrove
end Perennial
