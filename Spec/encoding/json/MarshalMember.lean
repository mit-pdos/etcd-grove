/-
`json.Marshal(m)` (`encoding/json`, names only) of a `membership.Member` passed by value (boxed in
`any`): `EtcdServer.AddMember`'s and `UpdateMember`'s `json.Marshal(memb)`. No error; some fresh bytes;
the member's two string slices (`PeerURLs`, `ClientURLs`) read under any fraction and given back.

Faithful (go1.27.3, the pinned toolchain): `json.Marshal` is JSONv2's (`v2_encode.go`,
`jsonv2.Marshal(v, DefaultOptionsV1())`; with `GOEXPERIMENT=nojsonv2` etcd does not build at that
toolchain: prometheus/common imports `encoding/json/jsontext`). The value has no `MarshalJSON` or
`MarshalText` methods (nor has `types.ID`, whose only method is `String`), no maps, pointers, cycles or
unsupported kinds; strings with invalid UTF-8 are replaced by U+FFFD, never an error. So it returns
`nil` and a fresh buffer (`bytes.Clone`, `v2/arshal.go`), reading the value and the strings of its two
slices and writing nothing it is given. The smallest form (the user's decision, 2026-11-20): no claim
on the bytes. Evidence, run at go1.27.3 on etcd's types at the pin: `examples/authmedjson/`
(never an error: `TestNoError`, `TestFunctionOfFields` on 200k random values, `TestNoErrorLarge`,
`TestHuge`; fresh: `TestFresh`; inputs only read: `TestNoRetain`, `TestConcurrentReaders`; attacked
2026-11-20, sound: `notes/axiom-review/json-marshal-member.md`). Lean-first (no Rocq counterpart); the trust
boundary of auth-mediation M2 (`notes/auth-mediation-scope.md`, D4), an axiom
(`Proof/encoding/json/MarshalMember.lean`), beside the k8s continue-token spec (`Spec/encoding/json/Marshal.lean`:
one spec per argument shape at this trust boundary, as there).
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
