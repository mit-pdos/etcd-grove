/-
`json.Marshal(c)` (`encoding/json`, names only) of a `membership.ConfigChangeContext` passed by
value (boxed in `any`): `EtcdServer.promoteMember`'s `json.Marshal(promoteChangeContext)`. As
`MarshalMember`: no error, some fresh bytes, the embedded member's two string slices borrowed.

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
(`Proof/encoding/json/MarshalConfigChangeContext.lean`), beside the k8s continue-token spec (`Spec/encoding/json/Marshal.lean`:
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
abbrev encoding.json.MarshalConfigChangeContext.spec : Prop :=
  ∀ (c : go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext) (dp dc : DFrac) (ps cs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗
      c.Member'.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ c.Member'.Attributes'.ClientURLs' ↦*{dc} cs }}
    (App (Val (@! _root_.Perennial.encoding.json.Marshal))
      (Val #(interface.mkOk go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext.ty #c)))
  {{ (sl : GoSlice), RET (PairV #sl #GoInterface.nil);
      c.Member'.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ c.Member'.Attributes'.ClientURLs' ↦*{dc} cs ∗ sl ↦* membership.ccJson c ps cs }}

end spec

end EtcdGrove
end Perennial
