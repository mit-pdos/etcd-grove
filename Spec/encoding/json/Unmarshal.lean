/-
`json.Unmarshal(data, v)` (`encoding/json`, names only): the trust boundary (D43 M4, 2026-10-26,
the user's decision), for the one target the verified code passes, a `*ConfigChangeContext`
(`membership.ValidateConfigurationChange`'s `AddNode` case). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest

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
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- `json.Unmarshal(data, cc)` into a `*membership.ConfigChangeContext` `p`, of bytes whose decoding
the model knows (`membership.ccContextOf data = some (id, prom)`: a JSON object with the
embedded `Member`'s fields and `IsPromote`): it returns `nil` and leaves `*p` with the member's id
`id`, `IsPromote` `prom`, and the member's peer URLs, `IsLearner`, name and client URLs as
`membership.ccMemberOf` models them, its URL slices fresh (D43 M5e, 2026-10-26, the user's
decision: restated with the name and the client URLs, which `applyConfChange`'s `AddMember` needs
of the member it adds). Faithful: `encoding/json` decodes an object into the
struct's exported fields by name (`ConfigChangeContext`'s `Member` is embedded, so its fields are
the object's; `ID` an integer, `PeerURLs` and `ClientURLs` arrays of strings, `IsLearner` a
boolean, `Name` a string), allocating the slices, and leaves the other fields as the JSON says; it reads `data`, writes nothing else, and
returns `nil` on input it decodes. `ccContextOf`/`ccMemberOf` are opaque functions of the bytes:
the spec claims only that the decoding is a function of them. The URL slices are fresh only if
`*p`'s were `nil` (2026-11-20, prove-reflectfmt: until then any `v`): `encoding/json` decodes an
array into the existing slice, reusing its backing array while its capacity lasts (go1.27.3
`encoding/json/decode.go:553-556`, `array`: `v.Grow`/`v.SetLen` on the field's own slice), so a non-nil
`PeerURLs` would come back aliased to memory the caller still owns
(`notes/axiom-review/json-unmarshal-alias.md`, `examples/axiomcx/jsonunmarshalalias`). Both
callers decode into `new(ConfigChangeContext)`. -/
abbrev encoding.json.Unmarshal.spec : Prop :=
  ∀ (sl : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (v : go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext) (id : w64)
    (prom : Bool),
  membership.ccContextOf bs = some (id, prom) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ sl ↦*{dq} bs ∗ p ↦ v ∗
      ⌜v.Member'.RaftAttributes'.PeerURLs' = slice.nil ∧
        v.Member'.Attributes'.ClientURLs' = slice.nil⌝ }}
    (App (App (Val (@! _root_.Perennial.encoding.json.Unmarshal)) (Val #sl))
      (Val #(interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext.ty) #p)))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ sl ↦*{dq} bs ∗
      ∃ (v' : go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext)
        (pus : List GoString),
        p ↦ v' ∗ v'.Member'.RaftAttributes'.PeerURLs' ↦* pus ∗
        v'.Member'.Attributes'.ClientURLs' ↦* (membership.ccMemberOf bs).clientURLs ∗
        ⌜v'.Member'.ID' = id ∧ v'.IsPromote' = prom ∧
          pus = (membership.ccMemberOf bs).peerURLs ∧
          v'.Member'.RaftAttributes'.IsLearner' = (membership.ccMemberOf bs).isLearner ∧
          v'.Member'.Attributes'.Name' = (membership.ccMemberOf bs).name⌝ }}

end spec

end EtcdGrove
end Perennial
