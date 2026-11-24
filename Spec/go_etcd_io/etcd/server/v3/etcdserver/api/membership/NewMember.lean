/-
`membership.NewMember(name, peerURLs, clusterName, now)` (`member.go:49-52`; claim #34, stage 2,
2026-11-25: translated with its body). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Build

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewMember(name, us, token, nil)`** of plain peer URLs `us` (read-only), the `fips140` GODEBUG
setting off: a fresh member, owned, `memberOfURLs name us token`. -/
abbrev membership.NewMember.spec : Prop :=
  ∀ (name : GoString) (sl : GoSlice) (us : List _root_.Perennial.net.url.URL) (token : GoString),
  crypto.fips140.GodebugFips140Off → (∀ u ∈ us, http.urlRootPlain u) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ sl ↦*□ us }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewMember)) (Val #name)) (Val #sl)) (Val #token))
      (Val #(null : Loc)))
  {{ (m : Loc), RET #m; membership.memberAt m 1 (membership.memberOfURLs name us token) }}

end spec

end EtcdGrove
end Perennial
