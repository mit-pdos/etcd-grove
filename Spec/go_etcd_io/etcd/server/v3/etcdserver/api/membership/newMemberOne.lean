/-
`membership.newMember(name, peerURLs, memberID, isLearner)` (`member.go`): a fresh member with the id.
Lean-first (no Rocq counterpart); etcd_safe's deployment check (2026-11-24).

**The one-URL variant** (`.specOne`, merged 2026-11-24 beside claim #34's general `.spec`): stated over
`membership.Assumptions`, which the deployment check's callers (`examples/etcd/dist`'s client, whose
`Assumptions` do not import `etcdserver`'s) have, where the general spec's vocabulary (`memberAt`,
`Build.lean`) is over `etcdserver.Assumptions`. To go once membership's defs are over `membership.Assumptions`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewMemberDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.MemberId
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.URLs
public import Perennial.TrustedCode.crypto.fips140

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

/-- `newMember(name, us, id, l)`, of read-only `URLs`, returns a fresh member (owned) of id `id`. -/
abbrev membership.newMember.specOne : Prop :=
  ∀ (name : GoString) (sl : GoSlice) (us : List _root_.Perennial.net.url.URL) (id : w64) (l : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ sl ↦*□ us }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.newMember)) (Val #name)) (Val #sl)) (Val #id)) (Val #l))
  {{ (m : Loc) (mv : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member), RET #m; m ↦ mv ∗ ⌜mv.ID' = id⌝ }}

end spec

end EtcdGrove
end Perennial
