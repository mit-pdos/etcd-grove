/-
`membership.NewMember(name, peerURLs, clusterName, now)` (`member.go`), of one peer URL `http://p` and
`now = nil`: a fresh member whose id is `memberId ("http://" ++ p) clusterName`. Lean-first (no Rocq
counterpart); etcd_safe's deployment check (`notes/etcd-dist-plan.md`, D2): `deployment.memberIDs`
computes the members' ids with it. A trust-boundary axiom (interim: `Proof/.../NewMember.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewMemberDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelDefs
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

/-- `NewMember(name, us, token, nil)`, where `us` is a `types.URLs` slice of exactly the one URL
`url.URL{Scheme: "http", Host: p}` (held at any fraction, kept), returns a pointer to a fresh member
(owned) whose `ID` is `memberId ("http://" ++ p) token` (`TopLevelDefs`'s `memberId`: etcd's
`computeMemberID`, the first 8 bytes, big-endian, of the SHA-1 of the URL's string and the token).
The `fips140` GODEBUG setting unset or `off` (`GodebugFips140Off`): in mode `only`,
`crypto/sha1.Sum` panics. -/
abbrev membership.NewMember.spec : Prop :=
  ∀ (name : GoString) (sl : GoSlice) (dq : DFrac) (p token : GoString),
  crypto.fips140.GodebugFips140Off →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      sl ↦*{dq} [membership.urlHttp p] }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewMember))
      (Val #name)) (Val #sl)) (Val #token)) (Val #null))
  {{ (m : Loc) (mv : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member), RET #m;
      sl ↦*{dq} [membership.urlHttp p] ∗ m ↦ mv ∗
      ⌜mv.ID' = etcd_dist.memberId (go!"http://" ++ p) token⌝ }}

end spec

end EtcdGrove
end Perennial
