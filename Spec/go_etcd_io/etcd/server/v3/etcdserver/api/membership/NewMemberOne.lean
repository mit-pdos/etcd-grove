/-
`membership.NewMember(name, peerURLs, clusterName, nil)` (`member.go`), of one peer URL
`url.URL{Scheme: "http", Host: p}`: a fresh member whose id is `memberIdOf ("http://" ++ p) clusterName`
when `p` is a plain host. Lean-first (no Rocq counterpart); etcd_safe's deployment check
(`notes/etcd-dist-plan.md`, D2): `deployment.memberIDs` computes the members' ids with it. (An interim
trust-boundary axiom until 2026-11-24, when `computeMemberID` was translated with its body again.)

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

/-- `NewMember(name, us, token, nil)`, where `us` is a read-only `types.URLs` slice of exactly the one URL
`url.URL{Scheme: "http", Host: p}`, returns a pointer to a fresh member (owned), whose `ID` is
`memberIdOf ("http://" ++ p) token` (etcd's `computeMemberID`) when `p` is a plain host
(`http.urlRootPlain`: non-empty, of bytes `url.URL.String` writes unescaped). The `fips140` GODEBUG
setting unset or `off` (`GodebugFips140Off`): in mode `only`, `crypto/sha1.Sum` panics. The URL plain and
shorter than `2^61` bytes (`strings.Join`'s bound in `computeMemberID`). -/
abbrev membership.NewMember.specOne : Prop :=
  ∀ (name : GoString) (sl : GoSlice) (p token : GoString),
  crypto.fips140.GodebugFips140Off → http.urlRootPlain (membership.urlHttp p) →
  (go!"http://" ++ p).length < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ sl ↦*□ [membership.urlHttp p] }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewMember)) (Val #name)) (Val #sl)) (Val #token)) (Val #null))
  {{ (m : Loc) (mv : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member), RET #m; m ↦ mv ∗
      ⌜http.urlRootPlain (membership.urlHttp p) →
        mv.ID' = membership.memberIdOf (go!"http://" ++ p) token⌝ }}

end spec

end EtcdGrove
end Perennial
