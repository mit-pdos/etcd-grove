/-
`membership.computeMemberID(peerURLs, clusterName, nil)` (`member.go`) of one URL: the URLs' strings
sorted and joined, then the token, hashed with SHA-1, the first 8 bytes read big-endian
(`membership.memberIdOf`). Lean-first (no Rocq counterpart); etcd_safe's deployment check (2026-11-24).
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

/-- `computeMemberID(us, token, nil)`, of a read-only `URLs` slice of one URL `u`, returns an id, which is
`memberIdOf ("http://" ++ host) token` when `u` is of only the scheme `http` and a plain host
(`http.urlRootPlain`: its string is then `http://` and the host). The `fips140` GODEBUG setting unset or
`off` (`crypto/sha1.Sum`'s premise). -/
abbrev membership.computeMemberID.spec : Prop :=
  ∀ (sl : GoSlice) (u : _root_.Perennial.net.url.URL) (token : GoString),
  crypto.fips140.GodebugFips140Off →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ sl ↦*□ [u] }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.computeMemberID)) (Val #sl)) (Val #token)) (Val #null))
  {{ (id : w64), RET #id; ⌜http.urlRootPlain u → id = membership.memberIdOf (go!"http://" ++ u.Host') token⌝ }}

end spec

end EtcdGrove
end Perennial
