/-
`membership.computeMemberID(peerURLs, clusterName, now)` (`member.go:61-74`; claim #34, stage 2,
2026-11-25: translated with its body, over Perennial's proved `crypto/sha1.Sum`). Lean-first.
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

/-- **`computeMemberID(us, token, nil)`** of plain peer URLs `us` (read-only; `URL.String()` is
`urlStrOf`), when the `fips140` GODEBUG setting is off (`crypto/sha1.Sum`'s premise; with
`fips140=only` it panics), at most `2^62` of them (`sort.Strings`' bound): `memberIDOf` of their strings and the token. -/
abbrev membership.computeMemberID.spec : Prop :=
  ∀ (sl : GoSlice) (us : List _root_.Perennial.net.url.URL) (token : GoString),
  crypto.fips140.GodebugFips140Off → (∀ u ∈ us, http.urlRootPlain u) → us.length ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ sl ↦*□ us }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.computeMemberID)) (Val #sl)) (Val #token)) (Val #(null : Loc)))
  {{ RET #(membership.memberIDOf (us.map membership.urlStrOf) token); True }}

end spec

end EtcdGrove
end Perennial
