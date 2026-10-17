/-
`version.VersionForPeer(peerVer)` (`api/v3/version`, translated with its body for etcd#22261's
verification): the version string rafthttp sends a peer in `X-Server-Version`. Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base
public import Spec.github_com.Masterminds.semver.v3.Version__LessThan

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.version.Assumptions]

/-- What `VersionForPeer` may return for a peer whose version is `p` (a `*semver.Version`), when
the package variable `Version` is `ver`: `ver` without a leading `"v"` if the peer's version is
unknown (`p` nil); otherwise `ver` either with or without it (with it exactly when the peer is at
v3.8 or later, by semver's `LessThan`, which is at the trust boundary with an unspecified
result). -/
def version.versionForPeerOk (p : Loc) (ver s : GoString) : Prop :=
  (p = null → s = strings.trimPrefix ver go!"v") ∧
  (s = ver ∨ s = strings.trimPrefix ver go!"v")

/-- What `VersionForPeer` returns for a known peer version `pv` (`*p`), by its (major, minor,
patch): `ver` without a leading `"v"` below 3.8.0, `ver` itself above. At exactly 3.8.0 the
pre-release decides (`3.8.0-rc.0` is below v3.8, `3.8.0` is not), which the semver postulate does
not model. -/
def version.versionForKnownPeerOk (pv : github_com.Masterminds.semver.v3.Version)
    (ver s : GoString) : Prop :=
  (semver.tripleLt (semver.triple pv) (3, 8, 0) → s = strings.trimPrefix ver go!"v") ∧
  (semver.tripleLt (3, 8, 0) (semver.triple pv) → s = ver)

/-- `VersionForPeer(p)` returns a string allowed by `versionForPeerOk`, and, if the peer's version
`*p` is fixed (`↦□`: rafthttp's cached versions are parsed by `serverVersion` and never
written), by `versionForKnownPeerOk`; it does not panic (for any `p`: `LessThan` is only called on
a non-nil `p`). -/
abbrev version.VersionForPeer.spec : Prop :=
  ∀ (p : Loc) (ver : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version ∗
      globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ ver }}
    (App (Val (@! go_etcd_io.etcd.api.v3.version.VersionForPeer)) (Val #p))
  {{ (s : GoString), RET #s; ⌜version.versionForPeerOk p ver s⌝ ∗
      ∀ (pv : github_com.Masterminds.semver.v3.Version), p ↦□ pv -∗
        ⌜version.versionForKnownPeerOk pv ver s⌝ }}

end spec

/-- When `Version` has no leading `"v"` (as at the PR's head, `"3.8.0-alpha.0"`), every result
`versionForPeerOk` allows is `Version` itself: `VersionForPeer` changes nothing on the wire. -/
theorem version.versionForPeerOk_unprefixed {p : Loc} {ver s : GoString}
    (hv : ¬ go!"v" <+: ver) (h : version.versionForPeerOk p ver s) : s = ver := by
  have ht : strings.trimPrefix ver go!"v" = ver := by
    simp only [strings.trimPrefix, hv, ite_false]
  rcases h.2 with h | h
  · exact h
  · rw [h, ht]

/-- A peer at 3.x with x < 8 (a v3.7 member, which parses `X-Server-Version` with coreos/go-semver
and panics on a leading `"v"`) gets `Version` without its leading `"v"`. -/
theorem version.versionForKnownPeerOk_below_3_8 [FfiSyntax]
    {pv : github_com.Masterminds.semver.v3.Version} {ver s : GoString}
    (h : version.versionForKnownPeerOk pv ver s)
    (h3 : (semver.triple pv).1 = 3) (h8 : (semver.triple pv).2.1 < 8) :
    s = strings.trimPrefix ver go!"v" :=
  h.1 (Or.inr ⟨h3, Or.inl h8⟩)

end EtcdGrove
end Perennial
