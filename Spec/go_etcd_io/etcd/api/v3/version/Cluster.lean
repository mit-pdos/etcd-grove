/-
`version.Cluster(v)` (`api/version/version.go`): the major.minor prefix of a version string.

Users: the server's logs and metrics labels (`server.go:581`, `2331`), `Status`/`Downgrade` replies
(`v3_server.go:1243`, `1264`).

**Assumed** (a translation gap, not a trust boundary of etcd's design): the package is translated
names only (`Code/go_etcd_io/etcd/api/v3/version.toml`), so the body is axiomatized. True of the
code: it parses `v` with `semver.NewVersion` and returns `major.minor`, or (a parse error) splits
on `.` and joins the first two parts: a string, never a panic.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/api/v3/version/Cluster.lean`: the old post
(`semverStr v → asciiStr s`) dropped: no user reads the string but a logger or a reply field.
Margin: the value is not specified.
-/
module

public import GeneratedProof.go_etcd_io.etcd.api.v3.version
public import Spec.PkgInit.go_etcd_io.etcd.api.v3.version

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Version

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.version.Assumptions]

/-- `Cluster(v)`: some string. -/
def Cluster.spec : Prop :=
  ∀ (v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version }}
    (App (Val (@! go_etcd_io.etcd.api.v3.version.Cluster)) (Val #v))
  {{ (s : GoString), RET #s; True }}

end spec

end Version
end EtcdGrove
end Perennial
