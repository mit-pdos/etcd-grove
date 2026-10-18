/-
`version.Cluster(v)` (`api/v3/version`): names-only (the server's `start` logs it). Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.github_com.Masterminds.semver.v3.Str

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `version.Cluster(v)` returns a string (names-only: the major and minor of `v`), ASCII if `v`
starts with two decimal numbers each followed by a dot (`semverStr`, a `semver.Version`'s
`String()`): `"%d.%d"` of the parsed version, or else the first two of `strings.Split(v, ".")`
joined by a dot (`version.go`; D19l (iii), 2026-10-18: until then some string). -/
abbrev version.Cluster.spec : Prop :=
  ∀ (v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version }}
    (App (Val (@! go_etcd_io.etcd.api.v3.version.Cluster)) (Val #v))
  {{ (s : GoString), RET #s; ⌜semverStr v → asciiStr s⌝ }}

end spec

end EtcdGrove
end Perennial
