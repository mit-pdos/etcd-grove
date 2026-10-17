/-
`semver.New`: the trust boundary (`github.com/Masterminds/semver/v3` is names-only). Lean-first (the
downgrade API, etcd-io/etcd#22575, 2026-10-16).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

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

/-- `semver.New(major, minor, patch, pre, metadata)` returns a version, not nil (`&Version{...}`
after `v.String()`; `New` never fails). -/
abbrev semver.New.spec : Prop :=
  ∀ (maj mnr pat : w64) (pre md : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
    (App (App (App (App (App (Val (@! github_com.Masterminds.semver.v3.New)) (Val #maj)) (Val #mnr))
      (Val #pat)) (Val #pre)) (Val #md))
  {{ (v : Loc), RET #v; ⌜v ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
