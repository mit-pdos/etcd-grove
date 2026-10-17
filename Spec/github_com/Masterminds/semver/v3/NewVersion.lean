/-
`semver.NewVersion`: the trust boundary (`github.com/Masterminds/semver/v3` is names-only). Lean-first (the
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

/-- `semver.NewVersion(s)` returns a version, not nil, or a non-nil error (and a nil version). -/
abbrev semver.NewVersion.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
    (App (Val (@! github_com.Masterminds.semver.v3.NewVersion)) (Val #s))
  {{ (v : Loc) (err : GoInterface), RET (PairV #v #err);
      ⌜(err = GoInterface.nil ∧ v ≠ null) ∨ (err ≠ GoInterface.nil ∧ v = null)⌝ }}

end spec

end EtcdGrove
end Perennial
