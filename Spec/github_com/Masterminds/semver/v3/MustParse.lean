/-
`semver.MustParse`: the trust boundary (`github.com/Masterminds/semver/v3` is names-only). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest

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

/-- `semver.MustParse(s)`: a version, not nil, if `s` parses (`semverValid`); else a panic
(`MustParse` panics on an error of `NewVersion`). -/
abbrev semver.MustParse.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
    (App (Val (@! github_com.Masterminds.semver.v3.MustParse)) (Val #s))
  {{ (r : val), RET r;
      ⌜(apply.semverValid s ∧ ∃ v : Loc, r = #v ∧ v ≠ null) ∨
        (¬ apply.semverValid s ∧ ∃ p : val, r = PanicV p)⌝ }}

end spec

end EtcdGrove
end Perennial
