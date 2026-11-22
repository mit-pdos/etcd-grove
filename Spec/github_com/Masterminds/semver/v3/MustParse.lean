/-
`semver.MustParse`: proved over `NewVersion`'s spec since 2026-11-22 (prove-ps2-client; until then the
trust boundary). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.Masterminds.semver.v3.Assumptions]

/-- `semver.MustParse(s)`: a version, not nil, if `s` parses (`semverValid`), the version of
`s` (`apply.semverIs`, D22, 2026-10-23: the value the cluster's `SetVersion` saves is its
`String()`, `apply.semverNorm s`), read-only (2026-11-20, prove-smalllibs: the version it points to, `NewVersion`'s
fresh allocation, which nothing else holds); else a panic (`MustParse` panics on an error of
`NewVersion`). -/
abbrev semver.MustParse.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
    (App (Val (@! github_com.Masterminds.semver.v3.MustParse)) (Val #s))
  {{ (r : val), RET r;
      (⌜apply.semverValid s⌝ ∗ ∃ (v : Loc) (x : github_com.Masterminds.semver.v3.Version),
        ⌜r = #v ∧ v ≠ null⌝ ∗ v ↦□ x ∗ apply.semverIs v s) ∨
        ⌜¬ apply.semverValid s ∧ ∃ p : val, r = PanicV p⌝ }}

end spec

end EtcdGrove
end Perennial
