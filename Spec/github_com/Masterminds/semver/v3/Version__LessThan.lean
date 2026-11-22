/-
`semver.Version.LessThan`: proved over the real code since 2026-11-22 (prove-ps2-semver; until then
the trust boundary, of any receivers not nil, returning some boolean). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.github_com.Masterminds.semver.v3.CompareModel

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

/-- `v.LessThan(o)` of the versions `v` and `o` point to, at any fractions, kept, returns whether
`v.Compare(o) < 0` (`semver.lessThan`: by major, minor, patch, then prerelease). (2026-11-22,
prove-ps2-semver: until then of any `v`, `o` not nil, which a concurrent writer races, and some
boolean; `notes/specs-only/ledger.md`.) -/
abbrev semver.Version.LessThan.spec : Prop :=
  ∀ (v o : Loc) (dv dw : DFrac) (x y : github_com.Masterminds.semver.v3.Version),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ v ↦{dv} x ∗ o ↦{dw} y }}
    (App (Val (v @!! go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty @!! go!"LessThan")) (Val #o))
  {{ RET #(decide (semver.lessThan x y)); v ↦{dv} x ∗ o ↦{dw} y }}

end spec

end EtcdGrove
end Perennial
