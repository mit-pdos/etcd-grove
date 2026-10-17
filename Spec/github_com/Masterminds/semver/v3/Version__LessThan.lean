/-
`semver.Version.LessThan`: the trust boundary (`github.com/Masterminds/semver/v3` is names-only). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

/-- A `semver.Version`'s (major, minor, patch). -/
def semver.triple [FfiSyntax] (v : github_com.Masterminds.semver.v3.Version) : Nat × Nat × Nat :=
  (v.major'.toNat, v.minor'.toNat, v.patch'.toNat)

/-- The lexicographic order of (major, minor, patch) triples. -/
def semver.tripleLt (a b : Nat × Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `v.LessThan(o)` (both not nil: `Compare` reads both) returns a boolean that, for versions
whose contents are fixed (`↦□`, as every `semver.Version` etcd compares is: parsed or
package-level, never written after), follows the order of the (major, minor, patch) triples:
`true` if `*v`'s is lexicographically below `*o`'s, `false` if above (`Compare` compares the
three segments first, `compareSegment`); on equal triples (pre-releases decide) it says
nothing. (Strengthened for etcd#22261's verification, which needs `VersionForPeer`'s answer for a
peer below or above v3.8; the precondition is unchanged.) -/
abbrev semver.Version.LessThan.spec : Prop :=
  ∀ (v o : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ ⌜v ≠ null ∧ o ≠ null⌝ }}
    (App (Val (v @!! go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty @!! go!"LessThan")) (Val #o))
  {{ (b : Bool), RET #b;
      ∀ (vv ov : github_com.Masterminds.semver.v3.Version), v ↦□ vv -∗ o ↦□ ov -∗
        ⌜(semver.tripleLt (semver.triple vv) (semver.triple ov) → b = true) ∧
         (semver.tripleLt (semver.triple ov) (semver.triple vv) → b = false)⌝ }}

end spec

end EtcdGrove
end Perennial
