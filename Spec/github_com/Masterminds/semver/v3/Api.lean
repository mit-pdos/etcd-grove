/-
# `github.com/Masterminds/semver/v3`: the trust boundary (batch 4b)

semver (v3.5.0 at etcd's pin) is translated types and names only: its specs are **assumed**, each
true of the library's `version.go` at the pin. etcd parses version strings (its own constants, the
peers' `X-Server-Version`/`X-Min-Cluster-Version` headers, a committed `ClusterVersionSet`'s
`Ver`, the stored cluster version), builds `major.minor.0` versions (`New`), and compares them
(`LessThan`).

## Model

* `SemVer` (transparent): a version's fields, `major.minor.patch-pre+meta` (`Version`'s fields but
  `original`, which only `Original()` reads).
* `parse s` (opaque function): **what `NewVersion(s)` makes of `s`** (`none`: an error). With the
  package's default `CoerceNewVersion = true` it is the lenient parser (`coerceNewVersion`: a
  leading `v`, missing minor or patch); etcd never writes the variable. Laws pin it down where
  callers need it: `parse_render` (a parsed version's `String()` parses back to it),
  `parse_plain` (`a.b.c` parses), `parse_version` (etcd's own `version.Version`).
* `render v` (transparent): **`String()`**: `major.minor.patch`, then `-pre` and `+meta` if not
  empty (decimal, Perennial's `fmt.decimal`).
* `SemVer.ltb a b` (transparent): **`a.LessThan(b)`**: `Compare` (`version.go:525`): the
  `(major, minor, patch)` triples in order; equal ones: a version without a prerelease is above one
  with; two prereleases by `preLtb` (opaque: semver 2.0's precedence of dot-separated identifiers,
  `comparePrerelease`). Metadata is ignored.
* `verAt v sv` (transparent, persistent): **`v` is a `*Version` holding `sv`**, read-only for good
  (nothing in etcd writes a version after making it; the library's methods only read).

## Users

`rafthttp` (`util.go:134-175`, `stream.go:613,712`: `MustParse` of headers and constants, `New`,
`Major`, `Minor`, `LessThan`), the applier (`apply/backend.go:272-275`: `MustParse(r.Ver)`,
`LessThan`), the membership (`membership/cluster.go:270,586,610`: `MustParse`, `String`), the
schema (`schema/membership.go:205,233`: `MustParse`, `NewVersion`), the downgrade checks
(`etcdserver/version/downgrade.go`: `New`, `Major`, `Minor`, `LessThan`). Snippets:
`examples/specreq/pkgleaves/leaves.go` (`ReqParseCompare`, `ReqMajorMinor`, `ReqRoundTrip`).
-/
module

public import GeneratedProof.github_com.Masterminds.semver.v3
public import Spec.PkgInit.github_com.Masterminds.semver.v3
public import Perennial.Proof.fmt.Base

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Semver

open Iris Iris.BI

section model
variable [GooseExts]

/-- **A version's fields** (see the header). -/
structure SemVer where
  major : w64
  minor : w64
  patch : w64
  pre : GoString
  metadata : GoString

/-- **What `NewVersion(s)` makes of `s`** (`none`: an error); opaque. -/
opaque parse : GoString → Option SemVer

/-- semver 2.0's precedence of two non-empty prerelease strings (opaque). -/
opaque preLtb : GoString → GoString → Bool

/-- **`String()`**: `major.minor.patch[-pre][+meta]`. -/
def render (v : SemVer) : GoString :=
  _root_.Perennial.fmt.decimal (uint.Z v.major) ++ go!"." ++
  _root_.Perennial.fmt.decimal (uint.Z v.minor) ++ go!"." ++
  _root_.Perennial.fmt.decimal (uint.Z v.patch) ++
  (if v.pre = [] then [] else go!"-" ++ v.pre) ++
  (if v.metadata = [] then [] else go!"+" ++ v.metadata)

/-- **`a.LessThan(b)`** (see the header). -/
def SemVer.ltb (a b : SemVer) : Bool :=
  decide (uint.Z a.major < uint.Z b.major) ||
  (decide (a.major = b.major) && (decide (uint.Z a.minor < uint.Z b.minor) ||
  (decide (a.minor = b.minor) && (decide (uint.Z a.patch < uint.Z b.patch) ||
  (decide (a.patch = b.patch) &&
    ((decide (a.pre ≠ []) && decide (b.pre = [])) ||
     (decide (a.pre ≠ []) && decide (b.pre ≠ []) && preLtb a.pre b.pre)))))))

/-- The fields of a `Version` struct. -/
def verOf (x : github_com.Masterminds.semver.v3.Version) : SemVer :=
  ⟨x.major', x.minor', x.patch', x.pre', x.metadata'⟩

end model

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`v` is a `*Version` holding `sv`**, read-only for good (persistent). -/
def verAt (v : Loc) (sv : SemVer) : IProp GF :=
  iprop(∃ x : github_com.Masterminds.semver.v3.Version, v ↦□ x ∗ ⌜verOf x = sv⌝)

end vocab

section laws
variable [GooseExts]

/-- A parsed version's `String()` parses back to it. -/
def parse_render.spec : Prop := ∀ s sv, parse s = some sv → parse (render sv) = some sv

/-- `a.b.c` (decimal, no prerelease or metadata) parses. -/
def parse_plain.spec : Prop := ∀ a b c : w64,
  parse (render ⟨a, b, c, [], []⟩) = some ⟨a, b, c, [], []⟩

/-- etcd's own version string (`api/version.Version` at the pin). -/
def parse_version.spec : Prop :=
  parse go!"3.8.0-alpha.0" = some ⟨W64 3, W64 8, W64 0, go!"alpha.0", []⟩

end laws

end Semver
end EtcdGrove
end Perennial
