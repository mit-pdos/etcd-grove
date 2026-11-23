/-
Trusted code for `github.com/Masterminds/semver/v3`, in namespace `github_com.Masterminds.semver.v3` like the generated package (`Code/github_com/Masterminds/semver/v3.toml`): its `init`
functions, which the models skip (etcd-grove#32).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.Masterminds.semver.v3

noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- `constraints.go`'s `init` (semver v3.5.0, the version etcd's `go.mod` pins): sets `constraintOps` to a
map literal of the 13 operators' functions, and `constraintRegex`, `constraintRangeRegex`,
`findConstraintRegex` and `validConstraintRegex` to `regexp.MustCompile` of `fmt.Sprintf`s of
constant patterns (`ops`, `cvRegex`). It cannot panic: the map's keys are distinct constants, and
`MustCompile` panics only on an invalid pattern, which these constant ones are not (every Go program
importing semver starts).
The model does nothing: the variables it writes are names-only (not allocated, read by no translated
code: `Code/github_com/Masterminds/semver/v3.toml`), so not running it is unobservable to the verified code (Go's own functions over them
are untranslated, specified by their trust-boundary specs). Until 2026-11-22 the trust-boundary axiom
`initFuncsOk` said it returns (etcd-grove#32). -/
def init.«0».impl : val :=
  λ: <>, #()

/-- `version.go`'s `init` (semver v3.5.0): sets `versionRegex` and `looseVersionRegex` to
`regexp.MustCompile` of the constant patterns `"^" + semVerRegex + "$"` and
`"^" + looseSemVerRegex + "$"`. It cannot panic: the patterns are valid constants (every Go program
importing semver starts).
The model does nothing: the variables it writes are names-only (not allocated, read by no translated
code: `Code/github_com/Masterminds/semver/v3.toml`), so not running it is unobservable to the verified code (Go's own functions over them
are untranslated, specified by their trust-boundary specs). Until 2026-11-22 the trust-boundary axiom
`initFuncsOk` said it returns (etcd-grove#32). -/
def init.«1».impl : val :=
  λ: <>, #()

end code
end

end github_com.Masterminds.semver.v3

end Perennial
