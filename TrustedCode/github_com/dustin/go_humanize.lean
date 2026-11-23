/-
Trusted code for `github.com/dustin/go-humanize`, in namespace `github_com.dustin.go_humanize` like the generated package (`Code/github_com/dustin/go_humanize.toml`): its `init`
function, which the model skip (etcd-grove#32).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.dustin.go_humanize

noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- `si.go`'s `init` (go-humanize v1.1.0, the version etcd's `go.mod` pins): builds a character class from
the constant tables `siPrefixTable` and `siParseAliases` (a map: its range order varies between runs,
so the class's characters do too, never its meaning) and sets `riParseRegex` to its
`regexp.MustCompile`. It cannot panic: every such pattern is valid (a bracket expression of literal
prefix characters; every Go program importing go-humanize starts).
The model does nothing: the variables it writes are names-only (not allocated, read by no translated
code: `Code/github_com/dustin/go_humanize.toml`), so not running it is unobservable to the verified code (Go's own functions over them
are untranslated, specified by their trust-boundary specs). Until 2026-11-22 the trust-boundary axiom
`initFuncsOk` said it returns (etcd-grove#32). -/
def init.«0».impl : val :=
  λ: <>, #()

end code
end

end github_com.dustin.go_humanize

end Perennial
