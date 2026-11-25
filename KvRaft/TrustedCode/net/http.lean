-- The copy for the part `KvRaft/` of `Net/TrustedCode/net/http.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Trusted code for the net/http model's `servemux121.go` (namespace of the generated package; project
models-net of `etc/goose.py`, `Net/Code/net/http.toml`): the variable `httpmuxgo121` (a
`*godebug.Setting`; `internal/godebug` is not translated) and the `init` function that reads it
(`init.«1»`, gc's numbering: `http2.go`'s is `init.«0»`), and the environment premise
`GodebugHttpmuxgo121Not1` about that setting. As Perennial's `crypto/fips140`
(`TrustedCode/crypto/fips140.lean`, `godebugFips140`, `GodebugFips140Off`).

```go
var httpmuxgo121 = godebug.New("httpmuxgo121")

var use121 bool

func init() {
	if httpmuxgo121.Value() == "1" {
		use121 = true
		httpmuxgo121.IncNonDefault()
	}
}
```

`use121` itself is translated (`var use121 bool`, zero). The ServeMux's methods read it
(`ServeMux.Handle`, `ServeMux.ServeHTTP`, `ServeMux.Handler`, ...: Go 1.21's matcher `mux121` when
it is true); the proofs cover only the current (Go 1.22) matcher, so they take
`GodebugHttpmuxgo121Not1`, under which this `init` leaves `use121` false.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace net.http

/-- **The run's `httpmuxgo121` GODEBUG setting, as net/http's initializer reads it**: its text,
without the `#`-pattern of `internal/bisect` a setting may carry. Go's runtime hands
`internal/godebug` the process's `GODEBUG` environment variable and the binary's default GODEBUG
(set by the go command from `go.mod`'s `go` and `godebug` lines and the main package's `//go:debug`
directives: `httpmuxgo121=0` for a main module at `go 1.22` or later, `=1` before); the last
`httpmuxgo121=` entry of the variable takes precedence over the default (`godebug.update`). The
setting is not immutable (`internal/godebugs`), but net/http reads it once, in its `init`; the value
here is the one that read returns (an `os.Setenv("GODEBUG", ...)` in a package initialized before
net/http could change it).

The model has no process environment, so the value is opaque: nothing is known or proved about
it, and a theorem about a program holds for every value it could be. A theorem that needs a
particular value takes it as a premise (`GodebugHttpmuxgo121Not1`). -/
opaque godebugHttpmuxgo121 : GoString

/-- **Environment premise: `GODEBUG` does not set `httpmuxgo121=1`** (`godebugHttpmuxgo121` is
not `"1"`): neither the process's `GODEBUG` variable (its last `httpmuxgo121=` entry) nor, when the
variable has none, the binary's default GODEBUG sets it to `1`, whatever `#`-pattern follows. Then
net/http's `init` leaves `use121` false, and the ServeMux uses Go 1.22's pattern matcher.

A top-level theorem about a program whose proof needs it (any program registering or dispatching
on a ServeMux) names it as a hypothesis, and then covers only the runs with that setting. It is
not of the overflow kind of `README.md`'s model assumptions: `GODEBUG=httpmuxgo121=1` is a
setting a real run can have (it restores Go 1.21's matcher, which this repository does not
verify). -/
def GodebugHttpmuxgo121Not1 : Prop :=
  godebugHttpmuxgo121 ≠ go!"1"

section code
variable [GooseExts] [GoGlobalContext]

/-- The initializer of `httpmuxgo121` (`var httpmuxgo121 = godebug.New("httpmuxgo121")`):
`New(name)` is `return &Setting{name: name}`, an allocation; it cannot panic.

The model does nothing, and the variable is not allocated (goose emits no allocation for a
trusted variable: its `init` is its whole initialization), so a load or store of it is stuck.
Sound because its only reader is the `init` function below, also trusted, whose model does not
read it; no translated code reads it (`ServeMux` and `Server` read `use121`, not the setting).
Not modelled: `internal/godebug`'s own state, which no translated code reads. -/
def httpmuxgo121.init : val :=
  λ: <>, #()

/-- servemux121.go's `init` (see the file header). Go's `httpmuxgo121.Value()` looks the setting
up once (`sync.Once`, a `sync.Map`, `internal/godebugs.Lookup`, which lists `httpmuxgo121`, so its
"not listed" panic is unreachable) and returns the setting's text, `godebugHttpmuxgo121`; when the
setting carries a `#`-pattern, it returns `""` instead if the pattern does not match the caller's
stack (`bisect.Matcher.Stack`, which may also print a match line to standard error).
`IncNonDefault()` increments the setting's `/godebug/non-default-behavior/httpmuxgo121:events`
metric (`runtime/metrics`; no translated code reads it). Neither can panic.

The model stores `true` into `use121` when the setting is `"1"`, or leaves it, chosen arbitrarily
(leaving it covers a pattern that does not match); when the setting is not `"1"` it leaves it. So
every value Go can leave in `use121` is one of its results. It cannot panic, nor can Go's `init`.
Not modelled: the metric and a bisect match line on standard error. -/
def init.«1».impl : val :=
  λ: <>,
    if: #(decide (godebugHttpmuxgo121 = go!"1")) then
      (if: ArbitraryInt =⟨go.int64⟩ #(W64 0)
       then GlobalVarAddr go!"net/http.use121" #() <-[go.bool] #true
       else #())
    else #()

end code

end net.http

end Perennial
