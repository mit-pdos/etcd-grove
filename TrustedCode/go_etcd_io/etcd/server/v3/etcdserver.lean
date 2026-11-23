/-
Trusted code for `go.etcd.io/etcd/server/v3/etcdserver`, in namespace
`go_etcd_io.etcd.server.v3.etcdserver` like the generated package
(`Code/go_etcd_io/etcd/server/v3/etcdserver.toml`): its two `init` functions that publish `expvar`
variables, which the models skip (etcd-grove#39, 2026-11-23). Its first `init` (`metrics.go`, the
metrics' registration) is translated.
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace go_etcd_io.etcd.server.v3.etcdserver

noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- `etcdserver`'s second `init` (etcd `edc800c6f262`, `raft.go:55`):

```go
func init() {
	expvar.Publish("raft.status", expvar.Func(func() any {
		raftStatusMu.Lock()
		defer raftStatusMu.Unlock()
		if raftStatus == nil {
			return nil
		}
		return raftStatus()
	}))
}
```

`expvar.Publish` adds the closure to `expvar`'s registry under the name, under the registry's lock; it
panics only if the name is already registered ("Reuse of exported var name"), and `"raft.status"` is
published once, here (no other package of etcd or its dependencies publishes it, and Go runs a
package's `init` once). Building the closure calls nothing. The closure runs only when the registry is
read and the variable formatted (`expvar.Do`, `(Func).String`): by `expvar`'s HTTP handler on
`http.DefaultServeMux` (`/debug/vars`) and by etcd's `etcdhttp.HandleDebug` (registered by `embed`).
Neither is translated, and no translated code or example serves either mux, so no verified execution
runs the closure; `expvar` itself is not translated (not in the package's goose imports). The model
does nothing (until 2026-11-23 the trust-boundary axiom `initFuncsOk` said it returns). The package's
fact keeps `raftStatusMu`'s invariant (`∃ f, raftStatus ↦ f`) as if the closure could take the lock. -/
def init.«1».impl : val :=
  λ: <>, #()

/-- `etcdserver`'s third `init` (etcd `edc800c6f262`, `server.go:128`):

```go
func init() {
	expvar.Publish(
		"file_descriptor_limit",
		expvar.Func(
			func() any {
				n, _ := runtime.FDLimit()
				return n
			},
		),
	)
}
```

As `init.«1»`: `expvar.Publish` panics only on a name already registered, and
`"file_descriptor_limit"` is published once, here; the closure (`runtime.FDLimit`, a `getrlimit`) runs
only when the registry is read, which no translated code or example does, and it touches no state of
the translated code. The model does nothing (until 2026-11-23 the trust-boundary axiom `initFuncsOk`
said it returns). -/
def init.«2».impl : val :=
  λ: <>, #()

end code
end

end go_etcd_io.etcd.server.v3.etcdserver

end Perennial
