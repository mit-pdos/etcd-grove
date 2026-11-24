-- The copy for the part `KvNet/` of `Net/TrustedCode/net/rpc.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Trusted model of the net/rpc model's `stuck` (namespace of the generated package; project
models-net of `etc/goose.py`, `Net/Code/net/rpc.toml`): the model's stuck point
(`models/net/rpc/codec.go`), whose Go body is `select {}`.

```go
func stuck() {
	select {}
}
```

Its model is Perennial's `internal.gomodel.Stuck.impl` (`Panic "not modelled"`: no behaviour, a
stuck panic no `recover` catches and no WP rule steps), the shared stuck point of the Go models,
which a model outside Perennial's overlay declares through a stub of its own. Why it is faithful:
the model calls it only where it does not model Go's behaviour, so it is less defined than Go
there, never more, and a verified program never reaches it. Its one caller is
`clientCodec.WriteRequest` on a request frame longer than `maxFrame`: Go's gob encoder refuses a
message too big (`gob: encoder: message too big`) but leaves the header it already encoded in its
buffer for the next flush, so the stream Go then writes is not one the model's frames describe;
the model stops there instead of silently diverging (a refusal that wrote nothing would drop Go's
buffered header). Not the Go body's blocking `select {}`, whose WP rule
(`chan.wp_select_blocking []`, precondition `True`) would prove anything after it.
-/
module

public import Perennial.Golang.Defn
public import Perennial.TrustedCode.internal.gomodel

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace net.rpc

section code
variable [GooseExts] [GoGlobalContext]

/-- `stuck()`: see the file header. -/
def stuck.impl : val := internal.gomodel.Stuck.impl

end code
end net.rpc

end Perennial
