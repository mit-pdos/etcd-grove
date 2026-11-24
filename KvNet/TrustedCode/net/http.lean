-- The copy for the part `KvNet/` of `Net/TrustedCode/net/http.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Trusted model of the net/http model's `stuck` (namespace of the generated package; `project models-net of `etc/goose.py`, `Net/Code/net/http.toml``): the model's
not-modelled point (`models/net/http/textproto_model.go`; models/README.md, "Not modelled: stuck"), whose Go body is
`select {}`.

```go
func stuck() {
	select {}
}
```

Its model is Perennial's `internal.gomodel.Stuck.impl` (`Panic "not modelled"`: no behaviour, a
stuck panic no `recover` catches and no WP rule steps), the shared stuck point of the Go models,
which a model outside Perennial's overlay declares through a stub of its own. Why it is faithful:
the model calls it only where it does not model Go's behaviour (header continuation lines, a header block starting with a space, a header name with a space, chunked bodies, TLS, unencrypted HTTP/2, the Transport's round trip), so it is less defined
than Go there, never more, and a verified program never reaches it. Not the Go body's blocking
`select {}`, whose WP rule (`chan.wp_select_blocking []`, precondition `True`) would prove
anything after it, nor a value panic, which a program could recover.
-/
module

public import Perennial.Golang.Defn
public import Perennial.TrustedCode.internal.gomodel

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace net.http

section code
variable [GooseExts] [GoGlobalContext]

/-- `stuck()`: see the file header. -/
def stuck.impl : val := internal.gomodel.Stuck.impl

end code
end net.http

end Perennial
