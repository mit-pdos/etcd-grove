/-
Trusted model of the net/rpc model's `Stuck` (namespace of the generated package; `project models-net of `etc/goose.py`, `Net/Code/net/rpc.toml``): the model's
not-modelled point (`models/net/rpc/codec.go`; models/README.md, "Not modelled: stuck"), whose Go body is
`select {}`.

```go
func Stuck() {
	select {}
}
```

Its model is Perennial's `internal.gomodel.Stuck.impl` (`Panic "not modelled"`: no behaviour, a
stuck panic no `recover` catches and no WP rule steps), the shared stuck point of the Go models,
which a model outside Perennial's overlay declares through a stub of its own. Why it is faithful:
the model calls it only where it does not model Go's behaviour (a request frame longer than `maxFrame` in `clientCodec.WriteRequest`, where Go's gob encoder refuses a message too big but leaves the header it already encoded in its buffer for the next flush; a second `SetCodec`; `getCodec` with no codec registered; the debugging page; and, through the generated codecs' `rpcStuck`, a value of a type the codec does not list, a nil pointer, decoding across types), so it is less defined
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

namespace net.rpc

section code
variable [GooseExts] [GoGlobalContext]

/-- `Stuck()`: see the file header. -/
def Stuck.impl : val := internal.gomodel.Stuck.impl

end code
end net.rpc

end Perennial
