/-
Trusted model of the encoding/json model's `stuck` (namespace of the generated package; `the `std_models` of projects etcd, k8s-apiserver, k8s-daemonset of `etc/goose.py`, `Code/encoding/json.toml``): the model's
not-modelled point (`models/encoding/json/model.go`; models/README.md, "Not modelled: stuck"), whose Go body is
`select {}`.

```go
func stuck() {
	select {}
}
```

Its model is Perennial's `internal.gomodel.Stuck.impl` (`Panic "not modelled"`: no behaviour, a
stuck panic no `recover` catches and no WP rule steps), the shared stuck point of the Go models,
which a model outside Perennial's overlay declares through a stub of its own. Why it is faithful:
the model calls it only where it does not model Go's behaviour (a second `SetCodec`, `getCodec` with no codec registered, `MarshalIndent`, `Indent`, `Compact`, `Encoder.SetIndent`, `Decoder.Token`/`More`/`DisallowUnknownFields`, `RawMessage`'s v2 methods, v2's options, a reader returning data after `io.EOF`), so it is less defined
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

namespace encoding.json

section code
variable [GooseExts] [GoGlobalContext]

/-- `stuck()`: see the file header. -/
def stuck.impl : val := internal.gomodel.Stuck.impl

end code
end encoding.json

end Perennial
