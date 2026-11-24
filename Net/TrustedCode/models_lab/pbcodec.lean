/-
Trusted model of `models.lab/pbcodec`'s `Stuck` (namespace of the generated package; `project models of `etc/goose.py`, `Net/Code/models_lab/pbcodec.toml``): the model's
not-modelled point (`models/pbcodec/pbcodec.go`; models/README.md, "Not modelled: stuck"), whose Go body is
`select {}`.

```go
func Stuck() {
	select {}
}
```

Its model is Perennial's `internal.gomodel.Stuck.impl` (`Panic "not modelled"`: no behaviour, a
stuck panic no `recover` catches and no WP rule steps), the shared stuck point of the Go models,
which a model outside Perennial's overlay declares through a stub of its own. Why it is faithful:
the model calls it only where it does not model Go's behaviour (the codecs pbgen.py generates in codec mode: marshaling or unmarshaling a value of a type the codec was not generated for), so it is less defined
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

namespace models_lab.pbcodec

section code
variable [GooseExts] [GoGlobalContext]

/-- `Stuck()`: see the file header. -/
def Stuck.impl : val := internal.gomodel.Stuck.impl

end code
end models_lab.pbcodec

end Perennial
