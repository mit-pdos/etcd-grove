/-
Trusted model of `go/token` (namespace of the generated package; project models-net of
`etc/goose.py`, `Net/Code/go/token.toml`): `IsExported`, which the net/rpc model's `register`
calls on a service's name (`!useName && !token.IsExported(sname)`). Go 1.27.3 (`go/token/token.go`):

```go
func IsExported(name string) bool {
	ch, _ := utf8.DecodeRuneInString(name)
	return unicode.IsUpper(ch)
}
```

Not translated: `unicode.IsUpper` reads Unicode's case tables, which nothing translates. The model
is exact on every name whose first byte is ASCII (`< 0x80`): `DecodeRuneInString` returns that
byte, and `IsUpper` of an ASCII rune is `'A' <= r && r <= 'Z'` (`unicode/letter.go`, its
`r <= MaxLatin1` fast path: `properties[uint8(r)]&pLmask == pLu`, which for ASCII holds exactly of
`A`..`Z`, `unicode/tables.go`). The empty name decodes to `RuneError` (U+FFFD), which is not upper
case: `false`. A name whose first byte is not ASCII is a **choice point** (`models/README.md`): the
model returns an arbitrary boolean (`ArbitraryInt`'s low bit), so every result Go gives is one of
the model's; a proof about such a name can rely on nothing. Go identifiers of the programs proved
here are ASCII. Checked against Go by `models/internal/rpcdifftest/isexported_test.go`
(`TestIsExportedASCII`: every ASCII first byte, with several continuations, and the empty name).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace go.token

section code
variable [GooseExts] [GoGlobalContext]

/-- `IsExported(name)`: see the file header. -/
noncomputable def IsExported.impl : val :=
  λ: "name",
    let: "n" := (FuncResolve go.len [go.string]) #() "name" in
    if: "n" =⟨go.int⟩ #(W64 0) then #false
    else
      let: "c" := (Index go.string) ("name", #(W64 0)) in
      if: "c" <⟨go.byte⟩ #(W8 0x80) then
        (#(W8 0x41) ≤⟨go.byte⟩ "c") && ("c" ≤⟨go.byte⟩ #(W8 0x5A))
      else
        ((ArbitraryInt &⟨go.uint64⟩ #(W64 1)) =⟨go.uint64⟩ #(W64 1))

end code
end go.token

end Perennial
