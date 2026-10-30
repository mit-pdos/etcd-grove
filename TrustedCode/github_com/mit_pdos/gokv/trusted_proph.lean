/-
Trusted code for gokv's `github.com/mit-pdos/gokv/trusted_proph` (v0.1.1), in namespace
`github_com.mit_pdos.gokv.trusted_proph` like the generated package
(`Code/github_com/mit_pdos/gokv/trusted_proph.toml`): Perennial's models, re-exported.

```go
func NewProph() ProphId { return primitive.NewProph() }
func ResolveBytes(p ProphId, b []byte) {}
```

`NewProph.impl` is GooseLang's `NewProph`, as primitive's `NewProph` is. `ResolveBytes.impl`
converts the slice to a string and resolves the prophecy `p` with it (`ResolveProph`): in Go it
does nothing, and a resolution has no effect on the execution, only on what the prophecy's owner
learns (the prophecy's values are the ones the execution resolves it with).
-/
module

public import Perennial.TrustedCode.github_com.mit_pdos.gokv.trusted_proph
