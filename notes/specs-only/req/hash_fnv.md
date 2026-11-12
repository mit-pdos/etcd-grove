# Requirements on `hash/fnv` (this repository's translation; trust boundary or proved)

## from 4d

`Meta.Sum64` (`internal/common/meta.go:61-65`) hashes the meta's first 56 bytes:

```go
var h = fnv.New64a()
_, _ = h.Write((*[unsafe.Offsetof(Meta{}.checksum)]byte)(unsafe.Pointer(m))[:])
return h.Sum64()
```

Needed: specs of `New64a()` (a fresh hasher, as a `hash.Hash64` interface value, with the empty
input), `Write(b)` on it (appends `b`'s bytes, read at any share; returns `(len(b), nil)`) and
`Sum64()` (returns FNV-1a 64 of the bytes written: `BboltCommon.fnv64a`, offset basis
`14695981039346656037`, prime `1099511628211`, XOR then multiply). The old proof had these
(`specs-ref/Spec/hash/fnv/`, proved from the translated bodies). Used by: `Meta.Sum64.spec`, hence
`Meta.Validate.spec`, `Meta.Write.spec`.
