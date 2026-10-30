/-
The model of `hash/fnv`'s 64-bit FNV-1a hash, which bbolt's meta checksum uses
(`Meta.Sum64`). Perennial translates `hash/fnv` names-only, so the functions bbolt calls
(`New64a`, and `Write` and `Sum64` of the `hash.Hash64` it returns) have no semantics, and
their specs (`Spec/hash/fnv/`) are axioms (the trust boundary; `etc/tcb-report.py` lists
them). The Go code is six lines (`var s sum64a = offset64; return &s`; `Write`: for each
byte, `hash ^= sum64a(c); hash *= prime64`; `Sum64`: `uint64(*s)`) and could be translated
with bodies and proved instead.

`fnvHash t v bs`: the `hash.Hash64` with dynamic type `t` and value `v` has hashed the bytes
`bs` (abstract state).
-/
module

public import Perennial.Golang.Theory.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

/-- FNV-1a's 64-bit offset basis. -/
def fnvOffset64 : w64 := BitVec.ofNat 64 14695981039346656037
/-- FNV-1a's 64-bit prime. -/
def fnvPrime64 : w64 := BitVec.ofNat 64 1099511628211

/-- FNV-1a of `bs` from the state `h`: for each byte, xor it in, then multiply by the
prime. -/
def fnv64aFrom (h : w64) (bs : List w8) : w64 :=
  bs.foldl (fun h b => (h ^^^ b.setWidth 64) * fnvPrime64) h

/-- The 64-bit FNV-1a hash of `bs`. -/
def fnv64a (bs : List w8) : w64 := fnv64aFrom fnvOffset64 bs

section model
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

axiom fnvHash (t : go.GoType) (v : val) (bs : List w8) : IProp GF

end model

end bbolt
end EtcdGrove
end Perennial
