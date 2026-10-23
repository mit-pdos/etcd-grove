/-
Lean-first (no Rocq counterpart).

# `k8s.io/apiserver/pkg/storage`: shared definitions (`notes/k8s-etcd3-plan.md`)

- `prepareKeyM`: `PrepareKey(resourcePrefix, key, recursive)` as a function: the key, with a
  trailing `/` if recursive, or none if it has a `.` or `..` segment, is empty or `/`, or lacks
  the resource prefix.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

/-- `key` has a `..` segment (`PrepareKey`'s first test). -/
def dotDot (key : GoString) : Bool :=
  decide (key = go!".." ∨ go!"../" <+: key ∨ go!"/.." <:+ key ∨ go!"/../" <:+: key)

/-- `key` has a `.` segment (`PrepareKey`'s second test). -/
def dotSeg (key : GoString) : Bool :=
  decide (key = go!"." ∨ go!"./" <+: key ∨ go!"/." <:+ key ∨ go!"/./" <:+: key)

/-- **`PrepareKey(resourcePrefix, key, recursive)`** (`storage/interfaces.go`): the key, made a
directory (a trailing `/`) if recursive, if it has no `.` or `..` segment, is neither empty nor
`/`, and has the resource prefix; else none (an error). -/
def prepareKeyM (rp key : GoString) (r : Bool) : Option GoString :=
  if dotDot key then none
  else if dotSeg key then none
  else if key = [] ∨ key = go!"/" then none
  else
    let k := if r = true ∧ ¬ go!"/" <:+ key then key ++ go!"/" else key
    if rp <+: k then some k else none

end k8s
end EtcdGrove
end Perennial
