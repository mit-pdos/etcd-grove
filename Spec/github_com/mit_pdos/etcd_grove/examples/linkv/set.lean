/- Lean-first (no Rocq counterpart).

`set(kv, k, v)` (linkv.go): a new slice, the store `kv` with `k ↦ v` (`setL`; `absStore_setL`:
it writes the store). Its premise bounds `kv`'s length: `make([]kvEntry, 0, len(kv)+1)` panics
in Perennial's model when `len(kv) + 1` overflows (Go's memory bounds a slice of 32-byte entries
far below; Perennial's model does not, see `notes/STATUS.md`, D20).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- See the file header. -/
abbrev set.spec : Prop :=
  ∀ (sl : GoSlice) (es : List kvEntry) (dq : DFrac) (k v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv ∗
      sl ↦*{dq} es ∗ ⌜es.length + 1 < 2 ^ 63⌝ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv.set)) (Val #sl)) (Val #k))
      (Val #v))
  {{ (out : GoSlice), RET #out;
      sl ↦*{dq} es ∗ out ↦* setL es k v ∗ ownSliceCap kvEntry out (DFrac.own 1) }}

end spec

end linkv
end EtcdGrove
end Perennial
