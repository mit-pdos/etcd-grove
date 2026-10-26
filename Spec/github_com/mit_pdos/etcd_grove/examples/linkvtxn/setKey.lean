/- Lean-first (no Rocq counterpart).

`setKey(kvs, k, r)` (linkvtxn.go): a new slice, the store `kvs` with `k ↦ r` (`setKeyL`). Its
premise bounds `kvs`'s length: `make([]entry, 0, len(kvs)+1)` panics in Perennial's model when
`len(kvs) + 1` overflows (as `linkv`'s `set`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev setKey.spec : Prop :=
  ∀ (sl : GoSlice) (es : List entry) (dq : DFrac) (k : GoString) (r : VR),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗ sl ↦*{dq} es ∗ ⌜es.length + 1 < 2 ^ 63⌝ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.setKey)) (Val #sl)) (Val #k)) (Val #r))
  {{ (out : GoSlice), RET #out;
      sl ↦*{dq} es ∗ out ↦* setKeyL es k r ∗ ownSliceCap entry out (DFrac.own 1) }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
