/- Lean-first (no Rocq counterpart).

`put(kvs, r, k, v)` (linkvtxn.go): a new slice, `kvs` after a put of `k` with `v` at revision
`r` (`putL`: the key's version one more, `1` for a new key). Its premise is `setKey`'s.
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
abbrev put.spec : Prop :=
  ∀ (sl : GoSlice) (es : List entry) (dq : DFrac) (r : w64) (k v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗ sl ↦*{dq} es ∗ ⌜es.length + 1 < 2 ^ 63⌝ }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.put)) (Val #sl)) (Val #r)) (Val #k)) (Val #v))
  {{ (out : GoSlice), RET #out;
      sl ↦*{dq} es ∗ out ↦* putL es r k v ∗ ownSliceCap entry out (DFrac.own 1) }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
