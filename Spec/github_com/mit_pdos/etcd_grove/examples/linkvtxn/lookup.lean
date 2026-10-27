/- Lean-first (no Rocq counterpart).

`lookup(kvs, k)` (linkvtxn.go): `k`'s first entry's value in `kvs`, and whether there is one
(`lookupL`).
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
abbrev lookup.spec : Prop :=
  ∀ (sl : GoSlice) (es : List entry) (dq : DFrac) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗ sl ↦*{dq} es }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.lookup')) (Val #sl)) (Val #k))
  {{ (v : VR) (ok : Bool), RET (PairV #v #ok); sl ↦*{dq} es ∗ ⌜(v, ok) = lookupL es k⌝ }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
