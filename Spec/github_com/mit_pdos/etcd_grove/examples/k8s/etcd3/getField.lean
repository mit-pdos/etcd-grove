/- Lean-first (no Rocq counterpart).

`getField(data, i)` (k8setcd3.go), at a small index `i` (below `2^16`: no overflow; `decodeObj`'s
are below `3 + 5 * 256`): the length-prefixed field at
`i` and the index after it (`getFieldD`), or `false`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev getField.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (d : GoString) (i : w64),
  0 ≤ sint.Z i → sint.Z i < 2 ^ 16 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ sl ↦*{dq} d }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getField)) (Val #sl)) (Val #i))
  {{ (f : GoString) (j : w64) (ok : Bool), RET (PairV (PairV #f #j) #ok); sl ↦*{dq} d ∗
      ⌜match getFieldD d (sint.nat i) with
        | some (f', j') => ok = true ∧ f = f' ∧ sint.Z j = (j' : Int)
        | none => ok = false⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
