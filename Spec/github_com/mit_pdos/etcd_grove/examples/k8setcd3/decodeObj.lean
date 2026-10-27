/- Lean-first (no Rocq counterpart).

`decodeObj(data)` (k8setcd3.go): either tag's encoding back (`decodeD`): the name and value, and
whether the data decoded.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev decodeObj.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (d : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗
      sl ↦*{dq} d }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.decodeObj)) (Val #sl))
  {{ (name val : GoString) (ok : Bool), RET (PairV (PairV #name #val) #ok);
      sl ↦*{dq} d ∗
      ⌜match decodeD d with
        | some (n, v) => ok = true ∧ name = n ∧ val = v
        | none => ok = false⌝ }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
