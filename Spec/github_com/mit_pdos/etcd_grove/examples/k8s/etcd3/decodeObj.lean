/- Lean-first (no Rocq counterpart).

`decodeObj(data)` (k8setcd3.go): either tag's encoding back (`decodeD`: the object's fields, its
resource version `0`), and whether the data decoded.
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
abbrev decodeObj.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (d : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      sl ↦*{dq} d }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeObj)) (Val #sl))
  {{ (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj) (ok : Bool), RET (PairV #v #ok);
      sl ↦*{dq} d ∗
      ⌜match decodeD d with
        | some w => ok = true ∧ v = w
        | none => ok = false⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
