/- Lean-first (no Rocq counterpart).

`(codec).Decode(data, nil, nil)` (k8setcd3.go; stage E of 7f-6: `runtime.Decode`'s, the watch path's
`decodeObj`): no object to decode into, so a fresh `*Obj` of the data's object at resource version
`0`, or `errBadData` if the data does not decode.
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
abbrev codec.Decode.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (d : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ sl ↦*{dq} d }}
    (App (App (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.codec.ty go!"Decode" #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.codec.mk))) (Val #sl)) (Val #null)) (Val #(interface.nil : GoInterface)))
  {{ (x : GoInterface) (g : Loc) (err : GoInterface), RET (PairV (PairV #x #g) #err); sl ↦*{dq} d ∗
      match decodeD d with
      | some w => ⌜err = GoInterface.nil⌝ ∗ ∃ p : Loc,
          ⌜x = interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #p⌝ ∗
          p ↦ { w with ResourceVersion' := W64 0 }
      | none => ⌜err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.errStrOk err }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
