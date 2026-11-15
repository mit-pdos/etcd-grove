/- Lean-first (no Rocq counterpart).

`putField(out, f)` (k8setcd3.go): `out` with `f`'s length byte and bytes appended (`putF`); the
slice's capacity is passed along.
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
abbrev putField.spec : Prop :=
  ∀ (sl : GoSlice) (out f : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      sl ↦* out ∗ ownSliceCap w8 sl (DFrac.own 1) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.putField)) (Val #sl)) (Val #f))
  {{ (sl' : GoSlice), RET #sl'; sl' ↦* putF out f ∗ ownSliceCap w8 sl' (DFrac.own 1) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
