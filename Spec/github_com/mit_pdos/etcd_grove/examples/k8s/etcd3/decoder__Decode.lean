/- Lean-first (no Rocq counterpart).

`decoder{}.Decode(data, objPtr, rev)` (k8s_etcd3.go) into a `*Obj`: the object the data decodes to
(`decodeD`), at the resource version `rev`; else `errBadData`, the object unchanged.
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
abbrev decoder.Decode.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (d : GoString) (p : Loc) (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ sl ↦*{dq} d ∗ p ↦ v }}
    (App (App (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decoder.ty go!"Decode" #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decoder.mk))) (Val #sl)) (Val #(interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #p))) (Val #rev))
  {{ (err : GoInterface), RET #err; sl ↦*{dq} d ∗
      match decodeD d with
      | some w => ⌜err = GoInterface.nil⌝ ∗ p ↦ { w with ResourceVersion' := rev }
      | none => ⌜err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.errStrOk err ∗
          p ↦ v }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
