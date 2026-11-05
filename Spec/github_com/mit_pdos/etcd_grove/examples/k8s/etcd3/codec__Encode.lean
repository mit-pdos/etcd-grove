/- Lean-first (no Rocq counterpart).

`codec{}.Encode(obj, w)` (k8s_etcd3.go) of a `*Obj` and a `*bytes.Buffer` writer: it appends the
object's current encoding to the buffer (`bytes.Buffer`'s trust boundary, `Proof/bytes/Buffer.lean`)
and returns no error.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Codec
public import Proof.bytes.Buffer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI bufferM

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev codec.Encode.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (name val : GoString) (rv : w64) (b : Loc) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      p ↦{dq} github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk name val rv ∗
      ownBuffer b bs }}
    (App (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.codec.ty go!"Encode"
        #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.codec.mk)))
      (Val #(interface.mkOk (go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #p)))
      (Val #(interface.mkOk (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty) #b)))
  {{ RET #GoInterface.nil;
      p ↦{dq} github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk name val rv ∗
      ownBuffer b (bs ++ encodeWith tagV1 name val) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
