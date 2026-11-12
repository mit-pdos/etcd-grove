/-
`runtime.Encode(e, obj)` (`k8s.io/apimachinery/pkg/runtime/codec.go`; translated with its body,
stage 6c of `notes/k8s-etcd3-plan.md`) of an encoder whose `Encode(obj, w)`, on a fresh
`*bytes.Buffer`, appends the bytes `bs` and returns no error (`P` its precondition, `Q` what it
leaves): those bytes, no error. Lean-first (no Rocq counterpart).
-/
module

public import Proof.bytes.Buffer
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI bufferM

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.runtime.Assumptions]

/-- See the file header. -/
abbrev runtime.Encode.spec : Prop :=
  ∀ (ei : GoInterfaceOk) (x : GoInterface) (P Q : IProp GF) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime ∗ P ∗
      (∀ (b : Loc) (Ψ : val → IProp GF), P -∗ ownBuffer b [] -∗
        ▷ (ownBuffer b bs ∗ Q -∗ Ψ #GoInterface.nil) -∗
        WP (App (App (Val #(methods ei.ty go!"Encode" ei.v)) (Val #x))
          (Val #(interface.mkOk (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty) #b)))
          {{ Ψ }}) }}
    (App (App (Val (@! k8s_io.apimachinery.pkg.runtime.Encode)) (Val #(GoInterface.ok ei)))
      (Val #x))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      ⌜err = GoInterface.nil⌝ ∗ sl ↦* bs ∗ Q }}

end spec

end EtcdGrove
end Perennial
