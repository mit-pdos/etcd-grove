/-
`SplitMetaNamespaceKey(key)` (`store.go:188`): the namespace and name a store key encodes. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.Keys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- `SplitMetaNamespaceKey(key)`: `splitKey key` (the parts around `/` when there are one or two:
`splitKey_nameKey`), or `""`, `""` and an error. -/
abbrev SplitMetaNamespaceKey.spec : Prop :=
  ∀ (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache }}
    (App (Val (@! SplitMetaNamespaceKey)) (Val #key))
  {{ (ns name : GoString) (err : GoInterface), RET (PairV (PairV #ns #name) #err);
      ⌜match splitKey key with
        | some (a, b) => ns = a ∧ name = b ∧ err = interface.nil
        | none => ns = [] ∧ name = [] ∧ err ≠ interface.nil⌝ }}

end spec

end cache
end EtcdGrove
end Perennial
