/-
`(*store).prepareKey(key, recursive)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go`):
`PrepareKey(s.resourcePrefix, key, recursive)` under `s.pathPrefix`, or its error. Lean-first (no
Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev store.prepareKey.spec : Prop :=
  ∀ (sp : Loc) (rp pp key : GoString) (r : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"resourcePrefix" sp ↦□ rp ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"pathPrefix" sp ↦□ pp }}
    (App (App (Val (sp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty @!!
      go!"prepareKey")) (Val #key)) (Val #r))
  {{ (k : GoString) (err : GoInterface), RET (PairV #k #err);
      ⌜match prepareKeyM rp key r with
        | some k' => k = pp ++ k' ∧ err = GoInterface.nil
        | none => err ≠ GoInterface.nil⌝ }}

end spec

end k8s
end EtcdGrove
end Perennial
