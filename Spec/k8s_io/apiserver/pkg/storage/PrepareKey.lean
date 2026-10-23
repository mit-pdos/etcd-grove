/-
`storage.PrepareKey(resourcePrefix, key, recursive)` (`k8s.io/apiserver/pkg/storage/interfaces.go`):
`prepareKeyM`'s key, or an error. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- See the file header. -/
abbrev storage.PrepareKey.spec : Prop :=
  ∀ (rp key : GoString) (r : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage }}
    (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.PrepareKey)) (Val #rp)) (Val #key))
      (Val #r))
  {{ (k : GoString) (err : GoInterface), RET (PairV #k #err);
      ⌜match k8s.prepareKeyM rp key r with
        | some k' => k = k' ∧ err = GoInterface.nil
        | none => err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
