/- Lean-first (no Rocq counterpart).

`notFound(st, key)` (k8setcd3.go): `notFoundL` at the store's resource version.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev notFound.spec : Prop :=
  ∀ (s : mstore) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.notFound)) (Val #s)) (Val #key))
  {{ RET #(notFoundL s.rv' key); True }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
