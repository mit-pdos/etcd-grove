/- Lean-first (no Rocq counterpart).

`objOut(o)` (k8setcd3.go): `objOutL`.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev objOut.spec : Prop :=
  ∀ (o : Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.objOut)) (Val #o))
  {{ RET #(objOutL o); True }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
