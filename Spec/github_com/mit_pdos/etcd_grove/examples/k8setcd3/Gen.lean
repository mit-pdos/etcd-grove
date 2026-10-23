/- Lean-first (no Rocq counterpart).

`Gen(id)` (k8setcd3.go): `genFrom` of a random number, boxed: `Apply`'s input (`kInOk`), as `lintest.genSpec` takes it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Calls

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
abbrev Gen.spec : Prop :=
  ⊢ lintest.genSpec (GF := GF) (functions github_com.mit_pdos.etcd_grove.examples.k8setcd3.Gen []) kInOk

end spec

end k8setcd3
end EtcdGrove
end Perennial
