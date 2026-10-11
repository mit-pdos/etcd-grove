/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/newSequentialKV.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newSequentialKV
public import Spec.go_etcd_io.etcd.client.v3.WithLastKey
public import Spec.go_etcd_io.etcd.client.v3.ModRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Spec.context.TODO

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem newSequentialKV.wp_proof (hWLK : EtcdGrove.WithLastKey.spec (GF := GF) (hG := hG))
    (hMR : EtcdGrove.ModRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hPut : EtcdGrove.OpPut.spec (GF := GF) (hG := hG))
    (hTODO : EtcdGrove.context.TODO.spec (GF := GF) (hG := hG)) :
    newSequentialKV.spec (GF := GF) (hG := hG) := by
  sorry -- unit 1b: needs Perennial's strings.Split / errors.Is / Sprintf integer models

end proof

end recipes
end EtcdGrove
end Perennial
