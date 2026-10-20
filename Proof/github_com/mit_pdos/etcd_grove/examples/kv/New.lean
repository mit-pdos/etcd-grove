/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/New.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.newKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

theorem New.wp_proof (wp_newKV : kv.newKV.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro γr γn id n st send op c0 c1
  wp_start as Hpre
  wp_auto
  wp_apply wp_newKV γr γn id n st send op c0 c1 $$ [$Hpkg $Hpre] as %r Hr
  iapply HΦ $$ Hr

end proof

end kv
end EtcdGrove
end Perennial
