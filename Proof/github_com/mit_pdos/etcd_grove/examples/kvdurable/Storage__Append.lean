/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Storage__Append.lean`. Lean-first
(no Rocq counterpart): the image's append, then the `MemoryStorage`'s (its triple, the premise).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__Append
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.image__append

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

theorem Storage.Append.wp_proof (wp_append : image.append.spec (GF := GF) (hG := hG)) :
    Storage.Append.spec (GF := GF) (hG := hG) := by
  intro s ms γs ip I sl dq k es P Q Hidx Hk Hb Hms
  wp_start as ⟨#Hrec, #Himg, HI, Hes, HP⟩
  iunfold kdStorRec at Hrec
  icases Hrec with ⟨#Hmsf, -⟩
  wp_auto
  wp_apply wp_append ip I sl dq k es Hidx Hk Hb $$ [$HI $Hes] as ⟨HI, Hes⟩
  wp_apply Hms $$ [$HP $Hes] as ⟨Hes, HQ⟩
  iapply HΦ
  iframe Hes HQ HI

end proof

end kvdurable
end EtcdGrove
end Perennial
