/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/New.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.New
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.newKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [KVStor GF]

theorem New.wp_proof (wp_newKV : kvwitness.newKV.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro γr γn id n st send op c0 c1
  wp_start as ⟨Hinv, Hdrv, %Hraft, %Hmd, Hncfg, %Hstor, #Hsrec, #Hc0, Hseq, #Hsend⟩
  wp_auto
  wp_apply wp_newKV γr γn id n st send op c0 c1 interface.nil
      $$ [$Hpkg $Hinv $Hdrv $Hncfg $Hsrec $Hc0 $Hseq $Hsend]
    as %r Hr
  · isplitr
    · ipureintro; exact Hraft
    isplitr
    · ipureintro; exact .inl Hmd
    isplitr
    · ipureintro; exact Hstor
    unfold kvWitRes; ileft; ipureintro; rfl
  iapply HΦ $$ Hr

end proof

end kvwitness
end EtcdGrove
end Perennial
