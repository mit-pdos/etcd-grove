/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/New.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__run

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

theorem New.wp_proof (wp_run : kv.KV.run.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro γr γn id n st send c0
  wp_start as ⟨#Hinv, Hdrv, %Hraft, %Hmd, Hncfg, %Hstor, #Hsrec, #Hc0, Hseq, #Hsend⟩
  wp_auto
  wp_apply wp_map_make1 (K := List w8) (V := List w8) as %mK HK
  wp_apply wp_map_make1 (K := List w8) (V := Bool) as %mA HA
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mW HW
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mR HRd
  iStructNamed «$r0»
  ipersist id
  ipersist node
  ipersist storage
  imod sync.init_Mutex (lockInv γr ⟨γn⟩ id «$r0_ptr») ⊤
    («$r0_ptr».[RKV, go!"mu"]) $$ mu [nextSeq waiters HW Hseq reads HRd] with #Hmu
  · inext
    unfold lockInv
    iexists W64 0, mW, ∅
    iframe waiters HW Hseq
    simp only [named]
    rw [show (W64 0 : w64) = 0 from rfl]
    iframe nextSeq
    isplitr
    · ipureintro; intro s ch Hs; cases Hs
    isplitr
    · iapply BigSepM.bigSepM_empty.2
      itrivial
    unfold readsOwn
    iexists mR, ∅
    simp only [named]
    iframe reads HRd
    isplitr
    · ipureintro; intro s ch Hs; cases Hs
    iapply BigSepM.bigSepM_empty.2
    itrivial
  unfold nodeDriver
  icases Hdrv with ⟨#HisNode, Hdlv, #Hdlb, Hreq⟩
  ihave #Hrep : isReplica γr ⟨γn⟩ «$r0_ptr» id n st $$ []
  · unfold isReplica
    simp only [named]
    iframe #
    ipureintro; exact ⟨Hraft, Hstor, Hmd.2.2.1⟩
  wp_apply wp_fork $$ [Hdlv Hreq kv HK applied HA Hncfg]
  · wp_apply wp_run γr ⟨γn⟩ «$r0_ptr» id n st send c0
      $$ [$Hpkg $Hrep Hdlv Hreq kv HK applied HA Hncfg]
    · iframe #
      isplitr
      · ipureintro; exact Hmd
      iframe Hncfg
      unfold nodeDriver
      iframe HisNode Hdlv Hdlb Hreq
      unfold runOwn
      iexists mK, ∅, mA, ∅, []
      simp only [named]
      iframe kv HK applied HA Hc0
      isplitl []
      · iapply BigSepL2.bigSepL2_nil.2; itrivial
      ipureintro
      refine ⟨?_, ?_⟩
      · intro k; simp [firstOcc, kvFold, kvEmpty]
      · intro d
        simp [firstOcc]
    itrivial
  iapply HΦ
  iexists ⟨γn⟩
  isplitr
  · ipureintro; rfl
  unfold isKV
  iexists id, n, st
  iexact Hrep

end proof

end kv
end EtcdGrove
end Perennial
