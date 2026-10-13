/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/New.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem New.wp_proof (wp_run : register.Register.run.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro γr γn id n st send
  wp_start as ⟨#Hinv, Hdrv, %Hraft, %Hstor, #Hsrec, #Hc0, Hseq, #Hsend⟩
  wp_auto
  wp_apply wp_map_make1 (K := List w8) (V := Bool) as %mA HA
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mW HW
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mR HRd
  iStructNamed «$r0»
  ipersist id
  ipersist node
  ipersist storage
  obtain ⟨N, hN⟩ : ∃ N : Nat, N = 2 ^ 64 - 1 := ⟨_, rfl⟩
  rw [← hN]
  imod own_alloc ((● N : Auth Nat) • ◯ N)
    (Auth.auth_both_valid_discrete.mpr ⟨⟨0, (Nat.add_zero _).symm⟩, trivial⟩) with ⟨%γc, HC⟩
  icases (own_op γc _ _).1 $$ HC with ⟨HCa, HCf⟩
  imod sync.init_Mutex (lockInv γr ⟨γn, γc⟩ id «$r0_ptr») ⊤
    («$r0_ptr».[RRegister, go!"mu"]) $$ mu [nextSeq waiters HW Hseq HCa reads HRd] with #Hmu
  · inext
    unfold lockInv
    iexists W64 0, mW, ∅, N
    iframe waiters HW Hseq HCa
    simp only [named]
    rw [show (W64 0 : w64) = 0 from rfl]
    iframe nextSeq
    isplitr
    · ipureintro; rw [hN]; word
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
  icases Hdrv with ⟨#HisNode, Hdlv⟩
  ihave #Hrep : isReplica γr ⟨γn, γc⟩ «$r0_ptr» id n st $$ []
  · unfold isReplica
    simp only [named]
    iframe #
    ipureintro; exact ⟨Hraft, Hstor⟩
  wp_apply wp_fork $$ [Hdlv value applied HA]
  · wp_apply wp_run γr ⟨γn, γc⟩ «$r0_ptr» id n st send $$ [$Hpkg $Hrep Hdlv value applied HA]
    · iframe #
      unfold nodeDriver
      iframe HisNode Hdlv
      unfold runOwn
      iexists [], mA, ∅, []
      simp only [named]
      iframe value applied HA Hc0
      isplitl []
      · iapply BigSepL2.bigSepL2_nil.2; itrivial
      ipureintro
      refine ⟨rfl, ?_⟩
      intro d
      simp [firstOcc]
    itrivial
  iapply HΦ
  iexists ⟨γn, γc⟩
  isplitr
  · ipureintro; rfl
  unfold opCred
  iframe HCf
  unfold isRegister
  iexists id, n, st
  iexact Hrep

end proof

end register
end EtcdGrove
end Perennial
