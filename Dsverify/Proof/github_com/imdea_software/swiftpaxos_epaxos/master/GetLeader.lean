/-
`m.GetLeader(args, reply)` (`masterGetLeader.spec`, `NetRpc/Specs.lean`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [master.Assumptions] [examples.epaxosnet.Assumptions] [epaxos.Assumptions]

set_option goose.wp.extras true in
open replica.defs in
theorem masterGetLeader.wp_proof (γ : EpNames) : masterGetLeader.spec (GF := GF) (isMaster γ) := by
  intro m pa pr
  wp_start as ⟨#Hm, Hpa, Hpr⟩
  unfold isMaster
  icases Hm with ⟨#Hpkg, %mu, %cfg, %logger, %ic, %c, #Hlock, #Hmu, #Hic, #Hcond, #HN, #Hcfgf, #Hcfg, %Hld, #Hlogf, #Hlog⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  unfold masterLockInv
  icases Hinv with ⟨%ks, %nl, %al, %pl, %ldsl, %alsl, %latsl, %ld, %alv, %lat, %fi, %Hks, Hlists, #Hldf, Hld, #Half, Halv, #Hlatf, Hlat, Hfi⟩
  wp_auto
  ihave %Hldl := ownSlice_len _ _ _ $$ Hld
  rename_i key_ptr
  irename : (key_ptr ↦ (zero_val w64) : IProp GF) => Hkey
  ihave HI : (∃ (iw kv : w64) (lv : Bool) (x : w64), "i" ∷ i_ptr ↦ iw ∗
      "Hkey" ∷ key_ptr ↦ kv ∗ "l" ∷ l_ptr ↦ lv ∗ "Hpr" ∷ pr ↦ GetLeaderReply.mk x ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iw ∧ sint.Z iw ≤ sint.Z ldsl.len⌝ : IProp GF)
      $$ [i Hkey l Hpr]
  · iexists _, _, _, _; iframe; ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · list_elem ld (sint.nat iw) as x0
    rw [ite_eq_left (show 0 ≤ sint.Z iw ∧ sint.Z iw < sint.Z ldsl.len by word)]
    wp_apply wp_load_slice_index ldsl (sint.Z iw) _ _ x0 (by word) $$ [$Hld] as Hld
    · ipureintro; simpa [sint.nat] using Hx0_lookup
    wp_if_destruct
    · wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro; constructor <;> word
    · wp_for_post
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hld Halv Hlat Hfi]
      · iexists ks, nl, al, pl, ldsl, alsl, latsl, ld, alv, lat, fi
        inext
        iframe
        iframe Hldf Half Hlatf
        ipureintro; exact Hks
      iapply HΦ
      iexists _; iexact Hpr
  · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hld Halv Hlat Hfi]
    · iexists ks, nl, al, pl, ldsl, alsl, latsl, ld, alv, lat, fi
      inext
      iframe
      iframe Hldf Half Hlatf
      ipureintro; exact Hks
    iapply HΦ
    iexists _; iexact Hpr

end proof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
