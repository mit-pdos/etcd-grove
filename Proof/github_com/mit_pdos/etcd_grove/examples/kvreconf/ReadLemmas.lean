/-
Lean-first (no Rocq counterpart).

# A read state's context (2026-10-29, track C)

`answer` matches a read state to the read waiting at the sequence number its context decodes to: a
read state's context was used (`readStateOk_used`), so minted (`MintOk`), at some `(replica, seq)`
as `readCtxB replica seq key`; it decodes back to that place (`decodeReadCtxB_readCtxB`), so a read
minted there has that context (`kvr_read_minted`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- A read's context decodes back. -/
theorem decodeReadCtxB_readCtxB (rp s : w64) (key : List w8) (hk : (key.length : Int) < 2 ^ 64) :
    decodeReadCtxB (readCtxB rp s key) = some (rp, s, key) := by
  unfold decodeReadCtxB readCtxB
  have hl : (u64Le rp).length = 8 := u64Le_length rp
  rw [if_pos (by simp [hl])]
  rw [List.drop_left' hl, decodeOp_encodeOp _ _ _ _ hk]
  simp only [if_true]
  rw [List.take_left' hl, u64Le_to_word]

end pure

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [StorageModel GF] [AllG GF]

/-- **A read state's context is the one minted where it decodes to** (see the file header). -/
theorem kvr_read_minted (γr : RNames) (c c0 : List w8) (i : w64) (rp s : w64) (key : List w8)
    (E : CoPset) (HE : ↑rkvN ⊆ E) (Hd : decodeReadCtxB c = some (rp, s, key)) :
    ⊢ rkvInv (GF := GF) γr -∗ readStateOk γr.cluster kvrRaftN c i -∗
      (rp, s) ↪[γr.rmint]□ c0 ={E}=∗ ⌜c0 = c⌝ := by
  unfold rkvInv rkvInvBody
  iintro #Hinv #Hok #Hmint
  iinv Hinv with ⟨%ops, %nn, %Mi, %RS, %RMi, %O, %U, >Hcore, Hslots⟩ Hclose
  iunfold kvCore at Hcore
  icases Hcore with ⟨Hops, Hval, Hrc, Hopn, HMi, HRS, HRMi, HO, %HMint, %HMod, %Hsh⟩
  ihave %HcU := readStateOk_used γr.cluster kvrRaftN c i U $$ [$Hok $Hrc]
  obtain ⟨⟨r1, s1⟩, Hk⟩ := HMint.2.2.2 c HcU
  obtain ⟨_, _, _, key1, Hkl, Hc⟩ := HMint.2.1 r1 s1 c Hk
  rw [Hc, decodeReadCtxB_readCtxB _ _ _ Hkl] at Hd
  cases Hd
  icases ghost_map_lookup $$ HRMi Hmint with %H0
  rw [Hk] at H0
  cases H0
  imod Hclose $$ [Hops Hval Hrc Hopn HMi HRS HRMi HO Hslots] with -
  · inext
    iexists ops, nn, Mi, RS, RMi, O, U
    iframe Hslots
    unfold kvCore
    iframe
    ipureintro; exact ⟨HMint, HMod, Hsh⟩
  imodintro
  ipureintro; rfl

end laws

end kvreconf
end EtcdGrove
end Perennial
