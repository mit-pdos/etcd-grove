/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/updateLastAppended.lean (241f27e).
-/
/-
The proof of `updateLastAppended` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.updateLastAppended
public import Dsverify.Spec.github_com.hashicorp.raft.commitment__match
public import Dsverify.Proof.github_com.hashicorp.raft.ReplNotify

@[expose] public section

set_option linter.unusedVariables false
set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot proto

theorem github_com.hashicorp.raft.updateLastAppended.wp_proof
    (wp_StoreUint64 : sync.atomic.StoreUint64.spec (GF := GF) (hG := hG))
    (wp_match : github_com.hashicorp.raft.commitment.match.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.updateLastAppended.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j s req rq snd prev pt ents lci dq => by
  wp_start as ⟨#Hs, Hnext, Hreq, #Hbody, #Hack⟩
  ihave ⟨-, ⟨%psf, #Hpeer⟩, -, -, ⟨%cm, #Hcm, #Hcmi⟩, -⟩ := replShared_core r γ i T j s $$ Hs
  ihave #Hcell := replShared_nextCell r γ rc i T j s $$ Hs
  unfold aeBody entPtrs
  icases Hbody with ⟨%Hrq, -, -, %ptrs, #Hptrs, %Hplen, #Hents⟩
  ihave ⟨HE, Hback⟩ := (AccessStrict.access_strict
    (self := github_com.hashicorp.raft.AppendEntriesRequest.AppendEntriesRequest_access_load_Entries req rq dq)) $$ Hreq
  wp_auto
  ihave Hreq := Hback $$ HE
  ihave %Hsl := ownSlice_len $$ Hptrs
  wp_if_destruct
  · have hn : 0 < ptrs.length := by word
    list_elem ptrs (ptrs.length - 1) as p
    rw [if_pos (show 0 ≤ sint.Z (rq.Entries'.len - W64 1) ∧ sint.Z (rq.Entries'.len - W64 1) < sint.Z rq.Entries'.len by word)]
    wp_apply (wp_load_slice_index rq.Entries' (sint.Z (rq.Entries'.len - W64 1)) ptrs DFrac.discard p (by word))
      $$ [Hptrs]
    · iframe #; ipureintro
      have : (sint.Z (rq.Entries'.len - W64 1)).toNat = ptrs.length - 1 := by word
      rw [this]; exact Hp_lookup
    iintro -
    ihave ⟨%e, %He, #Hlp⟩ := BigSepL.bigSepL_lookup (Φ := fun j p => iprop(∃ e, ⌜ents[j]? = some e⌝ ∗ logPtr (GF := GF) p (prev + 1 + j) e)) Hp_lookup $$ Hents
    unfold logPtr
    icases Hlp with ⟨%lv, #Hlv, #His⟩
    ihave %Hlvf := logIs_pure $$ His
    ihave Hlv2 := Hlv
    iStructNamed Hlv2
    unfold nextHalf
    icases Hnext with ⟨%nv, Hnext⟩
    wp_auto
    wp_apply (wp_storeUint64_cell wp_StoreUint64 s nv (lv.Index' + W64 1)) $$ [Hnext] as Hnext
    · iframe; iframe #
    ihave Hpeer2 := Hpeer
    iStructNamed Hpeer2
    wp_auto
    wp_apply wp_match $$ [$Hcmi]
    · icases Hack with (%Hnil | #Hack)
      · exfalso
        have h0 : ptrs.length = 0 := by rw [Hplen, Hnil]; rfl
        omega
      iright
      have : uint.nat lv.Index' = prev + ents.length := by rw [Hlvf.1]; omega
      rw [this]
      ileft; iexact Hack
    iapply HΦ
    iframe
  iapply HΦ
  iframe

end proof

end Perennial
