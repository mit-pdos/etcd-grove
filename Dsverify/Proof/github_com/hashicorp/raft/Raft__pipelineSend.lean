/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__pipelineSend.lean (241f27e).
-/
/-
The proof of `Raft__pipelineSend` (replication subsystem, stage 2).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__pipelineSend
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setupAppendEntries
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
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

theorem github_com.hashicorp.raft.Raft.pipelineSend.wp_proof
    (wp_StoreUint64 : sync.atomic.StoreUint64.spec (GF := GF) (hG := hG))
    (wp_setupAppendEntries : github_com.hashicorp.raft.Raft.setupAppendEntries.spec (GF := GF) (hG := hG))
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.pipelineSend.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j s pI nxt lastIndex tid => by
  wp_start as ⟨#Hr, #Hs, #Hl, #Hlb, #Hp, ⟨%nv, Hn⟩, Htok⟩
  ihave ⟨#HInv, -⟩ := isRaft_proto r γ rc i $$ Hr
  ihave ⟨#HcurT, -⟩ := replShared_core r γ i T j s $$ Hs
  wp_auto
  wp_apply (wp_setupAppendEntries r γ rc i T j s _ (Perennial.zero_val AppendEntriesRequest)) $$ [$Hr $Hs $Hl $Hlb $Htok «$r0»] as %err ⟨Htok, %rq', req, Hres⟩
  · iframe
  icases Hres with (⟨%Herr, %c, #Hce⟩ | ⟨%Herr, %prev, %pt, %ents, %lci, #Hbody, #Hvalid⟩)
  · -- setupAppendEntries failed: stop
    ihave ⟨%x, %Hx⟩ := isRaftErr_ptr c err $$ Hce
    subst Hx
    wp_auto
    iapply HΦ
    iframe
  subst Herr
  wp_auto
  ihave #Htc := isRaft_termCell r γ rc i $$ Hr
  ihave #Hdur := isRaft_durInv r γ rc i $$ Hr
  icases Hvalid with (#Hvalid | #Hstale)
  rotate_left
  · -- some read was of a later term: the term check stops
    wp_apply wp_getCurrentTerm.2 $$ [$Htc $Hdur $Hstale] as %t ⟨#Hlbt, %Ht⟩
    wp_if_destruct
    · exfalso
      have h1 : uint.nat (W64 (T : Int)) ≤ T := by word
      omega
    · iapply HΦ
      iframe
  -- every read was of term `T`: the request is valid
  wp_apply wp_getCurrentTerm.2 $$ [$Htc $Hdur $Hlb] as %t ⟨#Hlbt, %Ht⟩
  wp_if_destruct
  rotate_left
  · -- the term moved on: stop
    iapply HΦ
    iframe
  have hT : T < 2 ^ 64 := by
    have h1 : uint.nat (W64 (T : Int)) ≤ T := by word
    have h2 : uint.nat (W64 (T : Int)) < 2 ^ 64 := by word
    omega
  ihave Hds : iprop([∗list] p ∈ ([] : List (SID × Nat)), durLb (GF := GF) γ p.1 p.2) $$ []
  · iapply BigSepL.bigSepL_nil.2; iempintro
  ihave HS : iprop([∗list] s0 ∈ ([] : List Snap), histLb (GF := GF) γ s0) $$ []
  · iapply BigSepL.bigSepL_nil.2; iempintro
  imod histLb_now γ ⊤ (by solve_ndisj) [] [] (by simp) $$ [HInv HS Hds] with ⟨%ss, #Hss, -⟩
  · iframe #; iframe
  ihave #Haer := aeReq_intro γ rq' i T prev pt ents lci ss hT $$ [$Hbody $Hvalid $Hss]
  ipersist req
  unfold isPipeline
  icases Hp with ⟨#HAE, -, -⟩
  wp_bind (App (App (Val #(methods pI.ty _ pI.v)) _) _)
  iapply HAE $$ req Haer «$a1»
  · ipureintro; rfl
  iintro %fi %err Herr
  icases Herr with (%Herr | #Herro)
  rotate_left
  · -- the pipeline is closed: stop
    ihave %Hne := errOk_ne_nil err $$ Herro
    cases err with
    | nil => exact absurd rfl Hne
    | ok e =>
    wp_auto
    iapply HΦ
    iframe
  subst Herr
  wp_auto
  -- the next send starts after the entries just sent
  unfold aeBody entPtrs
  icases Hbody with ⟨%Hrq, -, -, %ptrs, #Hptrs, %Hplen, #Hents⟩
  ihave %Hsl := ownSlice_len $$ Hptrs
  ihave ⟨#HE, -⟩ := (AccessStrict.access_strict
    (self := github_com.hashicorp.raft.AppendEntriesRequest.AppendEntriesRequest_access_load_Entries _ rq' DFrac.discard)) $$ req
  wp_auto
  wp_if_destruct
  · have hn : 0 < ptrs.length := by word
    list_elem ptrs (ptrs.length - 1) as p
    rw [if_pos (show 0 ≤ sint.Z (rq'.Entries'.len - W64 1) ∧ sint.Z (rq'.Entries'.len - W64 1) < sint.Z rq'.Entries'.len by word)]
    wp_apply (wp_load_slice_index rq'.Entries' (sint.Z (rq'.Entries'.len - W64 1)) ptrs DFrac.discard p (by word))
      $$ [Hptrs]
    · iframe #; ipureintro
      have : (sint.Z (rq'.Entries'.len - W64 1)).toNat = ptrs.length - 1 := by word
      rw [this]; exact Hp_lookup
    iintro -
    ihave ⟨%e, %He, #Hlp⟩ := BigSepL.bigSepL_lookup (Φ := fun j p => iprop(∃ e, ⌜ents[j]? = some e⌝ ∗ logPtr (GF := GF) p (prev + 1 + j) e)) Hp_lookup $$ Hents
    unfold logPtr
    icases Hlp with ⟨%lv, #Hlv, #His⟩
    ihave Hlv2 := Hlv
    iStructNamed Hlv2
    wp_auto
    wp_apply (wp_storeUint64_own wp_StoreUint64 nxt nv (lv.Index' + W64 1)) $$ [Hn] as Hn
    · iframe
    iapply HΦ
    iframe
  iapply HΦ
  iframe

end proof

end Perennial
