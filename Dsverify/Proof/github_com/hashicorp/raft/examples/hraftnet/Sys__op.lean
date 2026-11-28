/-
`hraftnet.Sys.op`'s proof (notes/dsv-hraft.md, S5f): the count moved, the command built, its id
reserved (`id_reserve`, `idOf_cmdB`), then `try` at the servers in turn with the operation's state.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Sys__op
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Sys__try
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.command
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot rpctransport service

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : Net.NetProtoGS] [rsem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]
variable [rpcsem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [net.rpc.Assumptions] [net.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

set_option goose.wp.extras true

theorem Sys.op.wp_proof
    (wp_try : Sys.try.spec (GF := GF) (hG := hG))
    (wp_command : command.spec (GF := GF)) :
    Sys.op.spec (GF := GF) (hG := hG) := by
  intro K s sv i Ψ hc hseq hj1 hj6
  wp_start as ⟨#Henv, Hs, #Hconns, #Hid, Hseq, Hupd⟩
  wp_auto
  obtain ⟨⟨put, way, v⟩, hok⟩ := i
  have hx : inS ⟨(put, way, v), hok⟩ = In.mk put way v := rfl
  rw [hx]
  wp_apply wp_command as %cs Hcs
  · iunfold cliEnv at Henv; icases Henv with ⟨#Hpk, -⟩; iexact Hpk
  ipersist Hcs
  have hm : uint.nat (sv.seq' + W64 1) = uint.nat sv.seq' + 1 := by word
  have hid : idOf (cmdB sv.c' (sv.seq' + W64 1) put v) = (uint.nat sv.c', uint.nat sv.seq' + 1) := by
    rw [idOf_cmdB _ _ _ _ hc, hm, Nat.mod_eq_of_lt hseq]
  iapply fupd_wp
  imod id_reserve K.g (uint.nat sv.c') (uint.nat sv.seq' + 1) $$ [$Hid $Hseq] with ⟨Hseq, Htok⟩
  imodintro
  ihave ⟨#Hru, Hupd⟩ := slotUpd_readUpd K _ Ψ $$ Hupd
  ihave Hst : opSt K (cmdB sv.c' (sv.seq' + W64 1) put v) ⟨(put, way, v), hok⟩ Ψ $$ [Htok Hupd]
  · unfold opSt; ileft; rw [hid]; iframe Htok Hupd
  have hd := datumOf_cmdB sv.c' (sv.seq' + W64 1) ⟨(put, way, v), hok⟩
  have hdl : (cmdB sv.c' (sv.seq' + W64 1) put v).length ≤ 1000 := by
    have hv := hok.2
    unfold cmdB; split <;> simp [opIDB_length] <;> simp only at hv <;> omega
  ihave HI : (∃ (t : w64) (sv' : Sys), "t" ∷ t_ptr ↦ t ∗ "Hs" ∷ s ↦ sv' ∗
      "%Hsv" ∷ ⌜sv'.c' = sv.c' ∧ sv'.conns' = sv.conns' ∧ sv'.seq' = sv.seq' + W64 1 ∧
        1 ≤ uint.nat sv'.j' ∧ uint.nat sv'.j' ≤ 6⌝ ∗
      "Hst" ∷ opSt K (cmdB sv.c' (sv.seq' + W64 1) put v) ⟨(put, way, v), hok⟩ Ψ : IProp GF)
      $$ [t Hs Hst]
  · iexists W64 0, _
    iframe
    ipureintro
    exact ⟨rfl, rfl, rfl, hj1, hj6⟩
  wp_for HI
  wp_if_destruct
  · obtain ⟨hc', hcn', hsq', hj1', hj6'⟩ := Hsv
    wp_apply (wp_try K s sv' sv'.j' cs _ ⟨(put, way, v), hok⟩ Ψ hj1' hj6' hd hdl) $$ [Hs Hst]
      as %o %fin ⟨Hs, Hr⟩
    · iframe Hs Hst Hcs Henv Hru
      rw [hcn']; iframe Hconns
    (try wp_auto)
    cases fin
    · simp only [Bool.false_eq_true, ↓reduceIte]
      (try wp_auto)
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
      iexists t + W64 1, { sv' with j' := W64 1 + sv'.j' % W64 6 }
      iframe
      ipureintro
      refine ⟨hc', hcn', hsq', ?_, ?_⟩ <;> simp only <;> word
    · simp only [↓reduceIte]
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      iapply HΦ
      iframe Hseq Hr
      iexists sv'
      iframe Hs
      ipureintro
      exact ⟨hc', hcn', hsq', hj1', hj6'⟩
  · (try wp_auto)
    iapply HΦ
    obtain ⟨hc', hcn', hsq', hj1', hj6'⟩ := Hsv
    iframe Hseq
    isplitl [Hs]
    · iexists sv'
      iframe Hs
      ipureintro
      exact ⟨hc', hcn', hsq', hj1', hj6'⟩
    unfold outRes
    iright; ipureintro; rfl

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
