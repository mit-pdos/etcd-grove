/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the proof of `State.Bind` (B 669-686).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Bind
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Boot
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Recv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Ready
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Mem
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Write
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Wrote
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Flush
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Net
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Made
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Send
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__ApplyEv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__RestoreEv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__ConfEv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__SnapEv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__ReadAsked
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__ReadGiven
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem State.Bind.wp_proof
    (wp_Boot : State.Boot.spec (GF := GF) (hG := hG))
    (wp_Recv : State.Recv.spec (GF := GF) (hG := hG))
    (wp_Ready : State.Ready.spec (GF := GF) (hG := hG))
    (wp_Mem : State.Mem.spec (GF := GF) (hG := hG))
    (wp_Write : State.Write.spec (GF := GF) (hG := hG))
    (wp_Wrote : State.Wrote.spec (GF := GF) (hG := hG))
    (wp_Flush : State.Flush.spec (GF := GF) (hG := hG))
    (wp_Net : State.Net.spec (GF := GF) (hG := hG))
    (wp_Made : State.Made.spec (GF := GF) (hG := hG))
    (wp_Send : State.Send.spec (GF := GF) (hG := hG))
    (wp_ApplyEv : State.ApplyEv.spec (GF := GF) (hG := hG))
    (wp_RestoreEv : State.RestoreEv.spec (GF := GF) (hG := hG))
    (wp_ConfEv : State.ConfEv.spec (GF := GF) (hG := hG))
    (wp_SnapEv : State.SnapEv.spec (GF := GF) (hG := hG))
    (wp_ReadAsked : State.ReadAsked.spec (GF := GF) (hG := hG))
    (wp_ReadGiven : State.ReadGiven.spec (GF := GF) (hG := hG)) :
    State.Bind.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #He' := He
  iunfold eventRO at He'
  icases He' with ⟨%ge, #Hge, %Hgf, -⟩
  unfold State.bind at Ho
  iStructNamed Hge
  wp_auto
  rw [Hgf.1]
  by_cases h_boot : ev.e = go!"boot"
  · rw [decide_eq_true h_boot]
    simp only [beq_of_eq' h_boot, ite_true] at Ho
    try wp_auto
    wp_apply wp_Boot p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_boot]
  simp only [beq_of_ne' h_boot, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_recv : ev.e = go!"recv"
  · rw [decide_eq_true h_recv]
    simp only [beq_of_eq' h_recv, ite_true] at Ho
    try wp_auto
    wp_apply wp_Recv p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_recv]
  simp only [beq_of_ne' h_recv, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_ready : ev.e = go!"ready"
  · rw [decide_eq_true h_ready]
    simp only [beq_of_eq' h_ready, ite_true] at Ho
    try wp_auto
    wp_apply wp_Ready p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_ready]
  simp only [beq_of_ne' h_ready, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_mem : ev.e = go!"mem"
  · rw [decide_eq_true h_mem]
    simp only [beq_of_eq' h_mem, ite_true] at Ho
    try wp_auto
    wp_apply wp_Mem p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_mem]
  simp only [beq_of_ne' h_mem, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_write : ev.e = go!"write"
  · rw [decide_eq_true h_write]
    simp only [beq_of_eq' h_write, ite_true] at Ho
    try wp_auto
    wp_apply wp_Write p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_write]
  simp only [beq_of_ne' h_write, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_wrote : ev.e = go!"wrote"
  · rw [decide_eq_true h_wrote]
    simp only [beq_of_eq' h_wrote, ite_true] at Ho
    try wp_auto
    wp_apply wp_Wrote p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_wrote]
  simp only [beq_of_ne' h_wrote, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_flush : ev.e = go!"flush"
  · rw [decide_eq_true h_flush]
    simp only [beq_of_eq' h_flush, ite_true] at Ho
    try wp_auto
    wp_apply wp_Flush p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_flush]
  simp only [beq_of_ne' h_flush, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_net : ev.e = go!"net"
  · rw [decide_eq_true h_net]
    simp only [beq_of_eq' h_net, ite_true] at Ho
    try wp_auto
    wp_apply wp_Net p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_net]
  simp only [beq_of_ne' h_net, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_made : ev.e = go!"made"
  · rw [decide_eq_true h_made]
    simp only [beq_of_eq' h_made, ite_true] at Ho
    try wp_auto
    wp_apply wp_Made p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_made]
  simp only [beq_of_ne' h_made, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_send : ev.e = go!"send"
  · rw [decide_eq_true h_send]
    simp only [beq_of_eq' h_send, ite_true] at Ho
    try wp_auto
    wp_apply wp_Send p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_send]
  simp only [beq_of_ne' h_send, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_apply : ev.e = go!"apply"
  · rw [decide_eq_true h_apply]
    simp only [beq_of_eq' h_apply, ite_true] at Ho
    try wp_auto
    wp_apply wp_ApplyEv p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_apply]
  simp only [beq_of_ne' h_apply, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_restore : ev.e = go!"restore"
  · rw [decide_eq_true h_restore]
    simp only [beq_of_eq' h_restore, ite_true] at Ho
    try wp_auto
    wp_apply wp_RestoreEv p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_restore]
  simp only [beq_of_ne' h_restore, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_conf : ev.e = go!"conf"
  · rw [decide_eq_true h_conf]
    simp only [beq_of_eq' h_conf, ite_true] at Ho
    try wp_auto
    wp_apply wp_ConfEv p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_conf]
  simp only [beq_of_ne' h_conf, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_snap : ev.e = go!"snap"
  · rw [decide_eq_true h_snap]
    simp only [beq_of_eq' h_snap, ite_true] at Ho
    try wp_auto
    wp_apply wp_SnapEv p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_snap]
  simp only [beq_of_ne' h_snap, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_readreq : ev.e = go!"readreq"
  · rw [decide_eq_true h_readreq]
    simp only [beq_of_eq' h_readreq, ite_true] at Ho
    try wp_auto
    wp_apply wp_ReadAsked p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_readreq]
  simp only [beq_of_ne' h_readreq, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  by_cases h_read : ev.e = go!"read"
  · rw [decide_eq_true h_read]
    simp only [beq_of_eq' h_read, ite_true] at Ho
    try wp_auto
    wp_apply wp_ReadGiven p s n e ev o $$ [Hs He] as %q %ok Hsucc
    · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, Ho⟩
    try wp_auto
    iapply HΦ; iexact Hsucc
  rw [decide_eq_false h_read]
  simp only [beq_of_ne' h_read, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  simp only [pure_ok, Except.ok.injEq] at Ho
  subst Ho
  iapply HΦ; iunfold succOwn; ipureintro; rfl

end proof

end AntCheck
end EtcdGrove
end Perennial
