/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the proof of `State.ApplyEv` (B 598-609).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__ApplyEv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__first
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__entries
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EntriesEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setInt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setPre
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__MemCommit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.violAdd
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

theorem State.ApplyEv.wp_proof
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_first : Event.first.spec (GF := GF) (hG := hG))
    (wp_entries : Event.entries.spec (GF := GF) (hG := hG))
    (wp_has : Event.has.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG))
    (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG))
    (wp_setInt : setInt.spec (GF := GF) (hG := hG))
    (wp_setPre : setPre.spec (GF := GF) (hG := hG))
    (wp_MemCommit : State.MemCommit.spec (GF := GF) (hG := hG))
    (wp_violAdd : violAdd.spec (GF := GF) (hG := hG)) :
    State.ApplyEv.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp

  obtain ⟨bb, EE, HW, HNO, -, hbb, -⟩ := HBd
  unfold numBound Event.weight at hbb
  have hvl : (s.viol.length : Int) + 1 < 2 ^ 63 := by
    have := HW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega
  unfold State.applyEv at Ho
  obtain ⟨fi, hfi, Ho⟩ := bind_ok Ho
  have hfin : numOk fi := by have := HNO.2.2.1; rw [need_ok hfi] at this; exact this
  unfold numOk numBound at hfin
  icases intsRO_at g.LastApplied' s.lastApplied n ⟨Hn, by rw [HWf.len_lastApplied]; exact Hlt⟩ $$ HLastApplied with ⟨%la, #Hlaa, %Hla⟩
  icases logsRO_at g.Log' s.log n ⟨Hn, by rw [HWf.len_log]; exact Hlt⟩ $$ HLog with ⟨%lg, #Hlga, #Hlg⟩
  ihave %Hlgl := logRO_len _ _ $$ Hlg
  ihave %Hchl := logRO_len _ _ $$ HChain
  have hlab : bigOk s.lastApplied[sint.nat n]! := by
    have hn' : sint.nat n < s.lastApplied.length := by rw [HWf.len_lastApplied]; have := sint_nat_cast Hn; omega
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hn']
    exact HW.2.2.2.2.2.2.1 _ (List.getElem_mem hn')
  unfold bigOk at hlab
  wp_auto
  wp_apply wp_first e ev fi $$ [He] as %uf %Huf
  · iframe He; ipureintro; exact hfi
  try wp_auto
  wp_apply wp_load_at _ _ la Hn $$ [Hlaa]
  · iexact Hlaa
  try wp_auto
  have hla1 : sint.Z (la + W64 1) = s.lastApplied[sint.nat n]! + 1 := by
    rw [sint_add (by rw [Hla, sint_one]; omega) (by rw [Hla, sint_one]; omega), Hla, sint_one]
  rw [decide_w64_eq, Huf, hla1]
  by_cases h1 : fi = s.lastApplied[sint.nat n]! + 1
  case neg =>
    rw [decide_eq_false h1]
    rw [show (fi != s.lastApplied[sint.nat n]! + 1) = true by simpa using h1] at Ho
    simp only [ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true h1]
  rw [show (fi != s.lastApplied[sint.nat n]! + 1) = false by simpa using h1] at Ho
  simp only [Bool.false_eq_true, ite_false] at Ho
  obtain ⟨fi2, hfi2, Ho⟩ := bind_ok Ho
  rw [hfi] at hfi2; cases hfi2
  obtain ⟨es, hes, Ho⟩ := bind_ok Ho
  have hesz : es.length ≤ ev.size := by unfold Event.size; rw [need_ok hes]; simp; omega
  try wp_auto
  wp_apply wp_first e ev fi $$ [He] as %uf2 %Huf2
  · iframe He; ipureintro; exact hfi
  try wp_auto
  wp_apply wp_entries e ev es $$ [He] as %esl #Hes
  · iframe He; ipureintro; exact hes
  ihave %Hesl := logRO_len _ _ $$ Hes
  try wp_auto
  have Hlast : sint.Z (uf2 + esl.len - W64 1) = fi + es.length - 1 := by
    have h1 : sint.Z (uf2 + esl.len) = fi + es.length := by
      rw [sint_add (by rw [Huf2, Hesl]; omega) (by rw [Huf2, Hesl]; omega), Huf2, Hesl]
    rw [sint_sub (by rw [h1, sint_one]; omega) (by rw [h1, sint_one]; omega), h1, sint_one]
  generalize hlast : fi + (es.length : Int) - 1 = last at Ho Hlast
  try dsimp only at Ho
  try wp_auto
  wp_apply wp_load_at _ _ lg Hn $$ [Hlga]
  · iexact Hlga
  try wp_auto
  rw [Hlast, Hlgl]
  by_cases h2 : last ≤ (s.log[sint.nat n]!).length ∧ last ≤ s.chain.length
  case neg =>
    have : (!(decide (last ≤ ↑s.log[sint.nat n]!.length) && decide (last ≤ ↑s.chain.length))) = true := by
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    rw [this] at Ho
    simp only [ite_true, pure_ok, Except.ok.injEq] at Ho
    by_cases h2a : last ≤ (s.log[sint.nat n]!).length
    · rw [decide_eq_true h2a]
      try wp_auto
      rw [Hlast, Hchl, decide_eq_false (by omega)]
      subst Ho
      try wp_auto
      iapply HΦ; iunfold succOwn; ipureintro; rfl
    · rw [decide_eq_false h2a]
      subst Ho
      try wp_auto
      iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true h2.1]
  try wp_auto
  rw [Hlast, Hchl, decide_eq_true h2.2]
  have : (!(decide (last ≤ ↑s.log[sint.nat n]!.length) && decide (last ≤ ↑s.chain.length))) = false := by
    simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq]; omega
  rw [this] at Ho
  simp only [Bool.false_eq_true, ite_false] at Ho
  obtain ⟨sc, hsc, Ho⟩ := bind_ok Ho
  obtain ⟨sl, hsl, Ho⟩ := bind_ok Ho
  obtain ⟨eq1, heq1, Ho⟩ := bind_ok Ho
  try wp_auto
  wp_apply wp_SubSeq g.Chain' s.chain (W64 1) (uf2 + esl.len - W64 1) sc $$ [HChain] as %scl #Hsc
  · iframe HChain; ipureintro; rw [Hlast, sint_one]; exact hsc
  try wp_auto
  wp_apply wp_load_at _ _ lg Hn $$ [Hlga]
  · iexact Hlga
  try wp_auto
  wp_apply wp_SubSeq lg _ (W64 1) (uf2 + esl.len - W64 1) sl $$ [Hlg] as %sll #Hsl
  · iframe Hlg; ipureintro; rw [Hlast, sint_one]; exact hsl
  try wp_auto
  wp_apply wp_EntriesEqual scl sc sll sl eq1 $$ [Hsc Hsl]
  · iframe Hsc Hsl; ipureintro; exact heq1
  cases eq1
  · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
  obtain ⟨es2, hes2, Ho⟩ := bind_ok Ho
  rw [hes] at hes2; cases hes2
  obtain ⟨fi3, hfi3, Ho⟩ := bind_ok Ho
  rw [hfi] at hfi3; cases hfi3
  obtain ⟨sl2, hsl2, Ho⟩ := bind_ok Ho
  obtain ⟨eq2, heq2, Ho⟩ := bind_ok Ho
  try wp_auto
  wp_apply wp_entries e ev es $$ [He] as %esl2 #Hes2
  · iframe He; ipureintro; exact hes
  try wp_auto
  wp_apply wp_load_at _ _ lg Hn $$ [Hlga]
  · iexact Hlga
  try wp_auto
  wp_apply wp_first e ev fi $$ [He] as %uf3 %Huf3
  · iframe He; ipureintro; exact hfi
  try wp_auto
  wp_apply wp_SubSeq lg _ uf3 (uf2 + esl.len - W64 1) sl2 $$ [Hlg] as %sll2 #Hsl2
  · iframe Hlg; ipureintro; rw [Hlast, Huf3]; exact hsl2
  try wp_auto
  wp_apply wp_EntriesEqual esl2 es sll2 sl2 eq2 $$ [Hes2 Hsl2]
  · iframe Hes2 Hsl2; ipureintro; exact heq2
  cases eq2
  · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  wp_apply wp_clone p s $$ [Hs] as %q Hq
  · iexact Hs
  try wp_auto
  wp_apply wp_setInt g.LastApplied' s.lastApplied n (uf2 + esl.len - W64 1) $$ [HLastApplied] as %lao #Hlao
  · iframe HLastApplied; ipureintro; exact ⟨Hn, by rw [HWf.len_lastApplied]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_lastApplied q s lao (s.lastApplied.set (sint.nat n) (sint.Z (uf2 + esl.len - W64 1))) (by rw [List.length_set, HWf.len_lastApplied]) $$ [Hq Hlao] as Hq
  · iframe Hq Hlao
  try wp_auto
  rw [Hlast]
  rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.FA : val) = #fA from rfl]
  wp_apply wp_has e ev fA ev.a $$ [He]
  · iframe He; ipureintro; exact Event.hasF_A _
  cases hmc : s.memCommit (sint.nat n) with
  | error e' => cases ha : ev.a <;> simp [ha, hmc] at Ho
  | ok mc =>
  by_cases hbe : mc < last
  · cases ha : ev.a
    · simp only [Bool.not_false, ite_true]
      try wp_auto
      wp_apply wp_setPre g.Undo' s.undo n null none $$ [HUndo] as %uo #Huo
      · iframe HUndo; iunfold preRO; ipureintro; exact ⟨rfl, Hn, by rw [HWf.len_undo]; exact Hlt⟩
      try wp_auto
      wp_apply wp_set_undo q { s with lastApplied := s.lastApplied.set (sint.nat n) last } uo (s.undo.set (sint.nat n) none) (by rw [List.length_set, HWf.len_undo]) $$ [Hq Huo] as Hq
      · iframe Hq Huo
      try wp_auto
      wp_apply wp_MemCommit p s n mc $$ [Hs] as %umc %Humc
      · iframe Hs; ipureintro; exact ⟨Hn, Hlt, hmc⟩
      try wp_auto
      rw [Humc, Hlast]
      rw [decide_eq_true hbe]
      try wp_auto
      wp_apply wp_violAdd g.Viol' s.viol go!"ApplyBeyondCommit" $$ [HViol] as %vsl #Hvsl
      · iframe HViol; ipureintro; exact hvl
      try wp_auto
      wp_apply wp_set_viol q { { s with lastApplied := s.lastApplied.set (sint.nat n) last } with undo := s.undo.set (sint.nat n) none } vsl (setAdd s.viol go!"ApplyBeyondCommit") $$ [Hq Hvsl] as Hq
      · iframe Hq Hvsl
      try wp_auto
      have hO : o = some { { { s with lastApplied := s.lastApplied.set (sint.nat n) last } with undo := s.undo.set (sint.nat n) none } with viol := setAdd s.viol go!"ApplyBeyondCommit" } := by
        simp [ha, hmc, hbe] at Ho; rw [← Ho]
      subst hO
      iapply HΦ
      iunfold succOwn
      isplitr
      · ipureintro; rfl
      iexact Hq
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      try wp_auto
      wp_apply wp_MemCommit p s n mc $$ [Hs] as %umc %Humc
      · iframe Hs; ipureintro; exact ⟨Hn, Hlt, hmc⟩
      try wp_auto
      rw [Humc, Hlast]
      rw [decide_eq_true hbe]
      try wp_auto
      wp_apply wp_violAdd g.Viol' s.viol go!"ApplyBeyondCommit" $$ [HViol] as %vsl #Hvsl
      · iframe HViol; ipureintro; exact hvl
      try wp_auto
      wp_apply wp_set_viol q { s with lastApplied := s.lastApplied.set (sint.nat n) last } vsl (setAdd s.viol go!"ApplyBeyondCommit") $$ [Hq Hvsl] as Hq
      · iframe Hq Hvsl
      try wp_auto
      have hO : o = some { { s with lastApplied := s.lastApplied.set (sint.nat n) last } with viol := setAdd s.viol go!"ApplyBeyondCommit" } := by
        simp [ha, hmc, hbe] at Ho; rw [← Ho]
      subst hO
      iapply HΦ
      iunfold succOwn
      isplitr
      · ipureintro; rfl
      iexact Hq
  · cases ha : ev.a
    · simp only [Bool.not_false, ite_true]
      try wp_auto
      wp_apply wp_setPre g.Undo' s.undo n null none $$ [HUndo] as %uo #Huo
      · iframe HUndo; iunfold preRO; ipureintro; exact ⟨rfl, Hn, by rw [HWf.len_undo]; exact Hlt⟩
      try wp_auto
      wp_apply wp_set_undo q { s with lastApplied := s.lastApplied.set (sint.nat n) last } uo (s.undo.set (sint.nat n) none) (by rw [List.length_set, HWf.len_undo]) $$ [Hq Huo] as Hq
      · iframe Hq Huo
      try wp_auto
      wp_apply wp_MemCommit p s n mc $$ [Hs] as %umc %Humc
      · iframe Hs; ipureintro; exact ⟨Hn, Hlt, hmc⟩
      try wp_auto
      rw [Humc, Hlast]
      rw [decide_eq_false hbe]
      try wp_auto
      have hO : o = some { { s with lastApplied := s.lastApplied.set (sint.nat n) last } with undo := s.undo.set (sint.nat n) none } := by
        simp [ha, hmc, hbe] at Ho; rw [← Ho]
      subst hO
      iapply HΦ
      iunfold succOwn
      isplitr
      · ipureintro; rfl
      iexact Hq
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      try wp_auto
      wp_apply wp_MemCommit p s n mc $$ [Hs] as %umc %Humc
      · iframe Hs; ipureintro; exact ⟨Hn, Hlt, hmc⟩
      try wp_auto
      rw [Humc, Hlast]
      rw [decide_eq_false hbe]
      try wp_auto
      have hO : o = some { s with lastApplied := s.lastApplied.set (sint.nat n) last } := by
        simp [ha, hmc, hbe] at Ho; rw [← Ho]
      subst hO
      iapply HΦ
      iunfold succOwn
      isplitr
      · ipureintro; rfl
      iexact Hq

end proof

end AntCheck
end EtcdGrove
end Perennial
