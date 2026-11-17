/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__Equal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Server__equal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

-- A failing comparison: `false` (hygiene off: it names the proof's hypotheses).
set_option hygiene false in
local macro "eq_fail" h:ident : tactic => `(tactic| (
    try wp_auto
    have hf : s.eq t = false := by simp [State.eq, $h:ident]
    rw [hf]; iapply HΦ; ipureintro; trivial))

theorem State.Equal.wp_proof (wp_SetEqual : Set.Equal.spec (GF := GF) (hG := hG))
    (wp_BagEqual : Bag.Equal.spec (GF := GF) (hG := hG))
    (wp_ServerEqual : Server.equal.spec (GF := GF) (hG := hG)) :
    State.Equal.spec (GF := GF) (hG := hG) := by
  intro p s q t
  wp_start as ⟨#Hs, #Ht⟩
  iunfold stateRO at Hs Ht
  icases Hs with ⟨%gs, %sms, #Hps, #Hsrvs, #HSs, %Hkeyss, %Hnds, #Hsvs, #Hms, #Hpms, %Hrcs⟩
  icases Ht with ⟨%gt, %smt, #Hpt, #Hsrvt, #HSt, %Hkeyst, %Hndt, #Hsvt, #Hmt, #Hpmt, %Hrct⟩
  icases typedPointsto_split _ _ _ $$ Hps with Hpsf
  icases typedPointsto_split _ _ _ $$ Hpt with Hptf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpsf with ⟨#S1, #S2, #S3, #S4, #S5, #S6, #S7, -⟩
  icases Hptf with ⟨#T1, #T2, #T3, #T4, #T5, #T6, #T7, -⟩
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Equal_unfold.method_unfold]
  wp_auto
  wp_apply wp_SetEqual _ _ _ _ $$ [Hsrvs Hsrvt] as -
  · iframe Hsrvs Hsrvt
  by_cases h1 : s.server = t.server
  rotate_left
  · rw [decide_eq_false h1]; eq_fail h1
  rw [decide_eq_true h1]
  wp_auto
  have e2 := sint_eq_iff _ _ _ _ Hrcs.1 Hrct.1
  by_cases h2 : s.reconfigCount = t.reconfigCount
  rotate_left
  · rw [decide_eq_false (fun x => h2 (e2.1 x))]; eq_fail h2
  rw [decide_eq_true (e2.2 h2)]
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Equal_unfold.method_unfold]
  wp_auto
  wp_apply wp_BagEqual _ _ _ _ $$ [Hms Hmt] as -
  · iframe Hms Hmt
  cases h3 : s.messages.eq t.messages
  · eq_fail h3
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Equal_unfold.method_unfold]
  wp_auto
  wp_apply wp_BagEqual _ _ _ _ $$ [Hpms Hpmt] as -
  · iframe Hpms Hpmt
  cases h4 : s.pendingMessages.eq t.pendingMessages
  · eq_fail h4
  wp_auto
  rename_i ip
  irename : (ip ↦ (zero_val w64 : w64) : IProp GF) => Hj
  have hsrv : s.server = t.server := h1
  iunfold setRO at Hsrvs
  icases Hsrvs with ⟨%xs, #Hxs, %Hxm⟩
  ihave %Hxl := ownSlice_len $$ Hxs
  have heq : s.eq t = s.server.all (fun i => (s.s i).eq (t.s i) s.server) := by
    unfold State.eq; simp [h1, h2, h3, h4]
  rw [heq]
  ihave IH : iprop(∃ (n jv : w64),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ ip ↦ jv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z gs.Server'.len ∧
        (s.server.take (sint.nat n)).all (fun i => (s.s i).eq (t.s i) s.server) = true⌝) $$ [i Hj]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hn0, hn1, hna⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by rw [Hxl.1]; word
    obtain ⟨x, Hx⟩ : ∃ x, xs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hsx : s.server[sint.nat n]? = some (uint.nat x) := by rw [← Hxm, List.getElem?_map, Hx]; rfl
    have Htx : t.server[sint.nat n]? = some (uint.nat x) := by rw [← hsrv]; exact Hsx
    have Hii : W64 (Int.ofNat (uint.nat x)) = x := by apply BitVec.eq_of_toNat_eq; simp
    icases (BigSepL.bigSepL_lookup (Φ := fun _ j => iprop(∃ q : Loc, ⌜sms !! (W64 (Int.ofNat j)) = some q⌝ ∗
        serverRO (GF := GF) q (s.s j))) Hsx) $$ Hsvs with ⟨%qs, %Hqs, #Hsv⟩
    icases (BigSepL.bigSepL_lookup (Φ := fun _ j => iprop(∃ q : Loc, ⌜smt !! (W64 (Int.ofNat j)) = some q⌝ ∗
        serverRO (GF := GF) q (t.s j))) Htx) $$ Hsvt with ⟨%qt, %Hqt, #Htv⟩
    rw [Hii] at Hqs Hqt
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z gs.Server'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) xs DFrac.discard x hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hx
    try wp_auto
    wp_apply wp_map_lookup1 $$ [HSt] as -
    · iexact HSt
    rw [Hqt]
    simp only [Option.getD_some]
    try wp_auto
    wp_apply wp_map_lookup1 $$ [HSs] as -
    · iexact HSs
    rw [Hqs]
    simp only [Option.getD_some]
    try wp_auto
    wp_apply wp_ServerEqual qs (s.s (uint.nat x)) qt (t.s (uint.nat x)) gs.Server' s.server $$ [Hsv Htv Hxs]
    · iframe Hsv Htv
      iunfold setRO; iexists xs; iframe Hxs; ipureintro; exact Hxm
    have htake : (s.server.take (sint.nat (n + W64 1))).all (fun i => (s.s i).eq (t.s i) s.server) =
        ((s.server.take (sint.nat n)).all (fun i => (s.s i).eq (t.s i) s.server) &&
          (s.s (uint.nat x)).eq (t.s (uint.nat x)) s.server) := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hsx]
      simp
    cases hx : (s.s (uint.nat x)).eq (t.s (uint.nat x)) s.server
    · try wp_auto
      wp_for_post
      try wp_auto
      have : s.server.all (fun i => (s.s i).eq (t.s i) s.server) = false :=
        List.all_eq_false.2 ⟨uint.nat x, List.mem_of_getElem? Hsx, by simp [hx]⟩
      rw [this]
      iapply HΦ; ipureintro; trivial
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htake, hna, hx]
  · try wp_auto
    have hnx : sint.nat n = s.server.length := by rw [← Hxm, List.length_map, Hxl.1]; word
    rw [hnx, List.take_length] at hna
    rw [hna]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
