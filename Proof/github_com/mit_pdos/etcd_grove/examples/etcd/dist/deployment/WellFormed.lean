/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/WellFormed.lean`: every check
in Go's order, each failing one returning a fresh `fmt.Errorf` error (not `nil`); when all pass,
`goWellFormed d` holds, hence `d.WellFormed` (`WellFormedLemmas.goWellFormed_sound`). Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.WellFormed
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.nameOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.kindNames
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.boundsOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.AddrOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.NodeCount
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.IdsOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.compatible
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.NeedsAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.WellFormedLemmas
public import Spec.fmt.ErrorfStrs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section argok
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- An argument `fmt` formats safely: `nil` or a well-formed basic value. -/
def argOkP (a : GoInterface) : Prop := a = GoInterface.nil ∨ ∃ ii, a = interface.ok ii ∧ fmt.ArgWf ii

theorem argOkP_set {l : List GoInterface} {n : Nat} {x : GoInterface} (hl : ∀ a ∈ l, argOkP a)
    (hx : argOkP x) : ∀ a ∈ l.set n x, argOkP a :=
  fun a ha => (List.mem_or_eq_of_mem_set ha).elim (hl a) (fun h => h ▸ hx)

theorem argOkP_cons {l : List GoInterface} {x : GoInterface} (hx : argOkP x) (hl : ∀ a ∈ l, argOkP a) :
    ∀ a ∈ x :: l, argOkP a := by
  intro a ha
  rcases List.mem_cons.1 ha with rfl | ha
  · exact hx
  · exact hl a ha

theorem argOkP_nil : ∀ a ∈ ([] : List GoInterface), argOkP a := fun a ha => absurd ha List.not_mem_nil

theorem argOkP_nilv : argOkP GoInterface.nil := Or.inl rfl

end argok

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

theorem argOkP_int (n : w64) : argOkP (interface.mkOk go.int #n) :=
  Or.inr ⟨_, rfl, argWf_int (hG := hG) (sem := sem) n⟩

theorem argOkP_string (x : GoString) : argOkP (interface.mkOk go.string #x) :=
  Or.inr ⟨_, rfl, argWf_string (hG := hG) (sem := sem) x⟩

/-- Arguments `fmt` formats safely. -/
theorem strArgOk_list (args : List GoInterface) (h : ∀ a ∈ args, argOkP a) :
    ⊢ ([∗list] a ∈ args, fmt.strArgOk (GF := GF) a) := by
  induction args with
  | nil => iintro; iapply BigSepL.bigSepL_nil.2; itrivial
  | cons a args ih =>
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · rcases h a (List.mem_cons_self ..) with rfl | ⟨ii, rfl, hw⟩
      · unfold fmt.strArgOk; itrivial
      · unfold fmt.strArgOk; ileft; ipureintro; exact Or.inl hw
    · iapply ih (fun a ha => h a (List.mem_cons_of_mem _ ha))

set_option hygiene false in
/-- A check fails: `fmt.Errorf(format, args...)` (a fresh error, not `nil`) is returned. -/
local macro "err_exit" : tactic => `(tactic| (
  (try wp_auto)
  first
    | (wp_apply (hErrorf _ slice.nil [] (DFrac.own 1)) $$ [] as %e ⟨-, -, -⟩
       · iframe; isplitl
         · iapply ownSlice_nil
         · iapply BigSepL.bigSepL_nil.2; itrivial)
    | (wp_apply wp_slice_literal
       isplitr
       · ipureintro; rfl
       iintro %asl ⟨Hasl, -⟩
       wp_apply (hErrorf _ _ _ (DFrac.own 1)) $$ [Hasl] as %e ⟨-, -, -⟩
       · iframe
         iapply strArgOk_list
         repeat' (first
           | exact argOkP_nil
           | exact argOkP_nilv
           | exact argOkP_int (hG := hG) (sem := sem) _
           | exact argOkP_string (hG := hG) (sem := sem) _
           | apply argOkP_set
           | apply argOkP_cons))
  (try wp_auto)
  repeat wp_for_post
  iapply HΦ
  ipureintro; intro h; cases h))

theorem len_zero (s : GoSlice) (h : sint.nat s.len = 0) (h0 : 0 ≤ sint.Z s.len) : s.len = W64 0 := by
  word

theorem len_le (s : GoSlice) (n k : Nat) (h : ¬ sint.Z (W64 (k : Int)) < sint.Z s.len)
    (hl : n = sint.nat s.len) (hk : k < 2 ^ 63 := by decide) : n ≤ k := by
  word

theorem idx_facts (s : GoSlice) (j len : Nat) (hl : len = sint.nat s.len) (h0l : 0 ≤ sint.Z s.len)
    (h : sint.Z (W64 (j : Int)) < sint.Z s.len) (hj : j ≤ len) :
    j < len ∧ 0 ≤ sint.Z (W64 (j : Int)) ∧ (sint.Z (W64 (j : Int))).toNat = j ∧
      W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by
  refine ⟨by word, by word, by word, by word⟩

theorem idx_end (s : GoSlice) (j len : Nat) (hl : len = sint.nat s.len) (h0l : 0 ≤ sint.Z s.len)
    (h : ¬ sint.Z (W64 (j : Int)) < sint.Z s.len) (hj : j ≤ len) : j = len := by
  word

theorem strlen_le (n k : Nat) (hn : n < 2 ^ 63) (hk : k < 2 ^ 63)
    (h : ¬ sint.Z (W64 (n : Int)) > sint.Z (W64 (k : Int))) : n ≤ k := by
  word

theorem kind_known (k : w64) (s : GoSlice) (h1 : ¬ sint.Z k < sint.Z (W64 0))
    (h2 : ¬ sint.Z s.len ≤ sint.Z k) (hl : kindNameList.length = sint.nat s.len) (h0 : 0 ≤ sint.Z s.len) :
    kindKnown k := by
  have h11 : kindNameList.length = 11 := rfl
  unfold kindKnown
  constructor <;> word

/-- The `addrs` map holds the addresses `ad` checked so far: valid, short, distinct. -/
def addrsOk (mp : GMap GoString Bool) (ad : List GoString) : Prop :=
  (∀ k, mp !! k = if k ∈ ad then some true else none) ∧ ad.Nodup ∧
    ∀ a ∈ ad, Net.addrOk a = true ∧ a.length ≤ etcd_dist.typed.maxLen

theorem addrsOk_nil : addrsOk ∅ [] := ⟨fun k => by simp, List.nodup_nil, fun a h => by simp at h⟩

theorem addrsOk_insert (mp : GMap GoString Bool) (ad : List GoString) (a : GoString)
    (h : addrsOk mp ad) (hn : a ∉ ad) (ha : Net.addrOk a = true) (hl : a.length ≤ etcd_dist.typed.maxLen) :
    addrsOk (<[a := true]> mp) (ad ++ [a]) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun k => ?_, ?_, fun x hx => ?_⟩
  · by_cases hk : k = a
    · subst hk; simp
    · rw [lookup_insert_ne mp true (Ne.symm hk), h1 k]; simp [hk]
  · rw [List.nodup_append]
    refine ⟨h2, by simp, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_singleton] at hy
    subst hy; subst hxy; exact hn hx
  · rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h3 x hx
    · exact ⟨ha, hl⟩

set_option hygiene false in
/-- A call of the `addr` closure on a new address: it fails (an error returned at once) or the address
is valid, short and new, and is added to `addrs` (`Hok` then holds of the longer list). -/
local macro "addr_call" x:term : tactic => `(tactic| (
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsl
  wp_if_destruct
  · err_exit
  have hl255 := strlen_le _ 255 Hsl (by decide) Hif
  wp_apply (hAddr $x (by omega))
  cases hab : Net.addrOk $x
  · simp only [Bool.not_false]
    err_exit
  simp only [Bool.not_true]
  wp_auto
  wp_apply (wp_map_lookup1 _ _ am _ _) $$ [Ham] as Ham
  · iframe
  rw [Hok.1]
  split
  · simp only [Option.getD_some]
    err_exit
  rename_i hin
  simp only [Option.getD_none]
  rw [show (zero_val Bool) = false from rfl]
  wp_auto
  wp_apply wp_mapInsert $$ [Ham] as Ham
  · iframe
  have Hok := addrsOk_insert _ _ _ Hok hin hab (by unfold etcd_dist.typed.maxLen; exact hl255)))

theorem idx_lt (s : GoSlice) (j len : Nat) (hl : len = sint.nat s.len) (h0l : 0 ≤ sint.Z s.len)
    (hj : j < len) : sint.Z (W64 (j : Int)) < sint.Z s.len := by
  word

theorem len_eq_of (s : GoSlice) (n : Nat) (hl : n = sint.nat s.len) (h0l : 0 ≤ sint.Z s.len) :
    s.len = W64 (n : Int) ∧ n < 2 ^ 63 := by
  constructor <;> word

set_option maxHeartbeats 4000000 in
theorem WellFormed.wp_proof
    (hNameOk : etcd_dist.nameOk.spec (GF := GF) (hG := hG))
    (hNames : etcd_dist.kindNames.spec (GF := GF) (hG := hG))
    (hBounds : etcd_dist.boundsOk.spec (GF := GF) (hG := hG))
    (hAddr : etcd_dist.AddrOk.spec (GF := GF) (hG := hG))
    (hNodeCount : etcd_dist.NodeCount.spec (GF := GF) (hG := hG))
    (hIds : etcd_dist.IdsOk.spec (GF := GF) (hG := hG))
    (hCompat : etcd_dist.compatible.spec (GF := GF) (hG := hG))
    (hAuth : etcd_dist.NeedsAuth.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.ErrorfStrs.spec (GF := GF) (hG := hG)) :
    etcd_dist.WellFormed.spec (GF := GF) (hG := hG) := by
  intro v d hfips
  wp_start as #Hd
  wp_auto
  iunfold deploymentRepr at Hd
  icases Hd with ⟨#Hm, %htok, %hcfg, #Hw, %ss, #Hn, #Hns⟩
  ihave %Hlm := ownSlice_len _ _ _ $$ Hm
  rw [List.length_map] at Hlm
  wp_if_destruct
  · err_exit
  have hne0 := Hif
  wp_if_destruct
  · err_exit
  have hle64 := Hif
  have hmem : d.members ≠ [] := by
    intro h; rw [h] at Hlm; exact hne0 (len_zero _ Hlm.1.symm Hlm.2)
  have hmax : d.members.length ≤ etcd_dist.typed.maxMembers := len_le _ _ _ hle64 Hlm.1
  wp_apply (wp_map_make1 (K := GoString) (V := Bool)) as %nm Hnm
  ihave HI : (∃ (j : Nat) (mv : deployment.Member) (mp : GMap GoString Bool),
      "i" ∷ i_ptr ↦ W64 j ∗ "m" ∷ m_ptr ↦ mv ∗ "Hnm" ∷ nm ↦$ mp ∗
      "%Hj" ∷ ⌜j ≤ d.members.length ∧
        (∀ k, mp !! k = if k ∈ (d.members.take j).map Member.name then some true else none) ∧
        ((d.members.take j).map Member.name).Nodup ∧
        (∀ m ∈ d.members.take j, etcd_dist.typed.nameOk m.name = true ∧ m.name.length ≤ etcd_dist.typed.maxNameLen)⌝ :
      IProp GF) $$ [i m Hnm]
  · iexists 0, _, ∅
    iframe
    ipureintro
    exact ⟨by omega, fun k => by simp, by simp, fun m hm => by simp at hm⟩
  wp_for HI
  obtain ⟨Hj1, Hj2, Hj3, Hj4⟩ := Hj
  wp_if_destruct
  · obtain ⟨hj, h0, hsj, hw⟩ := idx_facts _ _ _ Hlm.1 Hlm.2 Hif Hj1
    simp only [h0, Hif, and_self, ↓reduceIte]
    obtain ⟨mm, hmm⟩ : ∃ mm, d.members[j]? = some mm := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index v.Members' (sint.Z (W64 (j : Int))) (d.members.map Member.val) DFrac.discard mm.val h0) $$ [] as -
    · iframe #; ipureintro; rw [hsj, List.getElem?_map, hmm]; rfl
    have htake : d.members.take (j + 1) = d.members.take j ++ [mm] := by
      rw [List.take_add_one, hmm]; rfl
    wp_apply hNameOk
    by_cases hn : typed.nameOk mm.name = true
    · rw [hn]
      simp only [Bool.not_true]
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsl
      wp_if_destruct
      · err_exit
      · have hl255 := strlen_le _ 200 Hsl (by decide) Hif
        wp_apply (wp_map_lookup1 _ _ nm mp mm.name) $$ [Hnm] as Hnm
        · iframe
        rw [Hj2]
        by_cases hin : mm.name ∈ (d.members.take j).map Member.name
        · rw [if_pos hin]
          simp only [Option.getD_some]
          err_exit
        · rw [if_neg hin]
          simp only [Option.getD_none]
          rw [show (zero_val Bool) = false from rfl]
          wp_auto
          wp_apply wp_mapInsert $$ [Hnm] as Hnm
          · iframe
          wp_for_post
          iframe
          iexists (j + 1), _, _
          rw [hw]
          iframe
          ipureintro
          refine ⟨by omega, ?_, ?_, ?_⟩
          · intro k
            rw [htake, List.map_append]
            by_cases hk : k = mm.name
            · subst hk; simp
            · rw [lookup_insert_ne mp true (Ne.symm hk), Hj2 k]; simp [hk]
          · rw [htake, List.map_append, List.nodup_append]
            refine ⟨Hj3, by simp, ?_⟩
            intro a ha b hb hab
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
            subst hb; subst hab; exact hin ha
          · intro m hm
            rw [htake, List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | rfl
            · exact Hj4 m hm
            · exact ⟨hn, hl255⟩
    · rw [Bool.not_eq_true] at hn
      rw [hn]
      simp only [Bool.not_false]
      err_exit
  · have hjl := idx_end _ _ _ Hlm.1 Hlm.2 Hif Hj1
    subst hjl
    rw [List.take_length] at Hj3 Hj4
    ihave %Hlw := ownSlice_len _ _ _ $$ Hw
    rw [List.length_map] at Hlw
    ihave HW : (∃ (j : Nat) (wv : deployment.Workload),
        "i" ∷ i_ptr ↦ W64 j ∗ "w" ∷ w_ptr ↦ wv ∗
        "%Hj" ∷ ⌜j ≤ d.workloads.length ∧ ∀ w ∈ d.workloads.take j, kindKnown w.kind ∧ w.goBoundsOk⌝ :
        IProp GF) $$ [i w]
    · iexists 0, _
      iframe
      ipureintro
      exact ⟨by omega, fun w hw => by simp at hw⟩
    wp_for HW
    obtain ⟨Hk1, Hk2⟩ := Hj
    wp_if_destruct
    · obtain ⟨hj, h0, hsj, hw⟩ := idx_facts _ _ _ Hlw.1 Hlw.2 Hif Hk1
      simp only [h0, Hif, and_self, ↓reduceIte]
      obtain ⟨ww, hww⟩ : ∃ ww, d.workloads[j]? = some ww := ⟨_, List.getElem?_eq_getElem hj⟩
      wp_apply (wp_load_slice_index v.Workloads' (sint.Z (W64 (j : Int))) (d.workloads.map Workload.val) DFrac.discard ww.val h0) $$ [] as -
      · iframe #; ipureintro; rw [hsj, List.getElem?_map, hww]; rfl
      have htake : d.workloads.take (j + 1) = d.workloads.take j ++ [ww] := by
        rw [List.take_add_one, hww]; rfl
      wp_if_destruct
      · err_exit
      · have hk0 := Hif
        wp_apply hNames as %knl Hknl
        ihave %Hkl := ownSlice_len _ _ _ $$ Hknl
        wp_if_destruct
        · err_exit
        · have hkk := kind_known _ _ hk0 Hif Hkl.1 Hkl.2
          wp_apply hBounds
          by_cases hb : ww.goBoundsOk
          · rw [decide_eq_true hb]
            simp only [Bool.not_true]
            wp_auto
            wp_for_post
            iframe
            iexists (j + 1), _
            rw [hw]
            iframe
            ipureintro
            refine ⟨by omega, fun w hw' => ?_⟩
            rw [htake, List.mem_append, List.mem_singleton] at hw'
            rcases hw' with hw' | rfl
            · exact Hk2 w hw'
            · exact ⟨hkk, hb⟩
          · rw [decide_eq_false hb]
            simp only [Bool.not_false]
            err_exit
    · have hjl := idx_end _ _ _ Hlw.1 Hlw.2 Hif Hk1
      subst hjl
      rw [List.take_length] at Hk2
      ihave %Hln := ownSlice_len _ _ _ $$ Hn
      ihave %Hlns := BigSepL2.bigSepL2_length $$ Hns
      by_cases hnl : v.Nodes'.len = v.Workloads'.len
      · simp only [hnl, _root_.decide_true, Bool.not_true]
        wp_auto
        have hnl' : d.nodes.length = d.workloads.length := by
          rw [← Hlns]; rw [Hln.1, Hlw.1, hnl]
        wp_apply (wp_map_make1 (K := GoString) (V := Bool)) as %am Ham
        ihave HA : (∃ (j : Nat) (mv : deployment.Member) (mpA : GMap GoString Bool),
            "i" ∷ i_ptr ↦ W64 j ∗ "m" ∷ m_ptr ↦ mv ∗ "Ham" ∷ am ↦$ mpA ∗
            "%Hj" ∷ ⌜j ≤ d.members.length ∧
              addrsOk mpA ((d.members.take j).flatMap (fun m => [m.peer, m.client]))⌝ : IProp GF)
          $$ [i m Ham]
        · iexists 0, _, ∅
          iframe
          ipureintro
          exact ⟨by omega, addrsOk_nil⟩
        wp_for HA
        obtain ⟨Hj1', Hok⟩ := Hj
        wp_if_destruct
        · obtain ⟨hj, h0, hsj, hw⟩ := idx_facts _ _ _ Hlm.1 Hlm.2 Hif Hj1'
          simp only [h0, Hif, and_self, ↓reduceIte]
          obtain ⟨mm, hmm⟩ : ∃ mm, d.members[j]? = some mm := ⟨_, List.getElem?_eq_getElem hj⟩
          wp_apply (wp_load_slice_index v.Members' (sint.Z (W64 (j : Int))) (d.members.map Member.val) DFrac.discard mm.val h0) $$ [] as -
          · iframe #; ipureintro; rw [hsj, List.getElem?_map, hmm]; rfl
          addr_call mm.peer
          addr_call mm.client
          wp_for_post
          iframe
          iexists (j + 1), _, _
          rw [hw]
          iframe
          ipureintro
          refine ⟨by omega, ?_⟩
          have e : (d.members.take (j + 1)).flatMap (fun m => [m.peer, m.client]) =
              (d.members.take j).flatMap (fun m => [m.peer, m.client]) ++ [mm.peer] ++ [mm.client] := by
            rw [List.take_add_one, hmm]; simp
          rw [e]; exact Hok
        · have hjl := idx_end _ _ _ Hlm.1 Hlm.2 Hif Hj1'
          subst hjl
          rw [List.take_length] at Hok
          ihave HN : (∃ (j : Nat) (wv : deployment.Workload) (jv : w64) (mpA : GMap GoString Bool),
              "i" ∷ i_ptr ↦ W64 j ∗ "w" ∷ w_ptr ↦ wv ∗ "j" ∷ j_ptr ↦ jv ∗ "Ham" ∷ am ↦$ mpA ∗
              "%Hj" ∷ ⌜j ≤ d.workloads.length ∧
                addrsOk mpA (d.members.flatMap (fun m => [m.peer, m.client]) ++ (d.nodes.take j).flatten) ∧
                ∀ (j' : Nat) (w : Workload) (ns : List GoString), j' < j → d.workloads[j']? = some w →
                  d.nodes[j']? = some ns → W64 ns.length = w.goNodeCount ∧ ns.length < 2 ^ 63⌝ : IProp GF)
            $$ [i w j Ham]
          · iexists 0, _, _, _
            iframe
            ipureintro
            refine ⟨by omega, by simpa using Hok, fun j' w ns h => absurd h (by omega)⟩
          wp_for HN
          obtain ⟨Hn1, Hok, Hn3⟩ := Hj
          wp_if_destruct
          · obtain ⟨hj, h0, hsj, hw⟩ := idx_facts _ _ _ Hlw.1 Hlw.2 Hif Hn1
            simp only [h0, Hif, and_self, ↓reduceIte]
            obtain ⟨ww, hww⟩ : ∃ ww, d.workloads[j]? = some ww := ⟨_, List.getElem?_eq_getElem hj⟩
            wp_apply (wp_load_slice_index v.Workloads' (sint.Z (W64 (j : Int))) (d.workloads.map Workload.val) DFrac.discard ww.val h0) $$ [] as -
            · iframe #; ipureintro; rw [hsj, List.getElem?_map, hww]; rfl
            have hjn : j < d.nodes.length := by omega
            obtain ⟨ns, hns⟩ : ∃ ns, d.nodes[j]? = some ns := ⟨_, List.getElem?_eq_getElem hjn⟩
            have hjs : j < ss.length := by omega
            obtain ⟨sj, hsj'⟩ : ∃ sj, ss[j]? = some sj := ⟨_, List.getElem?_eq_getElem hjs⟩
            ihave #Hsj := BigSepL2.bigSepL2_lookup (Φ := fun _ s ns => (s ↦*□ ns : IProp GF)) hsj' hns $$ Hns
            have hcN := idx_lt v.Nodes' j ss.length Hln.1 Hln.2 hjs
            simp only [h0, hcN, and_self, ↓reduceIte]
            wp_apply (wp_load_slice_index v.Nodes' (sint.Z (W64 (j : Int))) ss DFrac.discard sj h0) $$ [] as -
            · iframe #; ipureintro; rw [hsj]; exact hsj'
            ihave %Hsjl := ownSlice_len _ _ _ $$ Hsj
            obtain ⟨hsjlen, hsjlt⟩ := len_eq_of sj ns.length Hsjl.1 Hsjl.2
            wp_apply hNodeCount
            by_cases hnc : sj.len = ww.goNodeCount
            · rw [decide_eq_true hnc]
              (try simp only [Bool.not_true])
              wp_auto
              simp only [h0, hcN, _root_.and_self, ↓reduceIte]
              wp_apply (wp_load_slice_index v.Nodes' (sint.Z (W64 (j : Int))) ss DFrac.discard sj h0) $$ [] as -
              · iframe #; ipureintro; rw [hsj]; exact hsj'
              have Hok0 := Hok
              ihave HK : (∃ (k : Nat) (av : GoString) (mpA' : GMap GoString Bool),
                  "i" ∷ i_ptr ↦ W64 k ∗ "a" ∷ a_ptr ↦ av ∗ "Ham" ∷ am ↦$ mpA' ∗
                  "%Hk" ∷ ⌜k ≤ ns.length ∧ addrsOk mpA' (d.members.flatMap (fun m => [m.peer, m.client]) ++
                    (d.nodes.take j).flatten ++ ns.take k)⌝ : IProp GF) $$ [i a Ham]
              · iexists 0, _, _
                iframe
                ipureintro
                exact ⟨by omega, by simpa using Hok0⟩
              wp_for HK
              obtain ⟨Hk1', Hok⟩ := Hk
              wp_if_destruct
              · obtain ⟨hk, h0k, hsk, hwk⟩ := idx_facts _ _ _ Hsjl.1 Hsjl.2 Hif Hk1'
                simp only [h0k, Hif, _root_.and_self, ↓reduceIte]
                obtain ⟨x, hx⟩ : ∃ x, ns[k]? = some x := ⟨_, List.getElem?_eq_getElem hk⟩
                wp_apply (wp_load_slice_index sj (sint.Z (W64 (k : Int))) ns DFrac.discard x h0k) $$ [] as -
                · iframe #; ipureintro; rw [hsk]; exact hx
                addr_call x
                wp_for_post
                iframe
                iexists (k + 1), _, _
                rw [hwk]
                iframe
                ipureintro
                refine ⟨by omega, ?_⟩
                rw [List.take_add_one, hx]
                simpa [List.append_assoc] using Hok
              · have hkl := idx_end _ _ _ Hsjl.1 Hsjl.2 Hif Hk1'
                subst hkl
                rw [List.take_length] at Hok
                wp_for_post
                iframe
                iexists (j + 1), _, _, _
                rw [hw]
                iframe
                ipureintro
                refine ⟨by omega, ?_, ?_⟩
                · rw [List.take_add_one, hns]
                  simpa [List.append_assoc] using Hok
                · intro j' w' ns' hj' hw' hns'
                  by_cases hjj : j' = j
                  · subst hjj
                    rw [hww] at hw'; cases hw'
                    rw [hns] at hns'; cases hns'
                    exact ⟨by rw [← hnc, hsjlen], hsjlt⟩
                  · exact Hn3 j' w' ns' (by omega) hw' hns'
            · rw [decide_eq_false hnc]
              (try simp only [Bool.not_false])
              wp_auto
              simp only [h0, hcN, _root_.and_self, ↓reduceIte]
              wp_apply (wp_load_slice_index v.Nodes' (sint.Z (W64 (j : Int))) ss DFrac.discard sj h0) $$ [] as -
              · iframe #; ipureintro; rw [hsj]; exact hsj'
              wp_apply hNodeCount
              err_exit
          · have hjl := idx_end _ _ _ Hlw.1 Hlw.2 Hif Hn1
            subst hjl
            rw [← hnl', List.take_length] at Hok
            wp_apply (hIds v d hfips (fun m hm =>
                Hok.2.2 m.peer (List.mem_append_left _ (List.mem_flatMap.2 ⟨m, hm, by simp⟩)))) $$ [] as %bid %hbid
            · iunfold deploymentRepr
              iframe #
              ipureintro; exact ⟨htok, hcfg⟩
            cases bid
            · simp only [Bool.not_false]
              err_exit
            simp only [Bool.not_true]
            wp_auto
            rw [htok]
            wp_if_destruct
            · err_exit
            have htok0 : d.token ≠ [] := Hif
            wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Htl
            wp_if_destruct
            · err_exit
            have htokl := strlen_le _ 255 Htl (by decide) Hif
            rw [hcfg]
            wp_auto
            wp_if_destruct
            · err_exit
            have hsnap : 1 ≤ uint.Z d.cfg.snapCount := by
              have : uint.Z (W64 1) = 1 := rfl
              omega
            wp_if_destruct
            · err_exit
            have hcatch : 1 ≤ uint.Z d.cfg.catchUp := by
              have : uint.Z (W64 1) = 1 := rfl
              omega
            repeat' wp_if_destruct
            all_goals first | err_exit | skip
            all_goals (
              have hret : d.cfg.retention ≠ W64 0 →
                  (d.cfg.compactorMode = go!"revision" ∧ 1 ≤ sint.Z d.cfg.retention) ∨
                  (d.cfg.compactorMode = go!"periodic" ∧ 10 ≤ sint.Z d.cfg.retention) := by
                intro h
                first
                  | exact absurd ‹d.cfg.retention = W64 0› h
                  | (left; exact ⟨‹_›, by have : sint.Z (W64 1) = 1 := rfl; omega⟩)
                  | (right; exact ⟨‹_›, by have : sint.Z (W64 10) = 10 := rfl; omega⟩)
              wp_apply (hCompat v.Workloads' d.workloads) $$ [] as %bc %hbc
              · iframe #
              cases bc
              · simp only [Bool.not_false]
                err_exit
              simp only [Bool.not_true]
              wp_auto
              ihave HF : (∃ (j : Nat) (wv : deployment.Workload) (nb : Bool),
                  "i" ∷ i_ptr ↦ W64 j ∗ "w" ∷ w_ptr ↦ wv ∗ "needed" ∷ needed_ptr ↦ nb ∗
                  "%Hj" ∷ ⌜j ≤ d.workloads.length ∧ (∀ w ∈ d.workloads.take j,
                    (kindAlone w.kind = true → d.cfg.auth = true) ∧
                    (w.kind = W64 3 → ¬ (d.cfg.retention ≠ W64 0 ∧ d.cfg.compactorMode = go!"periodic")) ∧
                    (w.kind = W64 9 → d.cfg.auth = false)) ∧
                    (nb = true → ∃ w ∈ d.workloads.take j, kindAlone w.kind = true)⌝ : IProp GF) $$ [i w needed]
              · iexists 0, _, false
                iframe
                ipureintro
                exact ⟨by omega, fun w hw => by simp at hw, fun h => by cases h⟩
              wp_for HF
              obtain ⟨Hf1, Hf2, Hf3⟩ := Hj
              wp_if_destruct
              · have Hif' : sint.Z (W64 (j : Int)) < sint.Z v.Workloads'.len := by
                  first | exact Hif | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
                obtain ⟨hj, h0, hsj, hw⟩ := idx_facts _ _ _ Hlw.1 Hlw.2 Hif' Hf1
                simp only [h0, Hif', _root_.and_self, ↓reduceIte]
                obtain ⟨ww, hww⟩ : ∃ ww, d.workloads[j]? = some ww := ⟨_, List.getElem?_eq_getElem hj⟩
                wp_apply (wp_load_slice_index v.Workloads' (sint.Z (W64 (j : Int))) (d.workloads.map Workload.val) DFrac.discard ww.val h0) $$ [] as -
                · iframe #; ipureintro; rw [hsj, List.getElem?_map, hww]; rfl
                wp_apply hAuth
                have htake : d.workloads.take (j + 1) = d.workloads.take j ++ [ww] := by
                  rw [List.take_add_one, hww]; rfl
                rcases hal : kindAlone ww.kind with _ | _ <;> rcases hau : d.cfg.auth with _ | _ <;>
                  (try simp only [ServerCfg.val, hau]) <;> (try wp_auto)
                all_goals (repeat' wp_if_destruct)
                all_goals first | err_exit | skip
                all_goals (
                  wp_for_post
                  iframe
                  iexists (j + 1), _, _
                  rw [hw]
                  iframe
                  ipureintro
                  refine ⟨by omega, fun w hw' => ?_, fun hnb => ?_⟩
                  · rw [htake, List.mem_append, List.mem_singleton] at hw'
                    rcases hw' with hw' | rfl
                    · have h := Hf2 w hw'
                      first | exact h | (simp only [hau] at h; exact h) | simpa [hau] using h
                    clear hNameOk hNames hBounds hAddr hNodeCount hIds hCompat hAuth hErrorf
                    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp_all
                  · rw [htake]
                    first
                      | exact ⟨ww, List.mem_append_right _ (List.mem_singleton_self _), hal⟩
                      | (obtain ⟨w, hw', hk⟩ := Hf3 hnb
                         exact ⟨w, List.mem_append_left _ hw', hk⟩))
              · have Hif' : ¬ sint.Z (W64 (j : Int)) < sint.Z v.Workloads'.len := by
                  first
                    | exact Hif
                    | exact of_decide_eq_false (GoGlobalContext.intoVal_inj_bool Hif)
                    | (intro h; apply Hif; rw [decide_eq_true h])
                -- the loop's exit `if` may be left as `¬ #(decide _) = #true`: reduce it, so that the
                -- checks' `wp_if_destruct` below do not split on it again
                try simp only [decide_eq_false Hif', _root_.decide_true, ↓reduceIte]
                have hjl := idx_end _ _ _ Hlw.1 Hlw.2 Hif' Hf1
                subst hjl
                rw [List.take_length] at Hf2 Hf3
                -- the token provider only with a workload that needs it: `c.Auth && !needed` fails; then
                -- only with the compactor off: `c.Auth && c.Retention != 0` fails
                rcases hau : d.cfg.auth with _ | _ <;> rcases hnb : nb with _ | _ <;>
                  (try simp only [ServerCfg.val, hau]) <;> (try wp_auto)
                all_goals (repeat' wp_if_destruct)
                all_goals first | err_exit | skip
                all_goals (
                have hneed : d.cfg.auth = true → ∃ w ∈ d.workloads, kindAlone w.kind = true := by
                  intro ha
                  first | exact Hf3 hnb | (rw [hau] at ha; exact absurd ha (by decide))
                -- the token provider only with the compactor off: `c.Auth && c.Retention != 0` fails
                have hacmp : d.cfg.auth = true → d.cfg.retention = W64 0 := by
                  intro ha
                  first | (rw [hau] at ha; exact absurd ha (by decide)) | exact ‹d.cfg.retention = W64 0›
                iapply HΦ
                ipureintro
                intro _
                clear hNameOk hNames hBounds hAddr hNodeCount hIds hCompat hAuth hErrorf
                have hpeers : ∀ m ∈ d.members, Net.addrOk m.peer = true := fun m hm =>
                  (Hok.2.2 m.peer (List.mem_append_left _ (List.mem_flatMap.2 ⟨m, hm, by simp⟩))).1
                apply goWellFormed_sound
                refine ⟨hmem, Hj3, fun m hm => (Hj4 m hm).1, Hk2, hnl', fun a ha => (Hok.2.2 a ha).1,
                  Hok.2.1, ?_, hbid hpeers rfl, htok0, hsnap, hcatch, hret, hbc rfl,
                  fun w hw => (Hf2 w hw).1, fun w hw => (Hf2 w hw).2.1, fun w hw => (Hf2 w hw).2.2,
                  hneed, hacmp, hmax, fun m hm => (Hj4 m hm).2, fun a ha => (Hok.2.2 a ha).2, ?_⟩
                · intro j' w ns hw hns
                  exact Hn3 j' w ns (List.getElem?_eq_some_iff.1 hw).1 hw hns
                · unfold etcd_dist.typed.maxLen; rw [← htok]; exact htokl))
      · rw [decide_eq_false hnl]
        (try simp only [Bool.not_false])
        err_exit

end proof

end etcd_dist
end EtcdGrove
end Perennial
