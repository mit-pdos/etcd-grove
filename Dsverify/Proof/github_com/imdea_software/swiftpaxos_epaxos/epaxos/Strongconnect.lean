/-
`(*Exec).strongconnect(v, index)` (exec.go) against `StrongconnectSpec`: Tarjan's search with
the pure invariant of `Tarjan.lean`, the components executed at their pop with the model's
executor steps.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ExecLemmas
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.InStack
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.NodeArray

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof tarjan

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

omit [GoGlobalContext] [hG : HeapGS .hasLC GF] [go.Semantics] [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS] in
/-- (stage 2, S3) A client SCAN's value is its count's 8 bytes (`Execute`'s premise). -/
theorem opCmdOk_scan_len {c : WCmd} (h : OpCmdOk c) (hs : c.op = opSCAN) : 8 ≤ c.val.length := by
  rcases h.2 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, n, -, hv⟩
  · rw [hs] at h1; exact absurd h1 (by decide)
  · rw [hs] at h1; exact absurd h1 (by decide)
  · simp [hv, u64Le_length]

set_option maxHeartbeats 4000000 in
theorem wp_strongconnect (hEx : state.Command.Execute.spec (GF := GF))
    (hRP : replica.Replica.ReplyProposeTS.spec (GF := GF)) (γ : EpNames) (i : Nat) (r e rr : Loc)
    (L : List GoString) (p : FwPtrs) (Rext : IProp GF) :
    StrongconnectSpec (GF := GF) γ i r e rr L p Rext := by
  intro F σ t v idxp wv hok hvis hv hc hroot hedge
  iloeb as IH generalizing %σ %t %v %idxp %wv %hok %hvis %hv %hc %hroot %hedge
  wp_start as ⟨#Hctx, Hheap⟩
  obtain ⟨hwf, hib, hi, hT, hcnt⟩ := hok
  obtain ⟨hvq, hvi⟩ := hwf.ids v wv hv
  unfold exHeap stackOwn
  icases Hheap with ⟨Hins, Heut, Hstore, ⟨%s, Hst, Hs, Hcap, %Hcap0⟩, Hidx, Hfrag, Hpend, Hcur⟩
  icases repInstsX_acc γ i r F σ.inst t.ix v hvq (by omega) $$ Hins with
    ⟨%iss, %rows, %row, #Hiss, #Hrows, %Hrow, Hrow, %Hp, Hx, Hclose⟩
  rw [hv]
  have hixv : t.ix v = none := by unfold St.vis at hvis; simpa using hvis
  rw [hixv]
  unfold slotT ownInstT ownInstG
  icases Hx with ⟨%y, Hy, %Hyf, Hyrest⟩
  wp_auto
  -- the push (growing the stack when full)
  have hSl := stack_le_n hT hcnt
  have hnb := visCount_bound hcnt
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hcw := ownSliceCap_wf (V := Loc) _ _ $$ Hcap
  simp only [List.length_map] at Hsl
  have hsl : (t.S.length : Int) = sint.Z s.len := by
    rw [Hsl.1]; exact Int.toNat_of_nonneg Hsl.2
  have hlen_small : sint.Z s.len < 2 ^ 40 := by
    unfold nR MAX_INSTANCE at hnb; omega
  wp_join iprop(∃ s1 : GoSlice, structFieldRef epaxos.Exec go!"stack" e ↦ s1 ∗
      s1 ↦* t.S.map (ptrOf F) ∗ ownSliceCap Loc s1 (DFrac.own 1) ∗
      l_ptr ↦ s.len ∗ e_ptr ↦ e ∗ ⌜s1.len = s.len ∧ sint.Z s.len < sint.Z s1.cap⌝)
      with [Hst Hs Hcap l e] as ⟨%s1, Hst, Hs, Hcap, l, e, %Hs1⟩
  · -- full: `make([]*Instance, l, 2*l)` and `copy`
    have h2 : sint.Z (W64 2 * s.len) = 2 * sint.Z s.len := by word
    wp_apply (wp_slice_make3 (V := Loc) s.len (W64 2 * s.len) ⟨Hcw.1, by rw [h2]; omega⟩)
      as %ns ⟨Hns, Hncap, %Hnc⟩
    wp_apply wp_slice_copy ns _ s _ _ $$ [$Hns $Hs] as %k ⟨%Hk, Hns, Hs⟩
    wp_join_done
    ihave %Hnl := ownSlice_len _ _ _ $$ Hns
    have hl : sint.nat s.len = t.S.length := Hsl.1.symm
    have e3 : List.take (List.replicate (sint.nat s.len) (zero_val Loc)).length (t.S.map (ptrOf F)) ++
        List.drop (t.S.map (ptrOf F)).length (List.replicate (sint.nat s.len) (zero_val Loc)) =
        t.S.map (ptrOf F) := by
      rw [List.length_replicate, List.length_map, hl, List.take_of_length_le (by simp),
        List.drop_eq_nil_of_le (by simp), List.append_nil]
    rw [e3] at Hnl
    irevert Hns; rw [e3]; iintro Hns
    iexists ns
    iframe Hst Hncap l e
    isplitl [Hns]
    · iexact Hns
    ipureintro
    simp only [List.length_map] at Hnl
    constructor
    · apply BitVec.toInt_inj.mp
      have := Hnl.1; have := Hnl.2; have := Hsl.1; have := Hsl.2
      simp only [sint.nat, sint.Z] at *; omega
    · rw [Hnc, h2]; have := Hcap0; rw [← Hif] at this; omega
  · iexists s; iframe; ipureintro; refine ⟨rfl, ?_⟩
    have := Hcw.2
    rcases Int.lt_or_eq_of_le this with h | h
    · exact h
    · exact absurd (BitVec.toInt_inj.mp h) Hif
  -- `e.stack = e.stack[0 : l+1]; e.stack[l] = v`
  have hl1 : sint.Z (s.len + W64 1) = sint.Z s.len + 1 := by word
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (s.len + W64 1) ∧
      sint.Z (s.len + W64 1) ≤ sint.Z s1.cap := by
    rw [hl1]; refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega, by omega⟩
  simp only [hb, _root_.and_self, ↓reduceIte]
  ihave ⟨%vc, -, Hs, Hcap⟩ := ownSlice_slice_into_capacity (W64 0) (s.len + W64 1) s1 _ $$ [Hs Hcap]
  · iframe; ipureintro
    rw [Hs1.1, hl1]; refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega, by omega, by omega⟩
  wp_auto
  ihave %Hsl2 := ownSlice_len _ _ _ $$ Hs
  rw [show sint.nat (W64 0) = 0 by rfl, List.drop_zero] at Hsl2
  irevert Hs; rw [show sint.nat (W64 0) = 0 by rfl, List.drop_zero]; iintro Hs
  have hvc : vc.length = 1 := by
    have h1 := Hsl2.1
    simp only [List.length_append, List.length_map, slice.slice] at h1
    rw [show s.len + W64 1 - W64 0 = s.len + W64 1 by word] at h1
    have : sint.nat (s.len + W64 1) = sint.nat s.len + 1 := by
      show (sint.Z (s.len + W64 1)).toNat = (sint.Z s.len).toNat + 1; rw [hl1]; omega
    omega
  have hix : 0 ≤ sint.Z s.len ∧ sint.Z s.len < sint.Z (s.len + W64 1 - W64 0) := by
    rw [show s.len + W64 1 - W64 0 = s.len + W64 1 by word, hl1]; omega
  simp only [hix, _root_.and_self, ↓reduceIte]
  wp_apply wp_store_slice_index _ (sint.Z s.len) _ (ptrOf F v) $$ [$Hs] as Hs
  · ipureintro; simp only [List.length_append, List.length_map, hvc]; omega
  have hset : (t.S.map (ptrOf F) ++ vc).set (sint.Z s.len).toNat (ptrOf F v) =
      (t.S ++ [v]).map (ptrOf F) := by
    obtain ⟨c, rfl⟩ : ∃ c, vc = [c] := by
      match vc, hvc with
      | [c], _ => exact ⟨c, rfl⟩
    rw [show (sint.Z s.len).toNat = (t.S.map (ptrOf F)).length by simp; omega]
    simp
  rw [hset]
  -- `v.Cmds == nil`
  icases Hyrest with ⟨#Hid, Hcmds, Hdeps, Hlb⟩
  have hidx : W64 (t.n : Int) + W64 1 = W64 ((t.push v).n : Int) := by
    show W64 (t.n : Int) + W64 1 = W64 ((t.n + 1 : Nat) : Int); push_cast; word
  have hpix : upd t.ix v (some (t.n, t.n)) = (t.push v).ix := by
    funext x; by_cases h : x = v <;> simp [upd, St.push, h]
  have hpS : (t.push v).S = t.S ++ [v] := rfl
  rcases hcv : wv.cmds with _ | cs
  · -- `nil`: return false
    unfold cmdsRep; icases Hcmds with %Hnil
    rw [Hnil]
    simp only [decide_true]
    wp_auto
    ihave Hins := Hclose $$ %(some wv) %(some (t.n, t.n)) Hrow [Hy Hid Hdeps Hlb]
    · dsimp only; iexists _; iframe Hy Hid Hdeps Hlb
      isplitr
      · ipureintro; exact ⟨Hyf.1, Hyf.2.1, Hyf.2.2.1, Hyf.2.2.2.1, rfl, rfl⟩
      rw [hcv]; ipureintro; rfl
    rw [upd_self _ _ _ hv, hpix]
    iapply HΦ
    iexists σ, t.push v
    rw [hidx, hpS]
    iframe Hins Heut Hstore Hidx Hfrag Hpend Hcur
    isplitl [Hst Hs Hcap]
    · iexists _; iframe Hst Hs Hcap; ipureintro
      simp only [slice.slice]; rw [show s1.cap - W64 0 = s1.cap by word]; have := Hs1.2; omega
    ipureintro
    refine ⟨ExRel.refl σ, hwf, hib, push_visCount hcnt hvis hvq (by omega), push_ext hvis,
      by show t.n ≤ t.n + 1; omega, push_winv hT v, fun x hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨-, -, -, -, w, hw, -⟩ := hT.onS x hx; exact ⟨w, hw⟩
    · simp at hx; subst hx; exact ⟨wv, hv⟩
  -- not `nil`: `v` is pushed, the invariant holds
  unfold cmdsRep
  icases Hcmds with ⟨%Hnn, #Hcmds⟩
  simp only [Hnn, decide_false]
  wp_auto
  ihave Hins := Hclose $$ %(some wv) %(some (t.n, t.n)) Hrow [Hy Hid Hdeps Hlb]
  · dsimp only; iexists _; iframe Hy Hid Hdeps Hlb
    isplitr
    · ipureintro; exact ⟨Hyf.1, Hyf.2.1, Hyf.2.2.1, Hyf.2.2.2.1, rfl, rfl⟩
    rw [hcv]; isplitr
    · ipureintro; exact Hnn
    · iexact Hcmds
  rw [upd_self _ _ _ hv, hpix]
  have hn0 : 0 < t.n := by obtain ⟨V, -, -, hn, -⟩ := hcnt; omega
  have hrdv : σ.ready v := ⟨wv, hv, hc, by rw [hcv]; simp⟩
  have hexv : ¬ σ.executed v := by
    rintro ⟨w', hw', hs⟩; rw [hv] at hw'; cases hw'; rw [hc] at hs; revert hs; decide
  have hT1 : TInv (gr σ) (t.push v) := push_inv hT hvis hexv hrdv hroot hedge hn0
  ihave #Hro' := Hctx
  unfold exCtx
  icases Hro' with ⟨#Hpk, #Hpkr, #Hpks, #Hpkso, #Hrr, #Hro, #Hfw, #Htc, #Hex, #Her, #Hinv⟩
  ihave ⟨#HN, -, -, #HSt, -, -, -, -, #HDr, -, -, -, -, %HLn⟩ := fwRO_fields _ _ _ _ _ $$ Hro
  have hNn : L.length = nR := HLn.1
  -- the edge loops' invariant
  ihave HI : (∃ (qv : w32) (σc : RState) (tc : St InstId),
      "q" ∷ q_ptr ↦ qv ∗
      "Hins" ∷ repInstsX γ i r F σc.inst tc.ix ∗
      "Heut" ∷ repRowArr r go!"ExecedUpTo" σc.execedUpTo ∗
      "Hstore" ∷ repStore r σc.store ∗
      "Hfrag" ∷ repFrag γ i σc ∗ "Hpend" ∷ pendFrag γ i none ∗ "Hcur" ∷ curFrag γ i [] 0 ∗
      "Hidx" ∷ idxp ↦ W64 (tc.n : Int) ∗
      "Hstk" ∷ (∃ s2 : GoSlice, structFieldRef epaxos.Exec go!"stack" e ↦ s2 ∗
        s2 ↦* tc.S.map (ptrOf F) ∗ ownSliceCap Loc s2 (DFrac.own 1) ∗ ⌜0 < sint.Z s2.cap⌝) ∗
      "%Hq" ∷ ⌜0 ≤ zz qv ∧ zz qv ≤ nR ∧
        LoopOk σ t v σc tc (fun y => (y.q : Int) < zz qv)⌝ : IProp GF)
      $$ [q Hins Heut Hstore Hfrag Hpend Hcur Hidx Hst Hs Hcap]
  · iexists W32 0, σ, t.push v
    rw [hidx, hpS]
    iframe q Hins Heut Hstore Hfrag Hpend Hcur Hidx
    isplitl [Hst Hs Hcap]
    · iexists _; iframe Hst Hs Hcap; ipureintro
      simp only [slice.slice]; rw [show s1.cap - W64 0 = s1.cap by word]; have := Hs1.2; omega
    ipureintro
    refine ⟨by decide, by unfold nR; decide, ExRel.refl σ, hwf, hib,
      push_visCount hcnt hvis hvq (by omega), push_ext hvis, by show t.n + 1 ≤ t.n + 1; omega,
      hT1, rfl, ⟨t.n, by simp [St.push]⟩, by simp [St.push], ⟨[], rfl⟩, fun y _ hy => ?_⟩
    simp only [zz, show sint.Z (W32 0) = 0 from rfl] at hy; omega
  wp_for HI
  obtain ⟨Hq0, HqN, Hlp⟩ := Hq
  simp only [zz] at Hq0 HqN
  have hNz : sint.Z (W32 (sint.Z (W64 (L.length : Int)))) = (nR : Int) := by
    rw [hNn]; unfold nR; decide
  rw [hNz]
  wp_if_destruct
  · -- an iteration of the outer loop: row `q`
    have HifQ := Hif
    have hvS : v ∈ tc.S := Hlp.inv.actS v (by rw [Hlp.act]; simp)
    obtain ⟨-, -, -, hvex, wv', hwv', hwvc, -⟩ := Hlp.inv.onS v hvS
    obtain ⟨lv, hlv⟩ := Hlp.ixv
    have hdeps : wv'.deps = wv.deps := by
      have := Hlp.rel.deps v; rw [hwv', hv] at this; simpa using this
    have hdok : depsOk wv.deps := by
      rw [← hdeps]; apply Hlp.wf.deps v wv' hwv'; rw [hwvc]; decide
    have hqn : (sint.Z qv).toNat < nR := by omega
    obtain ⟨d, hd⟩ : ∃ d, wv.deps[(sint.Z qv).toNat]? = some d :=
      ⟨_, List.getElem?_eq_getElem (by rw [hdok.1]; exact hqn)⟩
    icases repInstsX_acc γ i r F σc.inst tc.ix v hvq (by omega) $$ Hins with
      ⟨%iss1, %rows1, %row1, #Hiss1, #Hrows1, %Hrow1, Hrow, %Hp1, Hx, Hclose⟩
    rw [hwv', hlv]
    dsimp only [slotT, ownInstT, ownInstG]
    icases Hx with ⟨%y1, Hy, %Hyf1, #Hid1, Hcmds1, ⟨%dq, Hdeps1⟩, Hlb1⟩
    wp_auto
    ihave %Hdl := ownSlice_len _ _ _ $$ Hdeps1
    have eq1 : sint.Z (W64 (sint.Z qv)) = sint.Z qv := by word
    have hb1 : 0 ≤ sint.Z (W64 (sint.Z qv)) ∧ sint.Z (W64 (sint.Z qv)) < sint.Z y1.Deps'.len := by
      rw [eq1]; have h1 := Hdl.1; rw [hdeps, hdok.1] at h1
      have : ((nR : Nat) : Int) = sint.Z y1.Deps'.len := by rw [h1]; exact Int.toNat_of_nonneg Hdl.2
      omega
    simp only [hb1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ _ _ _ d hb1.1 $$ [$Hdeps1] as Hdeps1
    · ipureintro; rw [eq1, hdeps]; exact hd
    ihave Hins := Hclose $$ %(some wv') %(some (t.n, lv)) Hrow [Hy Hid1 Hcmds1 Hdeps1 Hlb1]
    · dsimp only; iexists y1; iframe Hy Hid1 Hcmds1 Hlb1
      isplitr
      · ipureintro; exact Hyf1
      iexists dq; iexact Hdeps1
    rw [upd_self _ _ _ hwv', upd_self _ _ _ hlv]
    unfold repRowArr
    icases Heut with ⟨%eut, #Heutf, Heutsl⟩
    ihave %Heutl := ownSlice_len _ _ _ $$ Heutsl
    wp_auto
    have hb2 : 0 ≤ sint.Z (W64 (sint.Z qv)) ∧ sint.Z (W64 (sint.Z qv)) < sint.Z eut.len := by
      rw [eq1]; have h1 := Heutl.1; simp only [List.length_map, List.length_range] at h1
      have : ((nR : Nat) : Int) = sint.Z eut.len := by rw [h1]; exact Int.toNat_of_nonneg Heutl.2
      omega
    simp only [hb2, _root_.and_self, ↓reduceIte]
    have hqN : (sint.Z qv).toNat < nR := hqn
    wp_apply wp_load_slice_index _ _ _ _ (σc.execedUpTo (sint.Z qv).toNat) hb2.1 $$ [$Heutsl] as Heutsl
    · ipureintro; rw [eq1]; simp [hqN]
    obtain ⟨heu1, heu2⟩ := Hlp.wf.exLo _ hqN
    obtain ⟨eu, heu⟩ : ∃ eu, σc.execedUpTo (sint.Z qv).toNat = eu := ⟨_, rfl⟩
    rw [heu] at heu1 heu2 ⊢
    have heu1' : sint.Z (eu + W32 1) = zz eu + 1 := by
      simp only [zz] at *; unfold MAX_INSTANCE at heu2; word
    ihave HJ : (∃ (iv : w32) (σc' : RState) (tc' : St InstId),
        "i" ∷ i_ptr ↦ iv ∗
        "Hins" ∷ repInstsX γ i r F σc'.inst tc'.ix ∗
        "Hstore" ∷ repStore r σc'.store ∗
        "Hfrag" ∷ repFrag γ i σc' ∗ "Hpend" ∷ pendFrag γ i none ∗ "Hcur" ∷ curFrag γ i [] 0 ∗
        "Hidx" ∷ idxp ↦ W64 (tc'.n : Int) ∗
        "Hstk" ∷ (∃ s2 : GoSlice, structFieldRef epaxos.Exec go!"stack" e ↦ s2 ∗
          s2 ↦* tc'.S.map (ptrOf F) ∗ ownSliceCap Loc s2 (DFrac.own 1) ∗ ⌜0 < sint.Z s2.cap⌝) ∗
        "%Hj" ∷ ⌜zz eu + 1 ≤ zz iv ∧ (zz iv ≤ zz d + 1 ∨ zz iv = zz eu + 1) ∧
          σc'.execedUpTo = σc.execedUpTo ∧
          LoopOk σ t v σc' tc' (fun y => (y.q : Int) < zz qv ∨
            ((y.q : Int) = zz qv ∧ (y.i : Int) < zz iv))⌝ : IProp GF)
        $$ [«i» Hins Hstore Hfrag Hpend Hcur Hidx Hstk]
    · iexists eu + W32 1, σc, tc
      iframe
      ipureintro
      refine ⟨by rw [← heu1']; simp only [zz]; omega, Or.inr (by simp only [zz] at *; omega), rfl, ?_⟩
      refine ⟨Hlp.rel, Hlp.wf, Hlp.ib, Hlp.cnt, Hlp.ext, Hlp.n, Hlp.inv, Hlp.act, Hlp.ixv, Hlp.parv, Hlp.stk,
        fun y he hy => ?_⟩
      rcases hy with hy | ⟨hyq, hyi⟩
      · exact Hlp.done y he hy
      · -- below `ExecedUpTo[q] + 1`: executed
        left
        have hy' : (y.i : Int) ≤ zz eu := by simp only [zz] at hyi ⊢; rw [heu1'] at hyi; simp only [zz] at hyi; omega
        have hyq' : y.q = (sint.Z qv).toNat := by simp only [zz] at hyq; omega
        have := Hlp.wf.exUp _ hqN y.i (by rw [heu]; exact hy')
        rw [← hyq'] at this; exact this
    wp_for HJ
    obtain ⟨Hj1, Hj2, Hjeu, Hjl⟩ := Hj
    wp_if_destruct
    · -- an edge `v → (q, i)`
      have hd0 : 0 ≤ zz iv := by have := heu1; simp only [zz] at *; omega
      have hdok' := hdok.2 d (List.mem_of_getElem? hd)
      have hxi : toN iv + 1 < MAX_INSTANCE := by
        rcases hdok' with h | h <;> simp only [toN, zz] at * <;> omega
      have hxq : toN qv < nR := hqn
      have eqi : sint.Z (W64 (sint.Z iv)) = sint.Z iv := by word
      icases repInstsX_acc γ i r F σc'.inst tc'.ix ⟨toN qv, toN iv⟩ hxq (by simp only; omega) $$ Hins
        with ⟨%iss2, %rows2, %row2, #Hiss2, #Hrows2, %Hrow2, Hrow, %Hp2, Hx, Hclose⟩
      ihave %Hrl2 := ownSlice_len _ _ _ $$ Hrows2
      ihave %Hpl2 := ownSlice_len _ _ _ $$ Hrow
      icombine Hiss1 Hiss2 gives %Heqi
      subst Heqi
      ihave %Heqr := ownSlice_agree _ _ _ _ _ $$ Hrows1 Hrows2
      subst Heqr
      have hq1 : 0 ≤ sint.Z (W64 (sint.Z qv)) ∧ sint.Z (W64 (sint.Z qv)) < sint.Z iss1.len := by
        rw [eq1]; have hl := (List.getElem?_eq_some_iff.mp Hrow2).1
        have : (rows1.length : Int) = sint.Z iss1.len := by
          rw [Hrl2.1]; exact Int.toNat_of_nonneg Hrl2.2
        simp only [toN] at hl; constructor <;> omega
      have hi2 : 0 ≤ sint.Z (W64 (sint.Z iv)) ∧ sint.Z (W64 (sint.Z iv)) < sint.Z row2.len := by
        rw [eqi]; have h1 := Hpl2.1; have := Hp2
        have hl := (List.getElem?_eq_some_iff.mp Hp2).1
        have : ((F (toN qv)).length : Int) = sint.Z row2.len := by
          rw [h1]; exact Int.toNat_of_nonneg Hpl2.2
        have h0 : 0 ≤ sint.Z iv := hd0
        have hiv : ((toN iv : Nat) : Int) = sint.Z iv := Int.toNat_of_nonneg h0
        simp only at hl
        constructor <;> omega
      -- the slot's pointer, read
      have Hrd : ((rows1[(sint.Z (W64 (sint.Z qv))).toNat]? = some row2) ∧
          ((F (toN qv))[(sint.Z (W64 (sint.Z iv))).toNat]? = some (ptrOf F ⟨toN qv, toN iv⟩))) := by
        rw [eq1, eqi]; exact ⟨Hrow2, Hp2⟩
      simp only [hq1, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index iss1 _ rows1 _ row2 hq1.1 $$ [$Hrows1] as -
      · ipureintro; exact Hrd.1
      simp only [hi2, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index row2 _ _ _ _ hi2.1 $$ [$Hrow] as Hrow
      · ipureintro; exact Hrd.2
      -- the return `false` of the edge loop (state unchanged)
      have hfalse : ∀ x ∈ tc'.S, ∃ w, σc'.inst x = some w := fun x hx => by
        obtain ⟨-, -, -, -, w, hw, -⟩ := Hjl.inv.onS x hx; exact ⟨w, hw⟩
      rcases hxw : σc'.inst ⟨toN qv, toN iv⟩ with _ | w
      case none =>
        unfold slotT; icases Hx with %Hnull
        rw [Hnull]; simp only [decide_true]
        wp_auto
        ihave Hins := Hclose $$ %none %(tc'.ix ⟨toN qv, toN iv⟩) Hrow []
        · ipureintro; trivial
        rw [← hxw, upd_self _ _ _ rfl, upd_self _ _ _ rfl]
        wp_for_post
        wp_for_post
        iapply HΦ
        iexists σc', tc'
        iframe
        isplitl [Heutsl]
        · iexists eut; rw [Hjeu]; iframe Heutf Heutsl
        ipureintro
        exact ⟨Hjl.rel, Hjl.wf, Hjl.ib, Hjl.cnt, Hjl.ext, by have := Hjl.n; omega,
          Hjl.inv.winv, hfalse⟩
      case some =>
        dsimp only [slotT, ownInstT, ownInstG]
        icases Hx with ⟨%y2, Hy2, %Hyf2, #Hid2, Hcmds2, Hdeps2, Hlb2⟩
        ihave %Hnn2 := typedPointsto_not_null _ _ _ $$ Hy2
        simp only [Hnn2, decide_false]
        wp_auto
        simp only [hq1, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index iss1 _ rows1 _ row2 hq1.1 $$ [$Hrows1] as -
        · ipureintro; exact Hrd.1
        simp only [hi2, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index row2 _ _ _ _ hi2.1 $$ [$Hrow] as Hrow
        · ipureintro; exact Hrd.2
        unfold cmdsRep
        rcases hcw : w.cmds with _ | cw
        case none =>
          icases Hcmds2 with %Hcn
          rw [Hcn]; simp only [decide_true]
          wp_auto
          ihave Hins := Hclose $$ %(some w) %(tc'.ix ⟨toN qv, toN iv⟩) Hrow [Hy2 Hid2 Hdeps2 Hlb2]
          · dsimp only; iexists y2; iframe Hy2 Hid2 Hdeps2 Hlb2
            isplitr
            · ipureintro; exact Hyf2
            rw [hcw]; ipureintro; exact Hcn
          rw [← hxw, upd_self _ _ _ rfl, upd_self _ _ _ rfl]
          wp_for_post
          wp_for_post
          iapply HΦ
          iexists σc', tc'
          iframe
          isplitl [Heutsl]
          · iexists eut; rw [Hjeu]; iframe Heutf Heutsl
          ipureintro
          exact ⟨Hjl.rel, Hjl.wf, Hjl.ib, Hjl.cnt, Hjl.ext, by have := Hjl.n; omega,
            Hjl.inv.winv, hfalse⟩
        case some =>
          icases Hcmds2 with ⟨%Hcnn, #Hcmds2⟩
          simp only [Hcnn, decide_false]
          wp_auto
          simp only [hq1, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index iss1 _ rows1 _ row2 hq1.1 $$ [$Hrows1] as -
          · ipureintro; exact Hrd.1
          simp only [hi2, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index row2 _ _ _ _ hi2.1 $$ [$Hrow] as Hrow
          · ipureintro; exact Hrd.2
          have hiv1 : zz (iv + W32 1) = zz iv + 1 := by
            have := hdok'; simp only [toN, zz] at *; unfold MAX_INSTANCE at *; rcases this with h | h <;> word
          wp_if_destruct
          · -- executed: `continue`
            ihave Hins := Hclose $$ %(some w) %(tc'.ix ⟨toN qv, toN iv⟩) Hrow [Hy2 Hid2 Hcmds2 Hdeps2 Hlb2]
            · dsimp only; iexists y2; iframe Hy2 Hid2 Hdeps2 Hlb2
              isplitr
              · ipureintro; exact Hyf2
              rw [hcw]; isplitr
              · ipureintro; exact Hcnn
              · iexact Hcmds2
            rw [← hxw, upd_self _ _ _ rfl, upd_self _ _ _ rfl]
            wp_for_post
            iframe
            iexists iv + W32 1, σc', tc'
            iframe
            ipureintro
            refine ⟨by rw [hiv1]; omega, Or.inl (by rw [hiv1]; simp only [zz] at *; omega), Hjeu, ?_⟩
            refine ⟨Hjl.rel, Hjl.wf, Hjl.ib, Hjl.cnt, Hjl.ext, Hjl.n, Hjl.inv, Hjl.act, Hjl.ixv,
              Hjl.parv, Hjl.stk, fun y he hy => ?_⟩
            rw [hiv1] at hy
            by_cases hy' : (y.q : Int) < zz qv ∨ ((y.q : Int) = zz qv ∧ (y.i : Int) < zz iv)
            · exact Hjl.done y he hy'
            · left
              have hyx : y = ⟨toN qv, toN iv⟩ := by
                obtain ⟨q', i'⟩ := y
                simp only [InstId.mk.injEq, toN, zz] at *; omega
              subst hyx
              exact ⟨w, hxw, by rw [← Hyf2.2.2.1]; exact Hif⟩
          wp_for
          simp only [hq1, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index iss1 _ rows1 _ row2 hq1.1 $$ [$Hrows1] as -
          · ipureintro; exact Hrd.1
          simp only [hi2, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index row2 _ _ _ _ hi2.1 $$ [$Hrow] as Hrow
          · ipureintro; exact Hrd.2
          wp_if_destruct
          · -- not committed: return false
            ihave Hins := Hclose $$ %(some w) %(tc'.ix ⟨toN qv, toN iv⟩) Hrow [Hy2 Hid2 Hcmds2 Hdeps2 Hlb2]
            · dsimp only; iexists y2; iframe Hy2 Hid2 Hdeps2 Hlb2
              isplitr
              · ipureintro; exact Hyf2
              rw [hcw]; isplitr
              · ipureintro; exact Hcnn
              · iexact Hcmds2
            rw [← hxw, upd_self _ _ _ rfl, upd_self _ _ _ rfl]
            wp_for_post
            wp_for_post
            wp_for_post
            iapply HΦ
            iexists σc', tc'
            iframe
            isplitl [Heutsl]
            · iexists eut; rw [Hjeu]; iframe Heutf Heutsl
            ipureintro
            exact ⟨Hjl.rel, Hjl.wf, Hjl.ib, Hjl.cnt, Hjl.ext, by have := Hjl.n; omega,
              Hjl.inv.winv, hfalse⟩
          have hcom : y2.Status' = W8 4 :=
            Classical.byContradiction fun h => Hif (by rw [decide_eq_false h]; rfl)
          have hwc : w.status = stCOMMITTED := by rw [← Hyf2.2.2.1, hcom]; rfl
          simp only [hcom, _root_.decide_true, Bool.not_true, ↓reduceIte]
          wp_auto
          simp only [hq1, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index iss1 _ rows1 _ row2 hq1.1 $$ [$Hrows1] as -
          · ipureintro; exact Hrd.1
          simp only [hi2, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index row2 _ _ _ _ hi2.1 $$ [$Hrow] as Hrow
          · ipureintro; exact Hrd.2
          have hxS_or : tc'.ix ⟨toN qv, toN iv⟩ = none ∨ ⟨toN qv, toN iv⟩ ∈ tc'.S := by
            rcases hix : tc'.ix ⟨toN qv, toN iv⟩ with _ | a
            · exact Or.inl rfl
            · right; apply Hjl.inv.visS
              · unfold St.vis; rw [hix]; rfl
              · rintro ⟨w', hw', hs⟩; rw [hxw] at hw'; cases hw'; rw [hwc] at hs; revert hs; decide
          have hedgex : σc'.depEdge v ⟨toN qv, toN iv⟩ := by
            have hvS : v ∈ tc'.S := Hjl.inv.actS v (by rw [Hjl.act]; simp)
            obtain ⟨-, -, -, -, wv'', hwv'', -, -⟩ := Hjl.inv.onS v hvS
            have hdy : wv''.deps = wv.deps := by
              have := Hjl.rel.deps v; rw [hwv'', hv] at this; simpa using this
            refine ⟨wv'', hwv'', hxq, ?_⟩
            show ((toN iv : Nat) : Int) ≤ sint.Z ((wv''.deps.getD (toN qv) (W32 (-1))))
            rw [hdy, List.getD_eq_getElem?_getD, show toN qv = (sint.Z qv).toNat from rfl, hd,
              Option.getD_some]
            have : ((toN iv : Nat) : Int) = sint.Z iv := Int.toNat_of_nonneg hd0
            omega
          rcases hxS_or with hnone | hxS
          · -- unvisited: `Index == 0`, the recursive call
            have hI0 : y2.Index' = W64 0 := by
              have := Hyf2.2.2.2.2; rw [hnone] at this; exact this (by rw [hwc]; decide)
            rw [hI0]
            wp_auto
            ihave Hins := Hclose $$ %(some w) %none Hrow [Hy2 Hid2 Hcmds2 Hdeps2 Hlb2]
            · dsimp only; iexists y2; iframe Hy2 Hid2 Hdeps2 Hlb2
              isplitr
              · ipureintro; rw [← hnone]; exact Hyf2
              rw [hcw]; isplitr
              · ipureintro; exact Hcnn
              · iexact Hcmds2
            rw [← hxw, upd_self _ _ _ rfl, ← hnone, upd_self _ _ _ rfl]
            have hvisx : ¬ tc'.vis ⟨toN qv, toN iv⟩ := by unfold St.vis; rw [hnone]; simp
            have hlast : tc'.A.getLast? = some v := by rw [Hjl.act]; simp
            wp_method_call
            have hok' : SearchOk i σc' tc' := ⟨Hjl.wf, Hjl.ib, hi, Hjl.inv, Hjl.cnt⟩
            wp_apply IH $$ %σc' %tc' %(⟨toN qv, toN iv⟩ : InstId) %idxp %w [] [] [] [] [] [] [Hins Heutsl Hstore Hfrag Hpend Hcur Hidx Hstk]
              as %b ⟨%σ3, %t3, Hheap3, %Hpost3⟩
            · ipureintro; exact hok'
            · ipureintro; exact hvisx
            · ipureintro; exact hxw
            · ipureintro; exact hwc
            · ipureintro; intro h; rw [Hjl.act] at h; simp at h
            · ipureintro; intro a ha; rw [hlast] at ha; cases ha; exact hedgex
            · iframe Hctx Hins Hstore Hfrag Hpend Hcur Hidx Hstk
              iexists eut; rw [Hjeu]; iframe Heutf Heutsl
            -- the callee's result
            obtain ⟨hR3, hwf3, hib3, hcnt3, hext3, hn3, hb3⟩ := Hpost3
            icases Hheap3 with ⟨Hins, Heut3, Hstore, Hstk, Hidx, Hfrag, Hpend, Hcur⟩
            cases b
            · -- `false`: return false
              wp_auto
              wp_for_post
              wp_for_post
              iapply HΦ
              iexists σ3, t3
              iframe
              ipureintro
              exact ⟨Hjl.rel.trans hR3, hwf3, hib3, hcnt3, Hjl.ext.trans hext3,
                by have := Hjl.n; omega, by simpa using hb3⟩
            · -- `true`: `if w.Lowlink < v.Lowlink { v.Lowlink = w.Lowlink }`
              wp_auto
              obtain ⟨hT3, hsc3⟩ := hb3
              have hLo := LoopOk.callee Hjl hvis hR3 hwf3 hib3 hcnt3 hext3 hn3 hT3 hsc3 hvisx hedgex
              have hvS' : v ∈ tc'.S := Hjl.inv.actS v (by rw [Hjl.act]; simp)
              have hvv' : tc'.vis v := (Hjl.inv.onS v hvS').1
              obtain ⟨lv2, hlv2⟩ := Hjl.ixv
              have hlv3 : t3.ix v = some (t.n, lv2) := by rw [hext3.ix v hvv']; exact hlv2
              obtain ⟨lv', hly3, hcase3⟩ := hsc3
              have hlv'le : lv' ≤ tc'.n := by
                rcases hcase3 with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
              have hyv : (⟨toN qv, toN iv⟩ : InstId) ≠ v := fun h => hvisx (h ▸ hvv')
              -- the two instances exist in `σ3`
              have hex3 : ∀ x w0, σc'.inst x = some w0 → ∃ w3, σ3.inst x = some w3 := by
                intro x w0 h0
                rcases hR3.2 x with e | ⟨w1, -, e⟩
                · exact ⟨w0, by rw [e, h0]⟩
                · exact ⟨_, e⟩
              obtain ⟨wy3, hwy3⟩ := hex3 _ _ hxw
              obtain ⟨-, -, -, -, wv', hwv', -⟩ := Hjl.inv.onS v hvS'
              obtain ⟨wv3, hwv3⟩ := hex3 v _ hwv'
              -- the counter bounds the lowlinks
              have hb3n := visCount_bound hcnt3
              have hvS3 : v ∈ t3.S := by obtain ⟨T, hT⟩ := hext3.stk; rw [hT]; exact List.mem_append_left _ hvS'
              have hlv2le : lv2 ≤ t.n := by
                have := (hT3.lowW v hvS3).1; simp [St.low, St.num, hlv3] at this; exact this
              have hnn : t.n < tc'.n := by have := Hjl.n; omega
              have hsmall : tc'.n < 2 ^ 40 := by unfold nR MAX_INSTANCE at hb3n; omega
              icases repInstsX_acc2 γ i r F σ3.inst t3.ix ⟨toN qv, toN iv⟩ v hyv hxq (by simp only; omega)
                hvq (by omega) $$ Hins with ⟨Hxy, Hxv, Hclose2⟩
              rw [hwy3, hwv3, hly3, hlv3]
              dsimp only [slotT, ownInstT, ownInstG]
              icases Hxy with ⟨%y3, Hy3, %Hy3f, Hy3r⟩
              icases Hxv with ⟨%v3, Hv3, %Hv3f, Hv3r⟩
              wp_auto
              ihave Hins := Hclose2 $$ [Hy3 Hy3r] [Hv3 Hv3r]
              · iexists y3; iframe; ipureintro; exact Hy3f
              · iexists v3; iframe; ipureintro; exact Hv3f
              rw [Hy3f.2.2.2.2.2, Hv3f.2.2.2.2.2]
              have hcmp : sint.Z (W64 (lv' : Int)) < sint.Z (W64 (lv2 : Int)) ↔ lv' < lv2 := by
                rw [show sint.Z (W64 (lv' : Int)) = lv' by word, show sint.Z (W64 (lv2 : Int)) = lv2 by word]
                omega
              have hlowv3 : t3.low v = lv2 := by simp [St.low, hlv3]
              have hlowy3 : t3.low ⟨toN qv, toN iv⟩ = lv' := by simp [St.low, hly3]
              have hnumv3 : t3.num v = t.n := by simp [St.num, hlv3]
              wp_join iprop(repInstsX γ i r F σ3.inst (t3.merge t.A v ⟨toN qv, toN iv⟩).ix ∗
                  w_ptr ↦ ptrOf F ⟨toN qv, toN iv⟩ ∗ v_ptr ↦ ptrOf F v) with [Hins w v]
                as ⟨Hins, w, v⟩
              · -- `v.Lowlink = w.Lowlink`
                have hlt : lv' < lv2 := hcmp.mp Hif
                icases repInstsX_acc γ i r F σ3.inst t3.ix ⟨toN qv, toN iv⟩ hxq (by simp only; omega) $$ Hins
                  with ⟨%iss4, %rows4, %row4, #Hiss4, #Hrows4, %Hrow4, Hrow4, %Hp4, Hx4, Hclose4⟩
                rw [hwy3, hly3]
                dsimp only [slotT, ownInstT, ownInstG]
                icases Hx4 with ⟨%y4, Hy4, %Hy4f, Hy4r⟩
                wp_auto
                ihave Hins := Hclose4 $$ %(some wy3) %(some (tc'.n, lv')) Hrow4 [Hy4 Hy4r]
                · dsimp only; iexists y4; iframe; ipureintro; exact Hy4f
                rw [← hwy3, ← hly3, upd_self _ _ _ rfl, upd_self _ _ _ rfl]
                icases repInstsX_acc γ i r F σ3.inst t3.ix v hvq (by omega) $$ Hins
                  with ⟨%iss5, %rows5, %row5, #Hiss5, #Hrows5, %Hrow5, Hrow5, %Hp5, Hx5, Hclose5⟩
                rw [hwv3, hlv3]
                dsimp only [slotT, ownInstT, ownInstG]
                icases Hx5 with ⟨%y5, Hy5, %Hy5f, Hy5r⟩
                rw [Hy4f.2.2.2.2.2]
                wp_auto
                ihave Hins := Hclose5 $$ %(some wv3) %(some (t.n, lv')) Hrow5 [Hy5 Hy5r]
                · dsimp only; iexists _; iframe; ipureintro
                  exact ⟨Hy5f.1, Hy5f.2.1, Hy5f.2.2.1, Hy5f.2.2.2.1, Hy5f.2.2.2.2.1, rfl⟩
                rw [← hwv3, upd_self _ _ _ rfl]
                have hmix : (t3.merge t.A v ⟨toN qv, toN iv⟩).ix = upd t3.ix v (some (t.n, lv')) := by
                  funext x; rw [merge_ix, hnumv3, hlowv3, hlowy3, Nat.min_eq_right (Nat.le_of_lt hlt)]; rfl
                rw [hmix]
                iframe
                ipureintro; rfl
              · have hge : ¬ lv' < lv2 := fun h => Hif (hcmp.mpr h)
                have hmix : (t3.merge t.A v ⟨toN qv, toN iv⟩).ix = t3.ix := by
                  funext x; rw [merge_ix, hnumv3, hlowv3, hlowy3, Nat.min_eq_left (by omega)]
                  split
                  · subst_vars; exact hlv3.symm
                  · rfl
                rw [hmix]
                iframe
              have heu3 : σ3.execedUpTo = σc.execedUpTo := by rw [hR3.fields.2.2.2.1, Hjeu]
              icases Heut3 with ⟨%eut3, #Heutf3, Heutsl⟩
              icombine Heutf Heutf3 gives %Heq3
              subst Heq3
              rw [heu3]
              wp_for_post
              iframe
              iexists iv + W32 1, σ3, t3.merge t.A v ⟨toN qv, toN iv⟩
              have hmS : (t3.merge t.A v ⟨toN qv, toN iv⟩).S = t3.S := rfl
              rw [hmS]
              iframe
              ipureintro
              refine ⟨by rw [hiv1]; omega, Or.inl (by rw [hiv1]; simp only [zz] at *; omega), heu3, ?_⟩
              refine hLo.mono (fun z hz => ?_)
              rw [hiv1] at hz
              by_cases hz' : (z.q : Int) < zz qv ∨ ((z.q : Int) = zz qv ∧ (z.i : Int) < zz iv)
              · exact Or.inl hz'
              · right
                obtain ⟨q', i'⟩ := z
                simp only [InstId.mk.injEq, toN, zz] at *; omega
          · -- on the stack: `Index != 0`, `inStack`
            have hvisy : tc'.vis ⟨toN qv, toN iv⟩ := (Hjl.inv.onS _ hxS).1
            obtain ⟨⟨a, bl⟩, hab⟩ : ∃ ab, tc'.ix ⟨toN qv, toN iv⟩ = some ab :=
              Option.isSome_iff_exists.mp hvisy
            have ha0 : 0 < a := by have := (Hjl.inv.onS _ hxS).2.1; simp [St.num, hab] at this; exact this
            have han : a < tc'.n := by have := (Hjl.inv.onS _ hxS).2.2.1; simp [St.num, hab] at this; exact this
            have hsmall : tc'.n < 2 ^ 40 := by
              have := visCount_bound Hjl.cnt; unfold nR MAX_INSTANCE at this; omega
            have hIdx : y2.Index' = W64 a := by have := Hyf2.2.2.2.2; rw [hab] at this; exact this.1
            rw [hIdx]
            have hne0 : W64 (a : Int) ≠ W64 0 := by
              intro h; have := congrArg sint.Z h
              rw [show sint.Z (W64 (a : Int)) = a by word] at this; simp at this; omega
            simp only [hne0, decide_false]
            wp_auto
            ihave Hins := Hclose $$ %(some w) %(tc'.ix ⟨toN qv, toN iv⟩) Hrow [Hy2 Hid2 Hcmds2 Hdeps2 Hlb2]
            · dsimp only; iexists y2; iframe Hy2 Hid2 Hdeps2 Hlb2
              isplitr
              · ipureintro; exact Hyf2
              rw [hcw]; isplitr
              · ipureintro; exact Hcnn
              · iexact Hcmds2
            rw [← hxw, upd_self _ _ _ rfl, upd_self _ _ _ rfl]
            icases Hstk with ⟨%s5, Hst5, Hs5, Hcap5, %Hc5⟩
            wp_apply wp_inStack e s5 _ (ptrOf F ⟨toN qv, toN iv⟩) _ $$ [$Hst5 $Hs5] as ⟨Hst5, Hs5⟩
            rw [decide_eq_true (List.mem_map_of_mem hxS)]
            wp_auto
            -- `if w.Index < v.Lowlink { v.Lowlink = w.Index }`
            have hLo := LoopOk.stacked Hjl hvis hxS hedgex
            have hvS' : v ∈ tc'.S := Hjl.inv.actS v (by rw [Hjl.act]; simp)
            obtain ⟨lv2, hlv2⟩ := Hjl.ixv
            obtain ⟨-, -, -, -, wv', hwv', -⟩ := Hjl.inv.onS v hvS'
            have hlv2le : lv2 ≤ t.n := by
              have := (Hjl.inv.lowW v hvS').1; simp [St.low, St.num, hlv2] at this; exact this
            have hnn : t.n < tc'.n := by have := Hjl.n; omega
            have hnumy : tc'.num ⟨toN qv, toN iv⟩ = a := by simp [St.num, hab]
            have hlowv : tc'.low v = lv2 := by simp [St.low, hlv2]
            have hnumv : tc'.num v = t.n := by simp [St.num, hlv2]
            have hcmp : sint.Z (W64 (a : Int)) < sint.Z (W64 (lv2 : Int)) ↔ a < lv2 := by
              rw [show sint.Z (W64 (a : Int)) = a by word, show sint.Z (W64 (lv2 : Int)) = lv2 by word]
              omega
            wp_join iprop(repInstsX γ i r F σc'.inst
                (if tc'.num ⟨toN qv, toN iv⟩ < tc'.low v then tc'.setLow v (tc'.num ⟨toN qv, toN iv⟩)
                  else tc').ix ∗
                w_ptr ↦ ptrOf F ⟨toN qv, toN iv⟩ ∗ v_ptr ↦ ptrOf F v)
              at (if: _ then _ else _) with [Hins w v] as ⟨Hins, w, v⟩
            · by_cases hyv : (⟨toN qv, toN iv⟩ : InstId) = v
              · -- a self-edge: `v.Index < v.Lowlink` is false
                have ha : a = t.n := by rw [hyv, hlv2] at hab; cases hab; rfl
                have hnot : ¬ tc'.num ⟨toN qv, toN iv⟩ < tc'.low v := by rw [hnumy, hlowv]; omega
                rw [if_neg hnot]
                rw [hyv]
                icases repInstsX_acc γ i r F σc'.inst tc'.ix v hvq (by omega) $$ Hins
                  with ⟨%iss6, %rows6, %row6, #Hiss6, #Hrows6, %Hrow6, Hrow6, %Hp6, Hx6, Hclose6⟩
                rw [hwv', hlv2]
                dsimp only [slotT, ownInstT, ownInstG]
                icases Hx6 with ⟨%y6, Hy6, %Hy6f, Hy6r⟩
                wp_auto
                rw [Hy6f.2.2.2.2.1, Hy6f.2.2.2.2.2]
                have hcmp' : ¬ sint.Z (W64 (t.n : Int)) < sint.Z (W64 (lv2 : Int)) := by
                  rw [show sint.Z (W64 (t.n : Int)) = t.n by word, show sint.Z (W64 (lv2 : Int)) = lv2 by word]
                  omega
                simp only [hcmp', decide_false]
                wp_auto
                ihave Hins := Hclose6 $$ %(some wv') %(some (t.n, lv2)) Hrow6 [Hy6 Hy6r]
                · dsimp only; iexists y6; iframe; ipureintro; exact Hy6f
                rw [← hwv', ← hlv2, upd_self _ _ _ rfl, upd_self _ _ _ rfl]
                iframe
                ipureintro; rfl
              · icases repInstsX_acc2 γ i r F σc'.inst tc'.ix ⟨toN qv, toN iv⟩ v hyv hxq
                  (by simp only; omega) hvq (by omega) $$ Hins with ⟨Hxy, Hxv, Hclose2⟩
                rw [hxw, hwv', hab, hlv2]
                dsimp only [slotT, ownInstT, ownInstG]
                icases Hxy with ⟨%y7, Hy7, %Hy7f, Hy7r⟩
                icases Hxv with ⟨%v7, Hv7, %Hv7f, Hv7r⟩
                wp_auto
                ihave Hins := Hclose2 $$ [Hy7 Hy7r] [Hv7 Hv7r]
                · iexists y7; iframe; ipureintro; exact Hy7f
                · iexists v7; iframe; ipureintro; exact Hv7f
                rw [Hy7f.2.2.2.2.1, Hv7f.2.2.2.2.2]
                wp_if_destruct
                · have hlt : a < lv2 := hcmp.mp Hif
                  rw [if_pos (by rw [hnumy, hlowv]; exact hlt)]
                  icases repInstsX_acc γ i r F σc'.inst tc'.ix ⟨toN qv, toN iv⟩ hxq (by simp only; omega)
                    $$ Hins with ⟨%iss8, %rows8, %row8, #Hiss8, #Hrows8, %Hrow8, Hrow8, %Hp8, Hx8, Hclose8⟩
                  rw [hxw, hab]
                  dsimp only [slotT, ownInstT, ownInstG]
                  icases Hx8 with ⟨%y8, Hy8, %Hy8f, Hy8r⟩
                  wp_auto
                  ihave Hins := Hclose8 $$ %(some w) %(some (a, bl)) Hrow8 [Hy8 Hy8r]
                  · dsimp only; iexists y8; iframe; ipureintro; exact Hy8f
                  rw [← hxw, ← hab, upd_self _ _ _ rfl, upd_self _ _ _ rfl]
                  icases repInstsX_acc γ i r F σc'.inst tc'.ix v hvq (by omega) $$ Hins
                    with ⟨%iss9, %rows9, %row9, #Hiss9, #Hrows9, %Hrow9, Hrow9, %Hp9, Hx9, Hclose9⟩
                  rw [hwv', hlv2]
                  dsimp only [slotT, ownInstT, ownInstG]
                  icases Hx9 with ⟨%y9, Hy9, %Hy9f, Hy9r⟩
                  rw [Hy8f.2.2.2.2.1]
                  wp_auto
                  ihave Hins := Hclose9 $$ %(some wv') %(some (t.n, a)) Hrow9 [Hy9 Hy9r]
                  · dsimp only; iexists _; iframe; ipureintro
                    exact ⟨Hy9f.1, Hy9f.2.1, Hy9f.2.2.1, Hy9f.2.2.2.1, Hy9f.2.2.2.2.1, rfl⟩
                  rw [← hwv', upd_self _ _ _ rfl]
                  have hmix : (tc'.setLow v (tc'.num ⟨toN qv, toN iv⟩)).ix = upd tc'.ix v (some (t.n, a)) := by
                    funext x; simp only [St.setLow, upd, hnumv, hnumy]
                  rw [hmix]
                  iframe
                  ipureintro; rfl
                · have hge : ¬ tc'.num ⟨toN qv, toN iv⟩ < tc'.low v := by
                    rw [hnumy, hlowv]; exact fun h => Hif (hcmp.mpr h)
                  rw [if_neg hge]
                  iframe
            wp_for_post
            iframe
            iexists iv + W32 1, σc',
              (if tc'.num ⟨toN qv, toN iv⟩ < tc'.low v then tc'.setLow v (tc'.num ⟨toN qv, toN iv⟩) else tc')
            have hS6 : (if tc'.num ⟨toN qv, toN iv⟩ < tc'.low v then tc'.setLow v (tc'.num ⟨toN qv, toN iv⟩)
                else tc').S = tc'.S := by split <;> rfl
            have hn6 : (if tc'.num ⟨toN qv, toN iv⟩ < tc'.low v then tc'.setLow v (tc'.num ⟨toN qv, toN iv⟩)
                else tc').n = tc'.n := by split <;> rfl
            rw [hS6, hn6]
            iframe
            isplitl [Hst5 Hs5 Hcap5]
            · iexists s5; iframe; ipureintro; exact Hc5
            ipureintro
            refine ⟨by rw [hiv1]; omega, Or.inl (by rw [hiv1]; simp only [zz] at *; omega), Hjeu, ?_⟩
            refine hLo.mono (fun z hz => ?_)
            rw [hiv1] at hz
            by_cases hz' : (z.q : Int) < zz qv ∨ ((z.q : Int) = zz qv ∧ (z.i : Int) < zz iv)
            · exact Or.inl hz'
            · right
              obtain ⟨q', i'⟩ := z
              simp only [InstId.mk.injEq, toN, zz] at *; omega
    · -- the row is done: `q++`
      wp_for_post
      iframe
      iexists qv + W32 1, σc', tc'
      iframe
      rw [Hjeu]
      iframe
      have hq1 : zz (qv + W32 1) = zz qv + 1 := by simp only [zz]; unfold nR at HifQ; word
      isplitl [Heutsl]
      · iexists eut; iframe Heutf Heutsl
      ipureintro
      refine ⟨by rw [hq1]; simp only [zz]; omega, by rw [hq1]; simp only [zz]; omega, ?_⟩
      refine ⟨Hjl.rel, Hjl.wf, Hjl.ib, Hjl.cnt, Hjl.ext, Hjl.n, Hjl.inv, Hjl.act, Hjl.ixv, Hjl.parv, Hjl.stk,
        fun y he hy => ?_⟩
      rw [hq1] at hy
      by_cases hyq : (y.q : Int) < zz qv
      · exact Hjl.done y he (Or.inl hyq)
      · apply Hjl.done y he (Or.inr ⟨by omega, ?_⟩)
        -- `y.i ≤ deps[q] = d < i`
        obtain ⟨wy, hwy, -, hle⟩ := he
        have hdy : wy.deps = wv.deps := by
          have := (Hjl.rel.trans (ExRel.refl _)).deps v; rw [hwy, hv] at this; simpa using this
        have hyq' : y.q = (sint.Z qv).toNat := by simp only [zz] at *; omega
        rw [hdy, hyq', List.getD_eq_getElem?_getD, hd, Option.getD_some] at hle
        simp only [zz] at *; omega
  · -- all rows done: every edge of `v` is handled
    have hqv : zz qv = nR := by simp only [zz]; omega
    have hdone : DoneAll (gr σc) tc v := fun y he => Hlp.done y he (by
      rw [hqv]; obtain ⟨-, -, h, -⟩ := he; exact_mod_cast h)
    have hvS : v ∈ tc.S := Hlp.inv.actS v (by rw [Hlp.act]; simp)
    obtain ⟨-, -, -, hvex, wv', hwv', hwvc, -⟩ := Hlp.inv.onS v hvS
    obtain ⟨lv, hlv⟩ := Hlp.ixv
    have hlvle : lv ≤ t.n := by
      have := (Hlp.inv.lowW v hvS).1; simp [St.low, St.num, hlv] at this; exact this
    have htn : t.n < 2 ^ 40 := by have := visCount_bound Hlp.cnt; have := Hlp.n; unfold nR MAX_INSTANCE at *; omega
    icases repInstsX_acc γ i r F σc.inst tc.ix v hvq (by omega) $$ Hins with
      ⟨%iss1, %rows1, %row1, #Hiss1, #Hrows1, %Hrow1, Hrow, %Hp1, Hx, Hclose⟩
    rw [hwv', hlv]
    dsimp only [slotT, ownInstT, ownInstG]
    icases Hx with ⟨%y1, Hy, %Hyf1, Hyrest1⟩
    wp_auto
    obtain ⟨hy1, hy2, hy3, hy4, hyI, hyL⟩ := Hyf1
    rw [hyI, hyL]
    have heqW : (W64 (lv : Int) = W64 (t.n : Int)) ↔ lv = t.n := by
      constructor
      · intro h; have := congrArg sint.Z h
        rw [show sint.Z (W64 (lv : Int)) = lv by word, show sint.Z (W64 (t.n : Int)) = t.n by word] at this
        omega
      · intro h; rw [h]
    wp_if_destruct
    · -- `v.Lowlink == v.Index`: the component `stack[l:]` is popped and executed
      -- TODO: `pop_ready` gives `sccReady σc (v :: T)` (`S = t.S ++ v :: T`, `Hlp.ext.stk`);
      -- `ep_execSCC`; `list := stack[l:]`; `sort.Sort` with an `isSorter` for `nodeArray`
      -- (`own l` := the slice and the instances' `Seq`/`id`, `R` := `keyLt`) and
      -- `sort_eq_sccSort`; per instance and per command `ep_execCmd` (`Execute`,
      -- `ReplyProposeTS` with the `fired` witness, `ownLbF` flags), `w.Status = EXECUTED` with
      -- `ep_instDone`; `stack = stack[0:l]` (`slice_trunc`); `pop_inv`; return true (popped).
      have hlvn : lv = t.n := heqW.mp Hif
      ihave Hins := Hclose $$ %(some wv') %(some (t.n, lv)) Hrow [Hy Hyrest1]
      · dsimp only; iexists _; iframe Hy Hyrest1; ipureintro
        exact ⟨hy1, hy2, hy3, hy4, hyI, hyL⟩
      rw [upd_self _ _ _ hwv', upd_self _ _ _ hlv]
      obtain ⟨T, hST⟩ := Hlp.stk
      have hlow : tc.low v = tc.num v := by simp [St.low, St.num, hlv, hlvn]
      have hready := pop_sccReady Hlp.inv Hlp.act hST hlow hdone
      icases Hstk with ⟨%s2, Hst, Hs, Hcap, %Hcap2⟩
      ihave %Hs2l := ownSlice_len _ _ _ $$ Hs
      ihave %Hcw2 := ownSliceCap_wf (V := Loc) _ _ $$ Hcap
      have hS2len : (tc.S.length : Int) = sint.Z s2.len := by
        rw [List.length_map] at Hs2l; rw [Hs2l.1]; exact Int.toNat_of_nonneg Hs2l.2
      have hTS : tc.S.length = t.S.length + (v :: T).length := by rw [hST, List.length_append]
      have hbnd : 0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s2.len ∧ sint.Z s2.len ≤ sint.Z s2.cap := by
        refine ⟨Hsl.2, ?_, Hcw2.2⟩; rw [← hsl, ← hS2len, hTS]; simp; omega
      -- the component's ghost step: `execSCC`
      wp_auto_lc 1
      iapply fupd_wp
      imod (ep_execSCC γ ⊤ i σc (v :: T) (by simp) hi hready) $$ Hinv Hfrag Hpend Hcur Hlc1
        with ⟨Hfrag, Hpend, Hcur⟩
      imodintro
      simp only [hbnd, _root_.and_self, ↓reduceIte]
      icases (ownSlice_split_all s.len s2 _ _ ⟨hbnd.1, hbnd.2.1⟩).1 $$ Hs with ⟨Hs0, Hs1⟩
      have hsn : sint.nat s.len = t.S.length := Hsl.1.symm
      have htk : (tc.S.map (ptrOf F)).take (sint.nat s.len) = t.S.map (ptrOf F) := by
        rw [hsn, hST, List.map_append, List.take_left' (by simp)]
      have hdr : (tc.S.map (ptrOf F)).drop (sint.nat s.len) = (v :: T).map (ptrOf F) := by
        rw [hsn, hST, List.map_append, List.drop_left' (by simp)]
      rw [htk, hdr]
      wp_auto
      -- `sort.Sort(nodeArray(list))`
      have hCS : ∀ x ∈ v :: T, ∃ w, σc.inst x = some w := fun x hx => by
        have hxS : x ∈ tc.S := by rw [hST]; exact List.mem_append_right _ hx
        obtain ⟨-, -, -, -, w, hw, -⟩ := Hlp.inv.onS x hxS; exact ⟨w, hw⟩
      ihave #Hsrt := nodeArray_isSorter γ i r F σc tc.ix (slice.slice s2 Loc s.len s2.len) (v :: T)
        hCS Hlp.wf $$ Hpk
      ihave Hown : naOwn γ i r F σc tc.ix (slice.slice s2 Loc s.len s2.len) (v :: T) (v :: T)
        $$ [Hs1 Hins]
      · unfold naOwn; iframe Hs1 Hins; ipureintro; exact List.Perm.refl _
      have hlen62 : (v :: T).length ≤ 2 ^ 62 := by
        have := visCount_bound Hlp.cnt; have := stack_le_n Hlp.inv Hlp.cnt
        rw [hTS] at this; unfold nR MAX_INSTANCE at *; omega
      wp_apply sort.wp_Sort (GoInterfaceOk.mk epaxos.nodeArray.ty #(slice.slice s2 Loc s.len s2.len))
        (naOwn γ i r F σc tc.ix (slice.slice s2 Loc s.len s2.len) (v :: T)) (keyLt σc) (keyLt_swo σc)
        (v :: T) $$ [$Hsrt $Hown] as %ys ⟨Hown, %Hperm, %Hsorted⟩
      · ipureintro; exact hlen62
      have hys : ys = sccSort σc (v :: T) := sort_eq_sccSort σc (v :: T) ys Hperm.symm Hsorted
      rw [← hys]
      unfold naOwn
      icases Hown with ⟨-, Hls, Hins⟩
      have hysnd : ys.Nodup := Hperm.nodup_iff.mp hready.2.1
      have hysC : ∀ x ∈ ys, x ∈ v :: T := fun x hx => Hperm.symm.mem_iff.mp hx
      ihave %Hlsl := ownSlice_len _ _ _ $$ Hls
      simp only [List.length_map] at Hlsl
      -- the instances, in order
      ihave HR : (∃ (k : w64) (σk : RState),
          "Hi" ∷ i_ptr ↦ k ∗ "Hw" ∷ (∃ pw : Loc, w_ptr ↦ pw) ∗
          "Hins" ∷ repInstsX γ i r F σk.inst tc.ix ∗ "Hstore" ∷ repStore r σk.store ∗
          "Hfrag" ∷ repFrag γ i σk ∗ "Hcur" ∷ curFrag γ i (ys.drop (sint.nat k)) 0 ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ ys.length ∧ PopOk σc (ys.take (sint.nat k)) σk⌝ :
          IProp GF) $$ [«i» w Hins Hstore Hfrag Hcur]
      · iexists W64 0, σc
        iframe «i» Hins Hstore Hfrag
        isplitl [w]
        · iexists _; iexact w
        rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, List.take_zero]
        iframe Hcur
        ipureintro; exact ⟨by decide, by simp, PopOk.init Hlp.wf Hlp.ib⟩
      wp_for HR
      wp_if_destruct
      · -- instance `ys[k]`
        obtain ⟨hk0, hkl, hpop⟩ := Hk
        have hkn : sint.nat k < ys.length := by
          have h1 := Hlsl.1; simp only [slice.slice] at h1 Hif
          have : sint.Z (s2.len - s.len) = sint.Z s2.len - sint.Z s.len := by word
          rw [this] at Hif
          have : sint.nat (s2.len - s.len) = sint.nat s2.len - sint.nat s.len := by word
          rw [this] at h1
          word
        obtain ⟨x, hx⟩ : ∃ x, ys[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem hkn⟩
        have hxC : x ∈ v :: T := hysC x (List.mem_of_getElem? hx)
        have hdrop : ys.drop (sint.nat k) = x :: ys.drop (sint.nat k + 1) := by
          rw [List.drop_eq_getElem_cons hkn, (List.getElem?_eq_some_iff.mp hx).2]
        have hxD : x ∉ ys.take (sint.nat k) := by
          have h := hysnd; rw [← List.take_append_drop (sint.nat k) ys, hdrop] at h
          exact fun hm => (List.nodup_append.mp h).2.2 x hm x List.mem_cons_self rfl
        have htake : ys.take (sint.nat k + 1) = ys.take (sint.nat k) ++ [x] := by
          rw [List.take_succ, hx]; rfl
        have hxS : x ∈ tc.S := by rw [hST]; exact List.mem_append_right _ hxC
        obtain ⟨-, -, -, -, w, hw, hwc, hwcmds⟩ := Hlp.inv.onS x hxS
        obtain ⟨cs, hcs⟩ : ∃ cs, w.cmds = some cs := Option.ne_none_iff_exists'.mp hwcmds
        have hwk : σk.inst x = some w := by rw [hpop.inst_of hxD]; exact hw
        obtain ⟨hxq, hxi⟩ := hpop.wf.ids x w hwk
        have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z (s2.len - s.len) := ⟨hk0, Hif⟩
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index _ _ _ _ (ptrOf F x) hk0 $$ [$Hls] as Hls
        · ipureintro; rw [List.getElem?_map]; show Option.map _ ys[sint.nat k]? = _; rw [hx]; rfl
        icases Hw with ⟨%pw, Hw⟩
        wp_auto_lc 1
        irename Hlc1 => HlcI
        icases repInstsX_acc γ i r F σk.inst tc.ix x hxq (by omega) $$ Hins with
          ⟨%issx, %rowsx, %rowx, #Hissx, #Hrowsx, %Hrowx, Hrowx, %Hpx, Hx, Hclosex⟩
        rw [hwk]
        dsimp only [slotT, ownInstT, ownInstG]
        icases Hx with ⟨%yx, Hyx, %Hyxf, #Hidxx, Hcmdsx, Hdepsx, Hlbx⟩
        rw [hcs]; unfold cmdsRep
        icases Hcmdsx with ⟨%Hcnn, #Hcmdsx⟩
        icases ownCmds_open _ _ _ $$ Hcmdsx with ⟨%vs, #Hvs, %Hvsl, #Hvsc⟩
        ihave %Hvsl2 := ownSlice_len _ _ _ $$ Hvs
        ihave Hlbx : lbRes γ i (fun _ => decide (w.status = stEXECUTED)) yx.lb' w.lb $$ [Hlbx]
        · unfold lbRes; iexact Hlbx
        ihave Hlbx := lbRes_mono (GF := GF) γ i (fun _ => decide (w.status = stEXECUTED)) (fun _ => false)
          yx.lb' w.lb (by intro n hn; rw [hwc] at hn; revert hn; decide) $$ Hlbx
        rw [hdrop]
        -- the commands of `x`
        ihave HC : (∃ (j : w64) (σj : RState),
            "Hix" ∷ idx_ptr ↦ j ∗
            "Hlb" ∷ lbRes γ i (fun n => decide (n < sint.nat j)) yx.lb' w.lb ∗
            "Hstore" ∷ repStore r σj.store ∗ "Hfrag" ∷ repFrag γ i σj ∗
            "Hcur" ∷ curFrag γ i (x :: ys.drop (sint.nat k + 1)) (sint.nat j) ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ cs.length ∧ PopOk σc (ys.take (sint.nat k)) σj⌝ :
            IProp GF) $$ [idx Hlbx Hstore Hfrag Hcur]
        · iexists W64 0, σk
          iframe idx Hstore Hfrag
          rw [show sint.nat (W64 0) = 0 from rfl]
          iframe Hcur
          isplitl [Hlbx]
          · iapply lbRes_mono γ i (fun _ => false) _ _ _ (fun _ h => by cases h)
            iexact Hlbx
          ipureintro; exact ⟨by decide, by omega, hpop⟩
        wp_for HC
        obtain ⟨hj0, hjl, hpopj⟩ := Hj
        have hvl : (vs.length : Int) = sint.Z yx.Cmds'.len := by
          rw [Hvsl2.1]; exact Int.toNat_of_nonneg Hvsl2.2
        wp_if_destruct
        · -- command `j`
          have hjn : sint.nat j < cs.length := by rw [← Hvsl]; word
          -- `shouldRespond`
          wp_join (Q := fun vv => iprop(⌜vv = #((w.lb.bind (·.clientProposals)).isSome)⌝ ∗
              lbRes γ i (fun n => decide (n < sint.nat j)) yx.lb' w.lb ∗ w_ptr ↦ ptrOf F x ∗
              ptrOf F x ↦ yx)) with [Hlb Hw Hyx]
          · rcases hwl : w.lb with _ | lb
            · iframe; ipureintro; rfl
            · unfold lbRes; icases Hlb with ⟨%Hn, -⟩
              exact absurd Hif Hn
          · rcases hwl : w.lb with _ | lb
            · unfold lbRes; icases Hlb with %Hn; exact absurd Hn Hif
            unfold lbRes ownLbF
            icases Hlb with ⟨%Hnn, %yl, %gs, %prs, Hlbp, %Hylf, Hps, Hrest⟩
            wp_auto
            rcases hcp : lb.clientProposals with _ | ps
            · icases Hps with %Hcp
              rw [Hcp]
              isplitr
              · ipureintro; simp [hcp]
              iframe Hw Hyx
              isplitr
              · ipureintro; exact Hnn
              iexists yl, gs, prs; rw [hcp]; iframe Hlbp Hrest
              isplitr
              · ipureintro; exact Hylf
              ipureintro; exact Hcp
            · icases Hps with ⟨%Hcp, #Hgs, Hbig⟩
              isplitr
              · ipureintro; simp [hcp, Hcp.1]
              iframe Hw Hyx
              isplitr
              · ipureintro; exact Hnn
              iexists yl, gs, prs; rw [hcp]; iframe Hlbp Hrest
              isplitr
              · ipureintro; exact Hylf
              isplitr
              · ipureintro; exact Hcp
              isplitr
              · iexact Hgs
              iexact Hbig
          iintro ⟨%Hsr, Hlb, Hw, Hyx⟩
          subst Hsr
          wp_auto_lc 2
          have hwj : σj.inst x = some w := by rw [hpopj.inst_of hxD]; exact hw
          have hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z yx.Cmds'.len := ⟨hj0, Hif⟩
          obtain ⟨cv, hcv⟩ : ∃ cv, vs[sint.nat j]? = some cv :=
            ⟨_, List.getElem?_eq_getElem (by rw [Hvsl]; exact hjn)⟩
          ihave ⟨%wc, %hwc', #Hok⟩ := BigSepL.bigSepL_lookup hcv $$ Hvsc
          ihave ⟨#Hc, -⟩ := ownSlice_elem_acc (sint.Z j) cv _ _ vs hj0 hcv $$ Hvs
          have hcj : (w.cmds.getD []).getD (sint.nat j) default = wc := by
            rw [hcs, Option.getD_some, List.getD_eq_getElem?_getD, hwc', Option.getD_some]
          -- the command's ghost step (`execCmd`)
          iapply fupd_wp
          imod (ep_execCmd γ ⊤ i σj x (ys.drop (sint.nat k + 1)) w (sint.nat j) CoPset.subseteq_top
            CoPset.subseteq_top CoPset.subseteq_top hi hwj (by rw [hcs]; exact hjn)) $$ Hinv Hfrag Hcur
            [Hlc1 Hlc2] with ⟨Hfrag, Hcur, Houts⟩
          · iapply (lc_split (n := 1) (m := 1)).2; iframe
          imodintro
          ihave #Hc2 := Hc
          iStructNamed Hc2
          unfold cmdOk
          icases Hok with ⟨%Hokp, #Hokv⟩
          simp only [hbj, _root_.and_self, ↓reduceIte]
          wp_auto
          have hmono : ∀ n, decide (n < sint.nat j) = true → decide (n < sint.nat j + 1) = true := by
            intro n h; simp only [decide_eq_true_eq] at h ⊢; omega
          wp_join iprop(repStore r (execCmdAt σj w (sint.nat j)).1.store ∗
              lbRes γ i (fun n => decide (n < sint.nat j + 1)) yx.lb' w.lb ∗ w_ptr ↦ ptrOf F x ∗
              ptrOf F x ↦ yx ∗ e_ptr ↦ e ∗ idx_ptr ↦ j) with [Hstore Hlb Hw Hyx Houts e Hix shouldRespond]
              as ⟨Hstore, Hlb, Hw, Hyx, e, Hix⟩
          · -- `NONE`: nothing
            have hn : ((w.cmds.getD []).getD (sint.nat j) default).op = opNONE := by
              rw [hcj, ← Hokp.1]; exact Hif
            rw [execCmdAt_none _ _ _ hn]
            ihave Hlb := lbRes_mono (GF := GF) γ i _ _ yx.lb' w.lb hmono $$ Hlb
            iframe
          · -- not `NONE`
            have hnn : ((w.cmds.getD []).getD (sint.nat j) default).op ≠ opNONE := by
              rw [hcj, ← Hokp.1]; exact Hif
            have hcok : OpCmdOk wc := hpopj.wf.cmdsOk x w hwj (Or.inl hwc) wc
              (by rw [hcs, Option.getD_some]; exact List.mem_of_getElem? hwc')
              (by rw [← Hokp.1]; exact Hif)
            have hscan : wc.op = opSCAN → 8 ≤ wc.val.length := opCmdOk_scan_len hcok
            unfold repStore
            icases Hstore with ⟨%rr', %st, %S, #Hrr', #Hst', HS, %HSeq⟩
            icombine Hrr Hrr' gives %Hre
            subst Hre
            icombine HSt Hst' gives %Hse
            subst Hse
            rcases hsr : w.lb.bind (·.clientProposals) with _ | ps
            · -- no reply: a `PUT` is executed
              try simp only [Option.isSome_none]
              wp_auto
              ihave Hlb := lbRes_mono (GF := GF) γ i _ _ yx.lb' w.lb hmono $$ Hlb
              simp only [hbj, _root_.and_self, ↓reduceIte]
              wp_auto
              wp_if_destruct
              · have hput : ((w.cmds.getD []).getD (sint.nat j) default).op = opPUT := by
                  rw [hcj, ← Hokp.1]; exact Hif
                rw [execCmdAt_noreply_put σj w _ hnn hsr hput, hcj]
                simp only [hbj, _root_.and_self, ↓reduceIte]
                wp_apply (hEx (sliceIndexRef state.Command (sint.Z j) yx.Cmds') DFrac.discard cv wc p.st S
                  hscan (fun _ => by rw [(execCmd_agree S σj.store wc HSeq).2]; exact Nat.lt_trans (execCmd_res_len _ _ hpopj.wf.store hcok) (by omega))) $$ [HS] as %ret ⟨-, HS, -⟩
                · unfold cmdOk; iframe Hc HS Hokv; ipureintro; exact Hokp
                obtain ⟨hag1, -⟩ := execCmd_agree S σj.store wc HSeq
                iframe Hlb Hw Hyx e Hix
                isplitr
                · ipureintro; rfl
                iexists rr, p.st, (_root_.Perennial.github_com.imdea_software.swiftpaxos_epaxos.execCmd S wc).1
                iframe HS Hrr Hst'; ipureintro; exact hag1
              · have hnput : ((w.cmds.getD []).getD (sint.nat j) default).op ≠ opPUT := by
                  rw [hcj, ← Hokp.1]; exact Hif
                rw [execCmdAt_noreply_other σj w _ hnn hsr hnput]
                iframe Hlb Hw Hyx e Hix
                iexists rr, p.st, S
                iframe HS Hrr Hst'; ipureintro; exact HSeq
            · -- `shouldRespond`: `Execute`, `ReplyProposeTS`
              try simp only [Option.isSome_some]
              wp_auto
              simp only [hbj, _root_.and_self, ↓reduceIte]
              wp_apply (hEx (sliceIndexRef state.Command (sint.Z j) yx.Cmds') DFrac.discard cv wc p.st S
                hscan (fun _ => by rw [(execCmd_agree S σj.store wc HSeq).2]; exact Nat.lt_trans (execCmd_res_len _ _ hpopj.wf.store hcok) (by omega))) $$ [HS] as %ret ⟨-, HS, #Hret⟩
              · unfold cmdOk; iframe Hc HS Hokv; ipureintro; exact Hokp
              obtain ⟨lb, hwl, hcp⟩ : ∃ lb, w.lb = some lb ∧ lb.clientProposals = some ps := by
                rcases h : w.lb with _ | lb
                · rw [h] at hsr; cases hsr
                · rw [h] at hsr; exact ⟨lb, rfl, hsr⟩
              have hjps : sint.nat j < ps.length := hpopj.wf.props x w lb ps hwj (Or.inl hwc) hwl hcp
                (sint.nat j) wc (by rw [hcs, Option.getD_some]; exact hwc') (by rw [← Hokp.1]; exact Hif)
              rw [hwl]
              unfold lbRes ownLbF
              icases Hlb with ⟨%Hlnn, %yl, %gs, %prs, Hlbp, %Hylf, Hps, Hrest⟩
              rw [hcp]
              icases Hps with ⟨%Hcp, #Hgs, Hbig⟩
              obtain ⟨g, hg⟩ : ∃ g, gs[sint.nat j]? = some g :=
                ⟨_, List.getElem?_eq_getElem (by rw [Hcp.2]; exact hjps)⟩
              icases BigSepL.bigSepL_lookup_acc_impl hg $$ Hbig with ⟨Hg, Hbig⟩
              icases propHeld_open _ _ _ _ _ $$ Hg with ⟨%pp, %wr, %mu, %proxy, %addr, %cid, %inp, %cv', #Hgp, #Hpp, #Hcok, #Hconn,
                %Hpc, #Hcw, Htok⟩
              simp only [Nat.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte]
              ihave %Hgsl := ownSlice_len _ _ _ $$ Hgs
              have hgb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z yl.clientProposals'.len := by
                refine ⟨hj0, ?_⟩; have h1 := Hgsl.1; have h2 := Hgsl.2; rw [Hcp.2] at h1; word
              have hgl : gs[(sint.Z j).toNat]? = some g := hg
              ihave #Hgp' := Hgp
              iStructNamed Hgp'
              ihave #Hpp' := Hpp
              iStructNamed Hpp'
              repeat' (first
                | (simp only [hgb, _root_.and_self, ↓reduceIte]; first
                  | (wp_apply wp_load_slice_index yl.clientProposals' _ _ _ g hj0 $$ [$Hgs] as -;
                      (ipureintro; exact hgl))
                  | wp_auto)
                | wp_auto)
              rw [execCmdAt_reply σj w (sint.nat j) ps hnn hsr, hcj]
              dsimp only
              icases Houts with ⟨Hout, -⟩
              dsimp only [outOk]
              icases Hout with ⟨%o, #Hf, %Ho⟩
              obtain ⟨hag1, hag2⟩ := execCmd_agree S σj.store wc HSeq
              rw [hag2]
              wp_apply (wp_ep_ReplyProposeTS hRP γ r rr i L p Rext «$a0_ptr» wr mu
                (ps.getD (sint.nat j) default).cid o (model.execCmd σj.store wc).2 ret (W64 0)
                (DFrac.own 1) DFrac.discard) $$ [«$a0» Htok]
              · isplitr
                · iexact Hrr
                isplitr
                · ipureintro; exact ⟨Ho, execCmd_res_len _ _ hpopj.wf.store hcok⟩
                isplitr
                · iexact Hfw
                isplitl [«$a0»]
                · rw [show okTRUE = W8 1 from rfl]; iexact «$a0»
                isplitr
                · iexact Hret
                isplitr
                · iexact Hcw
                isplitl [Htok]
                · iexact Htok
                iexact Hf
              iintro -
              wp_auto
              have hmono' : ∀ k, k ≠ sint.nat j → decide (k < sint.nat j) = decide (k < sint.nat j + 1) := by
                intro k hk; simp only [decide_eq_decide]; omega
              ihave Hbig := Hbig $$ %(fun k g => propHeld γ i (decide (k < sint.nat j + 1)) g
                (ps.getD k default)) [] [Hgp Hpp Hcok Hconn Hcw]
              · iintro !> %k %y %hk %hkj Hk
                ihave Hk := propHeld_eq (GF := GF) γ i _ _ _ _ (hmono' k hkj) $$ Hk
                iexact Hk
              · unfold propHeld
                iexists pp, wr, mu, proxy, addr, cid, inp, cv'
                iframe Hgp Hpp Hcok Hconn Hcw
                isplitr
                · ipureintro; exact Hpc
                simp only [Nat.lt_succ_self, _root_.decide_true, ↓reduceIte]
                ipureintro; trivial
              iframe Hw Hyx e Hix
              isplitr
              · ipureintro; rfl
              isplitl [HS]
              · iexists rr, p.st, (_root_.Perennial.github_com.imdea_software.swiftpaxos_epaxos.execCmd S wc).1
                iframe HS Hrr Hst'; ipureintro; exact hag1
              isplitr
              · ipureintro; exact Hlnn
              iexists yl, gs, prs
              rw [hcp]
              iframe Hlbp Hrest
              isplitr
              · ipureintro; exact Hylf
              isplitr
              · ipureintro; exact Hcp
              isplitr
              · iexact Hgs
              iexact Hbig
          wp_for_post
          have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
            have h1 : sint.nat j < sint.nat yx.Cmds'.len := by rw [← Hvsl2.1, Hvsl]; exact hjn
            word
          iframe
          iexists j + W64 1, (execCmdAt σj w (sint.nat j)).1
          rw [hj1]
          iframe
          ipureintro
          exact ⟨by word, by omega, popOk_cmd hpopj hwj (Or.inl hwc) _⟩
        · -- `w.Status = EXECUTED`, the instance's end
          have hjc : sint.nat j = cs.length := by rw [← Hvsl]; word
          have hwj : σj.inst x = some w := by rw [hpopj.inst_of hxD]; exact hw
          iapply fupd_wp
          imod (ep_instDone γ ⊤ i σj x (ys.drop (sint.nat k + 1)) w (by simp) hi hwj) $$ Hinv Hfrag
            [Hcur] HlcI with ⟨Hfrag, Hcur⟩
          · rw [hcs, Option.getD_some, ← hjc]; iexact Hcur
          imodintro
          unfold epaxos.EXECUTED
          wp_auto
          ihave Hlb := lbRes_mono (GF := GF) γ i _ (fun _ => decide True) yx.lb' w.lb (fun _ _ => by simp) $$ Hlb
          ihave Hins := Hclosex $$ %(some (exStat w)) %(tc.ix x) Hrowx [Hyx Hdepsx Hlb]
          · dsimp only [slotT, ownInstT, ownInstG, exStat]
            iexists _; iframe Hyx Hidxx Hdepsx
            isplitr
            · ipureintro
              exact ⟨Hyxf.1, Hyxf.2.1, rfl, Hyxf.2.2.2.1, ixOk_exec _ _ _ Hyxf.2.2.2.2⟩
            isplitr
            · simp only [exStat, hcs]; iframe Hcmdsx; ipureintro; exact Hcnn
            unfold lbRes; simp only [exStat]; iexact Hlb
          have hjk : σj.inst = σk.inst := funext fun z => by rw [hpopj.inst z, hpop.inst z]
          rw [← hjk, ← execDone_inst hwj, upd_self _ _ _ rfl]
          wp_for_post
          have hysl : ys.length ≤ 2 ^ 62 := by rw [← Hperm.length_eq]; exact hlen62
          have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
          iframe
          iexists k + W64 1, execDone σj x
          rw [execDone_store, hk1]
          iframe Hi Hins Hstore Hfrag Hcur
          isplitl [Hw]
          · iexists _; iexact Hw
          ipureintro
          refine ⟨by word, by omega, ?_⟩
          rw [htake]; exact popOk_done hpopj hxD hw (Or.inl hwc)
      · -- the component is executed: `e.stack = e.stack[0:l]`, return true
        obtain ⟨hk0, hkl, hpop⟩ := Hk
        have hkend : sint.nat k = ys.length := by
          have h1 := Hlsl.1; have h2 := Hlsl.2
          simp only [slice.slice] at h1 h2 Hif
          have : sint.Z (s2.len - s.len) = sint.Z s2.len - sint.Z s.len := by word
          rw [this] at Hif h2
          have : sint.nat (s2.len - s.len) = sint.nat s2.len - sint.nat s.len := by word
          rw [this] at h1
          word
        rw [hkend, List.take_length] at hpop
        rw [hkend, List.drop_length]
        have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s2.cap :=
          ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; exact hbnd.1, by omega⟩
        simp only [hb0, _root_.and_self, ↓reduceIte]
        ihave Hcap := ownSlice_slice_absorb_capacity s2 _ (W64 0) s.len
          ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; exact hbnd.1, hbnd.2.1⟩ $$ [Hls Hcap]
        · iframe
        wp_auto
        obtain ⟨hE', hex', hrd'⟩ := popOk_final hpop Hperm.symm hCS
        have hTI : TInv (gr σk) { tc with S := t.S, A := t.A } :=
          pop_inv Hlp.inv Hlp.act hST hlow hdone (gr σk) hE' hex' hrd'
        have hexv : σk.executed v := (hex' v).mpr (Or.inr List.mem_cons_self)
        iapply HΦ
        iexists σk, { tc with S := t.S, A := t.A }
        iframe Hins Hstore Hidx Hfrag Hpend Hcur
        isplitl [Heut Hst Hs0 Hcap]
        · isplitl [Heut]
          · rw [hpop.rel.fields.2.2.2.1]; iexact Heut
          iexists _; iframe Hst Hs0 Hcap; ipureintro
          simp only [slice.slice]; rw [show s2.cap - W64 0 = s2.cap by word]; exact Hcap2
        ipureintro
        refine ⟨Hlp.rel.trans hpop.rel, hpop.wf, hpop.ib, Hlp.cnt, ?_, by have := Hlp.n; show t.n ≤ tc.n; omega, ?_⟩
        · refine ⟨⟨[], by simp⟩, fun x hx => Hlp.ext.ix x hx, fun x hx => hpop.rel.executed (Hlp.ext.ex x hx),
            by rw [hpop.rel.gE, Hlp.ext.E], fun x hx => Hlp.ext.par x hx⟩
        · show TInv (gr σk) _ ∧ scTrue σk _ t.A v t.n
          exact ⟨hTI, lv, hlv, Or.inl ⟨hexv, hlvn, rfl⟩⟩
    · -- `v` stays on the stack, finished
      have hlt : lv < t.n := by
        rcases Nat.lt_or_eq_of_le hlvle with h | h
        · exact h
        · exact absurd (by rw [h]) Hif
      ihave Hins := Hclose $$ %(some wv') %(some (t.n, lv)) Hrow [Hy Hyrest1]
      · dsimp only; iexists _; iframe Hy Hyrest1; ipureintro
        exact ⟨hy1, hy2, hy3, hy4, hyI, hyL⟩
      rw [upd_self _ _ _ hwv', upd_self _ _ _ hlv]
      iapply HΦ
      iexists σc, tc
      iframe
      ipureintro
      refine ⟨Hlp.rel, Hlp.wf, Hlp.ib, Hlp.cnt, Hlp.ext, by have := Hlp.n; omega, ?_⟩
      show TInv (gr σc) tc ∧ scTrue σc tc t.A v t.n
      exact ⟨Hlp.inv, lv, hlv, Or.inr ⟨hvS, hlt, Hlp.act, hdone, Hlp.parv⟩⟩

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
