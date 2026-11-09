/-
Lean-first (no Rocq counterpart). Trace-check's layer D (2026-11-09): the proof of
`ConvertEvents`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.ConvertEvents

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
variable [etcdraft_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem ConvertEvents.wp_proof : ConvertEvents.spec (GF := GF) (hG := hG) := by
  intro sl L
  wp_start as ⟨#Hrep, %Hasc⟩
  iunfold traceEventsRep at Hrep
  icases Hrep with ⟨%gs, #Hgs, #Hgl⟩
  ihave %Hgl := ownSlice_len $$ Hgs
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hgl
  iapply wp_fupd
  wp_auto
  wp_apply wp_slice_make2 (V := Etcdraft.G.Event) sl.len $$ [] as %out ⟨Hout, -⟩
  · ipureintro; exact Hgl.2
  try wp_auto
  ihave IH : iprop(∃ (n kv : w64) (dn : List Etcdraft.G.Event),
      "i" ∷ i_ptr ↦ n ∗ "k" ∷ k_ptr ↦ kv ∗
      "Hout" ∷ out ↦* (dn ++ List.replicate (sint.nat sl.len - sint.nat n) (zero_val Etcdraft.G.Event)) ∗
      "#Hdone" ∷ ([∗list] g;e ∈ dn;(L.take (sint.nat n)).map TraceSim.evConv, Etcdraft.eventRO g e) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧ dn.length = sint.nat n⌝) $$ [i k Hout]
  · iexists (W64 0), (zero_val w64), []
    rw [show sint.nat (W64 0) = 0 by rfl]
    simp only [List.nil_append, Nat.sub_zero, List.take_zero, List.map_nil]
    iframe
    isplitl []
    · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).mpr; iempintro
    ipureintro
    refine ⟨by word, by word, rfl⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnd⟩ := Hn
  wp_if_destruct
  · have hlt : sint.Z n < sint.Z sl.len :=  Hif
    have Hlt : sint.nat n < gs.length := by rw [Hgl.1]; word
    obtain ⟨g, Hg⟩ : ∃ g, gs[sint.nat n]? = some g := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨e, He⟩ : ∃ e, L[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave #Hge := BigSepL2.bigSepL2_lookup (PROP := IProp GF) Hg He $$ Hgl
    have Hgn : gs[(sint.Z n).toNat]? = some g := Hg
    icases ownSlice_elem_acc (sint.Z n) g sl DFrac.discard gs hn0 Hgn $$ Hgs with ⟨#Hel, -⟩
    iunfold tracingEventVal at Hge
    icases Hge with ⟨%ca, %cb, %Hf, #Hca, #Hcb, #Hmsg, -, #Hprops⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, hlt⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) gs DFrac.discard g hn0 $$ [Hgs] as -
    · isplitr
      · iexact Hgs
      ipureintro; exact Hg
    try wp_auto
    have Hoz : (dn ++ List.replicate (sint.nat sl.len - sint.nat n) (zero_val Etcdraft.G.Event))[(sint.Z n).toNat]? =
        some (zero_val Etcdraft.G.Event) := by
      rw [List.getElem?_append_right (by rw [hnd]; exact Nat.le_refl (sint.nat n)), List.getElem?_replicate]
      rw [ite_eq_left (by rw [hnd]; word)]
    ihave %HoL := ownSlice_len $$ Hout
    have hon : sint.Z n < sint.Z out.len := by
      have := HoL.1
      simp only [List.length_append, List.length_replicate, hnd] at this
      word
    icases ownSlice_elem_acc (sint.Z n) _ out (DFrac.own 1) _ hn0 Hoz $$ Hout with ⟨Hoel, Hoclose⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, hlt⟩))]
    wp_auto
    iStructNamed Hel
    iStructNamed State
    obtain ⟨Hfn, Hfi, Hft, Hfv, Hfc, Hfr, Hfl, Hfconf⟩ := Hf
    have Hc0 : g.Conf'.arr[(sint.Z (W64 0)).toNat]? = some ca := by rw [Hfconf]; rfl
    have Hc1 : g.Conf'.arr[(sint.Z (W64 1)).toNat]? = some cb := by rw [Hfconf]; rfl
    icases array_acc _ _ DFrac.discard _ g.Conf' ca (by word) Hc0 $$ Conf with ⟨#Hc0p, -⟩
    icases array_acc _ _ DFrac.discard _ g.Conf' cb (by word) Hc1 $$ Conf with ⟨#Hc1p, -⟩
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z out.len from ⟨hn0, hon⟩))]
    wp_auto
    ihave %Hmn := tracingMsgRep_null _ _ $$ Hmsg
    wp_join iprop(∃ v : Etcdraft.G.Event,
        "out" ∷ out_ptr ↦ out ∗ "k" ∷ k_ptr ↦ n ∗
        "Hoel" ∷ sliceIndexRef Etcdraft.G.Event (sint.Z n) out ↦ v ∗
        "%Hv" ∷ ⌜v.Name' = g.Name' ∧ v.NID' = g.NodeID' ∧ v.State'.Term' = g.State'.Term' ∧
          v.State'.Vote' = g.State'.Vote' ∧ v.State'.Commit' = g.State'.Commit' ∧ v.Role' = g.Role' ∧
          v.Log' = g.LogSize' ∧ v.Conf'.arr = [ca, cb] ∧ v.Prop' = null⌝ ∗
        "#Hvm" ∷ eventMsgRO v.Msg' (TraceSim.evConv e).msg)
      with [Hoel out k m] as ⟨%v, out, k, Hoel, %Hv, #Hvm⟩
    · have hnone : e.msg = none := Hmn.2 Hif
      iexists _
      iframe Hoel out k
      isplitr
      · ipureintro
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [show (TraceSim.evConv e).msg = none by simp [TraceSim.evConv, hnone]]
      unfold eventMsgRO
      ipureintro; rfl
    · obtain ⟨mm, hm⟩ : ∃ mm, e.msg = some mm :=
        Option.ne_none_iff_exists'.mp (fun h => Hif (Hmn.1 h))
      ihave #Hmsg' : tracingMsgRep g.Message' (some mm) $$ [Hmsg]
      · rw [← hm]; iexact Hmsg
      iunfold tracingMsgRep at Hmsg'
      icases Hmsg' with ⟨%gm, #Hgm, %Hgmf⟩
      iStructNamed Hgm
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z out.len from ⟨hn0, hon⟩))]
      ipersist «$r0»
      wp_auto
      have hea := Hasc e (List.mem_of_getElem? He)
      obtain ⟨ha1, ha2, ha3, ha4⟩ := hea.2.2.2.2.2.2.1 mm hm
      obtain ⟨hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11⟩ := Hgmf
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hoel out k
      isplitr
      · ipureintro
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      simp only [TraceSim.evConv, hm, Option.map_some]
      unfold eventMsgRO
      iexists _
      iframe «$r0»
      ipureintro
      unfold Etcdraft.eventMsgRel
      simp only [TraceSim.gInt]
      rw [hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11]
      exact ⟨strRel_gsStr _ ha1, rfl, strRel_gsStr _ ha2, strRel_gsStr _ ha3, rfl, rfl, rfl, rfl,
        strRel_gsStr _ ha4, rfl, rfl⟩
    have hea := Hasc e (List.mem_of_getElem? He)
    wp_join iprop(∃ v' : Etcdraft.G.Event,
        "out" ∷ out_ptr ↦ out ∗ "k" ∷ k_ptr ↦ n ∗
        "ev" ∷ ev_ptr ↦ sliceIndexRef TracingEvent (sint.Z n) sl ∗
        "Hoel" ∷ sliceIndexRef Etcdraft.G.Event (sint.Z n) out ↦ v' ∗
        "#Hev" ∷ Etcdraft.eventRO v' (TraceSim.evConv e)) at (if: _ then _ else _)
      with [Hoel out k ev] as ⟨%v', out, k, ev, Hoel, #Hev⟩
    · obtain ⟨hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9⟩ := Hv
      have hvf : v.Name' = e.name ∧ v.NID' = e.nid ∧ v.State'.Term' = e.term ∧ v.State'.Vote' = e.vote ∧
          v.State'.Commit' = e.commit ∧ v.Role' = e.role ∧ v.Log' = e.logSize ∧ v.Conf'.arr = [ca, cb] := by
        rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8]
        exact ⟨Hfn, Hfi, Hft, Hfv, Hfc, Hfr, Hfl, rfl⟩
      iunfold tracingPropsRep at Hprops
      icases Hprops with (⟨%Hpnil, %Hnone⟩ | ⟨%pm, %pc, #Hpm, %Hpf, #Hcc⟩)
      · rw [show g.Properties' = map.nil from Hpnil]
        wp_auto
        isplitr
        · ipureintro; rfl
        have hnp : (TraceSim.evConv e).prop = none := by
          simp [TraceSim.evConv, Hnone.1, Hnone.2.1, Hnone.2.2]
        iexists v
        iframe out k ev Hoel
        simp only [named]
        iapply eventRO_intro v e ca cb hea hvf $$ Hca Hcb Hvm
        rw [hnp]
        unfold Etcdraft.propsRO
        ipureintro; exact hv9
      · try wp_auto
        wp_apply (wp_map_len_lt (K := GoString) (V := GoInterface) g.Properties' pm DFrac.discard) $$ [Hpm]
          as ⟨-, %Hsz⟩
        · iexact Hpm
        obtain ⟨Hp1, Hp2, Hp3, Hp4, Hp5, Hp6, Hp7⟩ := Hpf
        wp_if_destruct
        · have hpm : pm = ∅ := GMap.map_size_empty_inv pm (by word)
          have hl : ∀ k, pm !! k = none := by intro k; rw [hpm]; rfl
          have hcc : e.propCC = none := by
            cases h : e.propCC with
            | none => rfl
            | some c => have := Hp1.1 (by simp [h]); rw [hl] at this; cases this
          have hmt : e.propMatch = none := by
            cases h : e.propMatch with
            | none => rfl
            | some w => have := (Hp3 w).1 h; rw [hl] at this; cases this
          have hnx : e.propNext = none := by
            cases h : e.propNext with
            | none => rfl
            | some w => have := (Hp5 w).1 h; rw [hl] at this; cases this
          have hnp : (TraceSim.evConv e).prop = none := by
            simp [TraceSim.evConv, hcc, hmt, hnx]
          isplitr
          · itrivial
          iexists v
          iframe out k ev Hoel
          simp only [named]
          iapply eventRO_intro v e ca cb hea hvf $$ Hca Hcb Hvm
          rw [hnp]
          unfold Etcdraft.propsRO
          ipureintro; exact hv9
        · have hsome : ¬ (e.propCC = none ∧ e.propMatch = none ∧ e.propNext = none) := by
            rintro ⟨hcc, hmt, hnx⟩
            obtain ⟨k0, x0, hk0⟩ := (GMap.map_size_ne_0_lookup pm).1 (fun h => Hif (by rw [h]; rfl))
            by_cases hk : k0 ∈ [go!"cc", go!"match", go!"next"]
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
              rcases hk with rfl | rfl | rfl
              · rw [Hp2 (by simp [hcc])] at hk0; cases hk0
              · rw [Hp4 hmt] at hk0; cases hk0
              · rw [Hp6 hnx] at hk0; cases hk0
            · rw [Hp7 k0 hk] at hk0; cases hk0
          have hnp : (TraceSim.evConv e).prop = some { cc := e.propCC.map TraceSim.ccConv } := by
            simp only [TraceSim.evConv]
            refine ite_eq_right (fun h => ?_)
            simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
            exact hsome ⟨h.1.1, h.1.2, h.2⟩
          obtain ⟨pp, hpp⟩ : ∃ pp, pp = «$r0_ptr» := ⟨_, rfl⟩
          rw [← hpp]
          wp_apply (wp_map_lookup1 (K := GoString) (V := GoInterface) go.string go.any g.Properties' pm
            go!"cc" DFrac.discard) $$ [Hpm] as -
          · iexact Hpm
          rcases (show e.propCC = none ∨ ∃ c, e.propCC = some c by
              cases e.propCC <;> simp) with hcc | ⟨c, hcc⟩
          · rw [Hp2 (by rw [hcc]; rfl)]
            wp_auto
            rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z out.len from ⟨hn0, hon⟩))]
            ipersist «$r0»
            wp_auto
            isplitr
            · ipureintro; rfl
            iexists _
            iframe out k ev Hoel
            simp only [named]
            iapply eventRO_intro { v with Prop' := pp } e ca cb hea hvf $$ Hca Hcb Hvm
            rw [hnp, hcc]
            unfold Etcdraft.propsRO
            iexists _
            iframe «$r0»
            simp only [Option.map_none]
            ipureintro; rfl
          · rw [Hp1.1 (by rw [hcc]; rfl)]
            ihave #Hcc' : tracingCCRep pc (some c) $$ [Hcc]
            · rw [← hcc]; iexact Hcc
            iunfold tracingCCRep at Hcc'
            icases Hcc' with ⟨%gcc, %chs, #Hpc, #Hchs, %Hchs, #Hnc⟩
            ihave %Hpcnn := typedPointsto_not_null _ _ _ $$ Hpc
            iStructNamed Hpc
            icases «$r0» with Hpp
            wp_auto
            rw [decide_eq_false Hpcnn]
            wp_auto
            obtain ⟨ep, hep⟩ : ∃ ep, ep = «$r0_ptr» := ⟨_, rfl⟩
            rw [← hep]
            icases «$r0» with Hep
            ihave %Hchl := ownSlice_len $$ Hchs
            have hea' := hea.2.2.2.2.2.2.2 c hcc
            wp_join iprop(∃ ge : Etcdraft.G.EventConfChange,
                "cc" ∷ cc_ptr ↦ pc ∗ "ecc" ∷ ecc_ptr ↦ ep ∗ "Hep" ∷ ep ↦ ge ∗
                "%Hgen" ∷ ⌜ge.NewConf' = null⌝ ∗
                "Hgch" ∷ |==> Etcdraft.optSliceRO (V := Etcdraft.G.EventChange) ge.Changes'
                  (TraceSim.ccConv c).changes Etcdraft.changeRel)
              at (if: _ then _ else _) with [cc ecc Hep] as ⟨%ge, cc, ecc, Hep, %Hgen, Hgch⟩
            · wp_if_destruct
              · have hch0 : chs = [] := by
                  rw [Hif] at Hchl
                  exact List.length_eq_zero_iff.mp (by rw [Hchl.1]; rfl)
                have hc0 : c.changes = [] := by rw [← Hchs, hch0]; rfl
                isplitr
                · itrivial
                iexists _
                iframe cc ecc Hep
                isplitr
                · ipureintro; rfl
                simp only [TraceSim.ccConv, hc0, List.isEmpty_nil, ite_true]
                unfold Etcdraft.optSliceRO
                imodintro
                ipureintro; rfl
              · have hchne : chs ≠ [] := by
                  intro h0
                  rw [h0] at Hchl
                  apply Hif
                  have := Hchl.1
                  simp only [List.length_nil] at this
                  word
                wp_apply wp_slice_make2 (V := Etcdraft.G.EventChange) gcc.Changes'.len $$ [] as %chg ⟨Hchg, -⟩
                · ipureintro; exact Hchl.2
                try wp_auto
                ihave IHc : iprop(∃ (j hv : w64) (cv : SingleConfChange) (Lc : List Etcdraft.G.EventChange),
                    "i" ∷ i_ptr ↦ j ∗ "h" ∷ h_ptr ↦ hv ∗ "c" ∷ c_ptr ↦ cv ∗ "Hchg" ∷ chg ↦* Lc ∗
                    "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z gcc.Changes'.len ∧ Lc.length = chs.length ∧
                      ∀ jj < sint.nat j, Lc[jj]? = (chs[jj]?).map changeOf⌝) $$ [i h c Hchg]
                · iexists _, _, _, _
                  iframe
                  ipureintro
                  refine ⟨by word, by word, by simp [Hchl.1], fun jj hjj => ?_⟩
                  rw [show sint.nat (W64 0) = 0 by rfl] at hjj; omega
                wp_for IHc
                obtain ⟨hj0, hj1, hjL, hjp⟩ := Hj
                wp_if_destruct
                · have Hlt : sint.nat j < chs.length := by rw [Hchl.1]; word
                  obtain ⟨y, Hy⟩ : ∃ y, chs[sint.nat j]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
                  rw [ite_eq_left_of_eq_true _ _
                    (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z gcc.Changes'.len from ⟨hj0, Hif⟩))]
                  wp_apply wp_load_slice_index _ (sint.Z j) chs DFrac.discard y hj0 $$ [Hchs] as -
                  · isplitr
                    · iexact Hchs
                    ipureintro; exact Hy
                  try wp_auto
                  ihave %HcL := ownSlice_len $$ Hchg
                  have hjc : sint.Z j < sint.Z chg.len := by
                    have : sint.nat j < Lc.length := by rw [hjL]; exact Hlt
                    rw [HcL.1] at this; word
                  rw [ite_eq_left_of_eq_true _ _
                    (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z chg.len from ⟨hj0, hjc⟩))]
                  wp_apply wp_store_slice_index chg (sint.Z j) Lc _ $$ [Hchg] as Hchg
                  · iframe Hchg; ipureintro
                    refine ⟨hj0, ?_⟩
                    have : sint.nat j < Lc.length := by rw [hjL]; exact Hlt
                    word
                  try wp_auto
                  wp_for_post
                  iframe
                  iexists _, _, _, _
                  iframe
                  ipureintro
                  refine ⟨by word, by word, by rw [List.length_set, hjL], ?_⟩
                  rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word]
                  intro jj hjj
                  rw [show (sint.Z j).toNat = sint.nat j from rfl, List.getElem?_set]
                  rcases Nat.lt_succ_iff_lt_or_eq.1 hjj with hjj | hjj
                  · rw [ite_eq_right (Nat.ne_of_gt hjj)]; exact hjp jj hjj
                  · subst hjj
                    have : sint.nat j < Lc.length := by rw [hjL]; exact Hlt
                    rw [ite_eq_left rfl, Hy]; simp [this, changeOf]
                · have hjx : sint.nat j = chs.length := by rw [Hchl.1]; word
                  have hLc : Lc = chs.map changeOf := by
                    apply List.ext_getElem?
                    intro jj
                    rw [List.getElem?_map]
                    by_cases hjj : jj < sint.nat j
                    · exact hjp jj hjj
                    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]; rfl
                  subst hLc
                  isplitr
                  · itrivial
                  iexists _
                  iframe cc ecc Hep
                  isplitr
                  · ipureintro; rfl
                  simp only [named]
                  ipersist changes
                  imod ownSlice_persist $$ Hchg with #Hchg
                  imodintro
                  have hne : c.changes.isEmpty = false := by
                    rw [← Hchs]; simp [hchne]
                  simp only [TraceSim.ccConv, hne, Bool.false_eq_true, ↓reduceIte]
                  unfold Etcdraft.optSliceRO
                  iexists chg, _
                  iframe changes Hchg
                  ipureintro
                  rw [← Hchs]
                  exact forall₂_changeRel chs (by rw [Hchs]; exact hea'.1)
            imod Hgch with #Hgch
            ihave %Hncl := ownSlice_len $$ Hnc
            wp_join iprop(∃ ge2 : Etcdraft.G.EventConfChange,
                "cc" ∷ cc_ptr ↦ pc ∗ "ecc" ∷ ecc_ptr ↦ ep ∗ "Hep" ∷ ep ↦ ge2 ∗
                "%Hge2" ∷ ⌜ge2.Changes' = ge.Changes'⌝ ∗
                "Hgnc" ∷ |==> Etcdraft.optSliceRO (V := GoString) ge2.NewConf'
                  (TraceSim.ccConv c).newconf (fun s t => Etcdraft.strRel s t))
              at (if: _ then _ else _) with [cc ecc Hep] as ⟨%ge2, cc, ecc, Hep, %Hge2, Hgnc⟩
            · wp_if_destruct
              · have hnc0 : c.newconf = [] := List.length_eq_zero_iff.mp (by rw [Hncl.1, Hif]; rfl)
                isplitr
                · itrivial
                iexists _
                iframe cc ecc Hep
                isplitr
                · ipureintro; rfl
                simp only [TraceSim.ccConv, hnc0, List.isEmpty_nil, ite_true]
                unfold Etcdraft.optSliceRO
                imodintro
                ipureintro; exact Hgen
              · have hncne : c.newconf.isEmpty = false := by
                  cases h : c.newconf with
                  | nil => exfalso; apply Hif; rw [h] at Hncl; have := Hncl.1; simp only [List.length_nil] at this; word
                  | cons _ _ => rfl
                ihave Hnil := ownSlice_nil (V := GoString) (GF := GF) (DFrac.own 1)
                ihave Hncap := ownSliceCap_nil (V := GoString) (GF := GF)
                wp_apply wp_slice_append slice.nil ([] : List GoString) gcc.NewConf' c.newconf DFrac.discard
                  $$ [$Hnil $Hncap $Hnc] as %nsl ⟨Hnsl, -, -⟩
                try wp_auto
                isplitr
                · itrivial
                iexists _
                iframe cc ecc Hep
                isplitr
                · ipureintro; rfl
                simp only [named]
                ipersist newconf
                imod ownSlice_persist $$ Hnsl with #Hnsl
                imodintro
                simp only [TraceSim.ccConv, hncne, Bool.false_eq_true, ↓reduceIte]
                unfold Etcdraft.optSliceRO
                iexists nsl, c.newconf
                rw [List.nil_append]
                iframe newconf Hnsl
                ipureintro
                exact forall₂_strRel_gsStr _ hea'.2
            imod Hgnc with #Hgnc
            ipersist Hep
            ipersist Hpp
            rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z out.len from ⟨hn0, hon⟩))]
            wp_auto
            isplitr
            · ipureintro; rfl
            iexists _
            iframe out k ev Hoel
            simp only [named]
            iapply eventRO_intro { v with Prop' := pp } e ca cb hea hvf $$ Hca Hcb Hvm
            rw [hnp, hcc]
            unfold Etcdraft.propsRO
            iexists _
            iframe Hpp
            simp only [Option.map_some]
            unfold Etcdraft.confChangeRO
            iexists ge2
            iframe Hep Hgnc
            rw [Hge2]
            iexact Hgch
    ihave Hout := Hoclose $$ Hoel
    have Hset : (dn ++ List.replicate (sint.nat sl.len - sint.nat n) (zero_val Etcdraft.G.Event)).set
        (sint.Z n).toNat v' =
        (dn ++ [v']) ++ List.replicate (sint.nat sl.len - sint.nat (n + W64 1)) (zero_val Etcdraft.G.Event) := by
      have hm : sint.nat sl.len - sint.nat n = (sint.nat sl.len - sint.nat (n + W64 1)) + 1 := by word
      rw [hm, List.replicate_succ, show (sint.Z n).toNat = dn.length by rw [hnd],
        List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero, List.append_assoc]
      rfl
    rw [Hset]
    have Htake : List.take (sint.nat (n + W64 1)) L = List.take (sint.nat n) L ++ [e] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, He]; rfl
    wp_for_post
    iframe
    iexists (n + W64 1), n, dn ++ [v']
    iframe
    isplitl []
    · rw [Htake, List.map_append, List.map_singleton]
      simp only [named]
      iapply (BigSepL2.bigSepL2_snoc (PROP := IProp GF)).2
      iframe Hdone Hev
    ipureintro
    refine ⟨by word, by word, by rw [List.length_append, hnd]; simp only [List.length_singleton]; word⟩
  · have hnx : sint.nat n = L.length := by rw [← Hlen, Hgl.1]; word
    have hdl : dn.length = L.length := by rw [hnd, hnx]
    rw [hnx, show sint.nat sl.len - L.length = 0 by rw [← Hlen, Hgl.1]; omega, List.replicate_zero,
      List.append_nil, List.take_length] at *
    imod ownSlice_persist $$ Hout with #Hout
    imodintro
    iapply HΦ
    iunfold Etcdraft.eventsRO
    iexists dn
    iframe Hout Hdone

end proof

end TraceCheck
end EtcdGrove
end Perennial
