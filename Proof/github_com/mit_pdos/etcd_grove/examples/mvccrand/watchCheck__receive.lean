/- Lean-first (no Rocq counterpart). The proof of `watchCheck.receive`: under `c.mu`, the tester's
invariant gives, at its state, mvcc's watch guarantee of the responses received so far
(`wsRecv_ok.law`), the history covering the notified log (`histOkM`), no compaction and the
registry (`regOk`) (`recv_facts`). Then: no compaction response; a progress response at a revision
written (the snapshot has it), its watcher's expected changes up to it already received
(`recv_prog`: `expect` returns none); each event its watcher's next expected change (`recv_exp`:
the events received for it are its expected changes, so the `n`-th is `expect`'s at the watcher's
position, `expNext_of_get`), whose event mvcc made of it (`chEv`: key, type, fields); the watcher
advanced (`posOk_advW`). The lock's invariant moves to `rs ++ [r]` at the longer of its history's
lower bound and the invariant's (`wPosOk_prefix`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.watchCheck__receive
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.watchCheck__expect
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.watcher__advance
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.checkKV
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem watchCheck.receive.wp_proof
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hrok : mvcc.api.wsRecv_ok.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_expect : watchCheck.expect.spec (GF := GF) (hG := hG))
    (wp_advance : watcher.advance.spec (GF := GF) (hG := hG))
    (wp_checkKV : checkKV.spec (GF := GF) (hG := hG)) :
    watchCheck.receive.spec (GF := GF) (hG := hG) := by
  intro c γ h wm rs r resp ne
  haveI := fun kv => hpers.1 kv γ.kv
  haveI := fun ws => hpers.2.1 ws γ.kv γ.ws
  wp_start as ⟨Hctx, Hrd, Hrcv, Hresp, Hhalf, Hev⟩
  iunfold wrespIs at Hresp
  icases Hresp with ⟨%Hfl, %ps, #Hps, %Hpsl, Hevs⟩
  icases (evOwns_split _ 1).1 $$ Hevs with ⟨#Hevs, -⟩
  iunfold wcCtx at Hctx
  icases Hctx with ⟨#Hpkg, #Hmpkg, #HhF, #HwF, #Hmu, #Hinv, #Hhist, %ws, %kv, #Hws, #Hkv⟩
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold cmuInv at HL
  icases HL with ⟨%rs0, %W, %Hl, Hwm, Hreg, Hrcv0, #Hlb, %Hknown, Hwats⟩
  ihave %Hrs := ghostVar_agree γ.rcv _ _ _ _ $$ Hrcv0 Hhalf
  subst Hrs
  imod recv_facts hpers hreach hrok h γ ws kv (rs0 ++ [r]) W $$ [$Hinv $Hws $Hkv $Hrcv $Hreg]
    with ⟨Hrcv, Hreg, %σ, %S, %Hlw, #Hlbw, %Hfacts⟩
  obtain ⟨Hro, Hh, Hcr, HregOk, hwf, hnl⟩ := Hfacts
  -- the longer of the two lower bounds of the history
  ihave %Hcmp := mono_list_lb_valid γ.h.l Hl Hlw $$ Hlb Hlbw
  obtain ⟨Hlx, hpx, hpwx, hx⟩ : ∃ Hlx, Hl <+: Hlx ∧ Hlw <+: Hlx ∧ (Hlx = Hlw ∨ Hlx = Hl) := by
    rcases Hcmp with hc | hc
    · exact ⟨Hlw, hc, List.prefix_refl _, Or.inl rfl⟩
    · exact ⟨Hl, List.prefix_refl _, hc, Or.inr rfl⟩
  ihave #Hlbx : monoListLbOwn γ.h.l Hlx $$ []
  · rcases hx with rfl | rfl
    · iexact Hlbw
    · iexact Hlb
  have hNL : σ.notifiedLog.length ≤ Hlx.length := Nat.le_trans Hh.1 hpwx.length_le
  -- the response's facts
  have hrmem : r ∈ rs0 ++ [r] := by simp
  obtain ⟨hid, hevle, hcr0, hcrne, hm1, hpos⟩ := Hro.1 r hrmem
  have hcr : r.compactRev = W64 0 := by
    by_cases hne : r.compactRev = W64 0
    · exact hne
    · have h1 := (hcrne hne).2.2.2.2
      rw [Hcr] at h1
      have h2 := (hcrne hne).2.2.2.1
      omega
  wp_apply wp_check
  · ipureintro; simp only [decide_eq_true_eq]; rw [Hfl.2.2, hcr]
  ihave %Hpsn := ownSlice_len $$ Hps
  have hrevl : sint.nat r.rev < σ.notifiedLog.length := hcr0 hcr
  imod ghostVar_update_halves (rs0 ++ [r]) γ.rcv _ _ $$ Hrcv0 Hhalf with ⟨Hrcv0, Hhalf⟩
  (try wp_auto)
  wp_if_destruct
  · -- a progress response
    have hev : r.evs = [] := by
      rw [← List.length_eq_zero_iff, ← Hpsl, Hpsn.1, Hif]; rfl
    have hneq : ne + W64 ((r.evs.length : Nat) : Int) = ne := by
      rw [hev]; exact BitVec.add_zero ne
    have hsame : ∀ id, recvEvs (rs0 ++ [r]) id = recvEvs rs0 id :=
      fun id => recvEvs_snoc_ne _ _ _ (Or.inr hev)
    have hknown' : rcvKnown (rs0 ++ [r]) W := by
      intro r' hr' hne
      rcases List.mem_append.1 hr' with hr' | hr'
      · exact Hknown r' hr' hne
      · rw [List.mem_singleton] at hr'; subst hr'; exact absurd hev hne
    (try wp_auto)
    wp_apply wp_snapshot h γ.h Hlx $$ [$Hrd $Hlbx] as %sl ⟨Hrd, %ms, %Hs, %Hsub, %Hcap, #HlbS, #Hms, #Hst⟩
    ihave %Hmsl := ownSlice_len $$ Hms
    ihave %Hmsn : ⌜ms.length = Hs.length⌝ $$ [Hst]
    · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
    wp_apply wp_check
    · ipureintro; simp only [decide_eq_true_eq]
      have := Hsub.1.length_le
      rw [Hfl.2.1]; word
    (try wp_auto)
    wp_apply wp_map_lookup1 $$ Hwm as Hwm
    rw [Hfl.1]
    cases hW : W !! r.id with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      (try wp_auto)
      ihave Hwats := wats_frame (GF := GF) hpx W hsame $$ Hwats
      wp_apply sync.Mutex.wp_Unlock (cF go!"mu" c) (cmuInv wm γ)
        $$ [$Hmu $Hlocked Hwm Hreg Hrcv0 Hwats]
      · iunfold cmuInv
        iexists rs0 ++ [r], W, Hlx
        iframe
        iframe #
        ipureintro; exact hknown'
      (try wp_auto)
      iapply HΦ
      rw [hneq]
      iframe
    | some x =>
      obtain ⟨wp, kk, e, en, st⟩ := x
      simp only [Option.map_some, Option.getD_some]
      icases (wats_take (GF := GF) hpx W r.id (wp, (kk, e, en, st)) hW (fun id _ => hsame id))
        $$ Hwats with ⟨Hwo, Hback⟩
      iunfold watcherOwn at Hwo
      icases Hwo with ⟨%wv, Hwp, #Hk, #He, %Hwo⟩
      icases (typedPointsto_not_null_dup _ _ _) $$ Hwp with ⟨Hwp, %Hwpn⟩
      obtain ⟨hen, hkk, hst1, hst2, hpos0⟩ := Hwo
      simp only at hen hkk hst1 hst2
      have hpos1 := wPosOk_prefix hpx _ _ _ _ hpos0
      have hreg := HregOk r.id
      rw [hW] at hreg
      obtain ⟨wi, hwi, hrg, hfs, hlo, -⟩ := hreg
      have hrg' : wi.rg = watchRangeOf kk e wv.end' st r.id := by
        rw [hrg]; exact rg_eq kk e wv.end' en st r.id hen
      have hprog := recv_prog σ S (rs0 ++ [r]) Hlx Hro (histOkM_prefix Hh hpwx) Hcr hwf hnl
        rs0.length r (by simp) hev hcr wi hwi kk e wv.end' st hrg' hfs hlo hkk hst1
      rw [List.take_of_length_le (by simp), hsame] at hprog
      have hnone : expNext Hlx (inRangeM (decide (wv.end' = slice.nil)) kk e) (sint.nat wv.rev')
          (sint.nat wv.index') (sint.Z r.rev) = none := by
        have hp := hpos1.2.2.1
        simp only [regInR, regLo] at hp
        rw [hen] at hp
        refine expNext_none_of_length _ _ _ _ _ _ _ (by word) hp ?_
        rw [hprog, List.length_map]
        exact Nat.le_refl _
      (try wp_auto)
      rw [decide_eq_false Hwpn]
      (try wp_auto)
      rw [Hfl.2.1]
      wp_apply wp_expect c h γ.h Hlx wp wv kk e r.rev DFrac.discard (DFrac.own 1) DFrac.discard
        DFrac.discard hpos1.1 hpos1.2.1 (by have := hNL; word) (by have := hnl; word)
        $$ [$HhF $Hwp $Hk $He $Hrd $Hlbx] as %ch %rr %ok ⟨-, Hwp, -, -, Hrd, %Hres⟩
      unfold expRes at Hres
      rw [hnone] at Hres
      subst Hres
      (try wp_auto)
      wp_apply wp_check
      · ipureintro; rfl
      (try wp_auto)
      ihave Hwats := Hback $$ [Hwp]
      · iunfold watcherOwn
        iexists wv
        iframe
        iframe #
        ipureintro
        rw [hsame]
        exact ⟨hen, hkk, hst1, hst2, hpos1⟩
      wp_apply sync.Mutex.wp_Unlock (cF go!"mu" c) (cmuInv wm γ)
        $$ [$Hmu $Hlocked Hwm Hreg Hrcv0 Hwats]
      · iunfold cmuInv
        iexists rs0 ++ [r], W, Hlx
        iframe
        iframe #
        ipureintro; exact hknown'
      (try wp_auto)
      iapply HΦ
      rw [hneq]
      iframe
  -- a response with events: its watcher is registered
  have hev : r.evs ≠ [] := by
    intro he; apply Hif; rw [he, List.length_nil] at Hpsl
    have h1 := Hpsn.1; rw [Hpsl] at h1; have h2 := Hpsn.2; word
  have hidn : r.id ≠ W64 (-1) := fun h => hev (hm1 h).1
  have hSs := hid hidn
  obtain ⟨⟨wp, kk, e, en, st⟩, hW⟩ : ∃ x, W !! r.id = some x := by
    cases hW : W !! r.id with
    | some x => exact ⟨x, rfl⟩
    | none =>
      have hreg := HregOk r.id
      rw [hW] at hreg
      simp only at hreg
      obtain ⟨wi, hwi⟩ := Option.isSome_iff_exists.1 hSs
      have h0 := recvEvs_uncovered σ S (rs0 ++ [r]) Hro Hcr r.id wi hwi (hreg wi hwi)
      rw [recvEvs_snoc] at h0
      simp only [↓reduceIte, List.append_eq_nil_iff] at h0
      exact absurd h0.2 hev
  have hknown' : rcvKnown (rs0 ++ [r]) W := by
    intro r' hr' hne
    rcases List.mem_append.1 hr' with hr' | hr'
    · exact Hknown r' hr' hne
    · rw [List.mem_singleton] at hr'; subst hr'; rw [hW]; rfl
  have hsame : ∀ id, id ≠ r.id → recvEvs (rs0 ++ [r]) id = recvEvs rs0 id :=
    fun id hne => recvEvs_snoc_ne _ _ _ (Or.inl (Ne.symm hne))
  icases (wats_take (GF := GF) hpx W r.id (wp, (kk, e, en, st)) hW hsame)
    $$ Hwats with ⟨Hwo, Hback⟩
  iunfold watcherOwn at Hwo
  icases Hwo with ⟨%wv, Hwp, #Hk, #He, %Hwo⟩
  icases (typedPointsto_not_null_dup _ _ _) $$ Hwp with ⟨Hwp, %Hwpn⟩
  obtain ⟨hen, hkk, hst1, hst2, hpos0⟩ := Hwo
  simp only at hen hkk hst1 hst2 Hwpn
  have hpos1 := wPosOk_prefix hpx _ _ _ _ hpos0
  have hreg := HregOk r.id
  rw [hW] at hreg
  obtain ⟨wi, hwi, hrg, hfs, hlo, -⟩ := hreg
  have hrg' : wi.rg = watchRangeOf kk e wv.end' st r.id := by
    rw [hrg]; exact rg_eq kk e wv.end' en st r.id hen
  have Hhx := histOkM_prefix Hh hpwx
  obtain ⟨hi, hhi, hE⟩ := recv_exp σ S (rs0 ++ [r]) Hlx Hro Hhx Hcr hwf hnl r.id wi hwi kk e
    wv.end' st hrg' hfs hlo hkk hst1
  (try wp_auto)
  wp_apply wp_map_lookup1 $$ Hwm as Hwm
  rw [Hfl.1, hW]
  simp only [Option.map_some, Option.getD_some]
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp [Hwpn]
  (try wp_auto)
  have hregIn : regInR (kk, e, en, st) = inRangeM (decide (wv.end' = slice.nil)) kk e := by
    simp only [regInR]; rw [hen]
  have hlo1 : 1 ≤ sint.nat st := by have : sint.nat st = (sint.Z st).toNat := rfl; omega
  have hpmem : ∀ p, p ∈ expChs Hlx (inRangeM (decide (wv.end' = slice.nil)) kk e) (sint.nat st) hi →
      (chEv p.1 p.2).kv.modRev = W64 (p.1 : Int) ∧ p.1 < σ.notifiedLog.length :=
    fun p hp => ⟨chEv_modRev σ.notifiedLog Hlx Hhx.2 _ _ hi hlo1 hhi p hp,
      by have := (mem_expChs hp).2.1; omega⟩
  ihave IH : (∃ (j : w64) (evp : Loc) (wv' : watcher) (nev : w64),
      "i" ∷ i_ptr ↦ j ∗ "ev" ∷ ev_ptr ↦ evp ∗ "Hwp" ∷ wp ↦ wv' ∗
      "Hev" ∷ cF go!"events" c ↦ nev ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ r.evs.length ∧ nev = ne + W64 ((sint.nat j : Nat) : Int) ∧
        wv'.key' = wv.key' ∧ wv'.end' = wv.end' ∧
        wPosOk Hlx (kk, e, en, st) wv'.rev' wv'.index' ((recvEvs rs0 r.id).length + sint.nat j)⌝ :
        IProp GF)
      $$ [i ev Hwp Hev]
  · iexists W64 0, _, wv, ne
    iframe
    ipureintro
    refine ⟨by word, by word, ?_, rfl, rfl, hpos1⟩
    exact (BitVec.add_zero ne).symm
  wp_for IH
  obtain ⟨hj0, hjle, hnev, hkey, hend, hposj⟩ := Hj
  by_cases Hlt : sint.Z j < sint.Z resp.Events'.len
  rotate_left
  · -- every event checked
    rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hjn : sint.nat j = r.evs.length := by
      have h1 := Hpsn.1; rw [Hpsl] at h1; word
    (try wp_auto)
    ihave Hwats := Hback $$ [Hwp]
    · iunfold watcherOwn
      iexists wv'
      iframe
      rw [hkey, hend]
      iframe #
      ipureintro
      rw [recvEvs_snoc]
      simp only [↓reduceIte, List.length_append]
      rw [← hjn]
      exact ⟨hend ▸ hen, hkk, hst1, hst2, hposj⟩
    wp_apply sync.Mutex.wp_Unlock (cF go!"mu" c) (cmuInv wm γ)
      $$ [$Hmu $Hlocked Hwm Hreg Hrcv0 Hwats]
    · iunfold cmuInv
      iexists rs0 ++ [r], W, Hlx
      iframe
      iframe #
      ipureintro; exact hknown'
    (try wp_auto)
    iapply HΦ
    rw [hnev, hjn]
    iframe
  rw [decide_eq_true Hlt]; simp only [↓reduceIte]
  have hjl : sint.nat j < r.evs.length := by
    have h1 := Hpsn.1; rw [Hpsl] at h1; word
  obtain ⟨pk, hpk⟩ : ∃ pk, ps[sint.nat j]? = some pk :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨evk, hevk⟩ : ∃ evk, r.evs[sint.nat j]? = some evk :=
    ⟨_, List.getElem?_eq_getElem hjl⟩
  have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z resp.Events'.len := ⟨hj0, Hlt⟩
  (try wp_auto)
  (try simp only [hb, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index resp.Events' (sint.Z j) ps DFrac.discard pk hj0 $$ [Hps] as -
  · iframe #; ipureintro; exact hpk
  have hz : (ps.zip r.evs)[sint.nat j]? = some (pk, evk) := by
    rw [List.getElem?_zip_eq_some]; exact ⟨hpk, hevk⟩
  ihave #Hevk := BigSepL.bigSepL_lookup hz $$ Hevs
  iunfold evRd at Hevk
  icases Hevk with ⟨%pp, %st', %uf, %sc, %Hnn, #HstE, #HtyE, #Hept, #HufE, #HscE, #Hkvf⟩
  iunfold kvPtrFixed at Hkvf
  icases Hkvf with ⟨%ks, %vs, %st2, %uf2, %sc2, #Hks, #Hvs, #Hkp⟩
  obtain ⟨⟨r1, ch1⟩, hEp, hevp⟩ := recv_ev_get hE hevk
  have hpE := List.mem_of_getElem? hEp
  obtain ⟨hmod, hpl⟩ := hpmem _ hpE
  simp only at hmod hpl hevp
  have hmodk : evk.kv.modRev = W64 (r1 : Int) := by rw [hevp]; exact hmod
  have hr1Z : sint.Z (W64 (r1 : Int)) = r1 := by word
  have hle := hevle evk (List.mem_of_getElem? hevk)
  simp only at Hnn
  iStructNamedSuffix Hkp "K"
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp only [decide_eq_true_eq]; rw [Hfl.2.1]; exact hle
  (try wp_auto)
  have hpk' : posOk Hlx (inRangeM (decide (wv.end' = slice.nil)) kk e) (sint.nat st)
      (sint.nat wv'.rev') (sint.nat wv'.index') ((recvEvs rs0 r.id).length + sint.nat j) := by
    have hp := hposj.2.2.1; rw [hregIn] at hp; exact hp
  have hexp := expNext_of_get Hlx _ (sint.nat st) _ _ _ hi r1 ch1 hlo1 hpk' hEp
  ihave #Hk' : wv'.key' ↦*□ kk $$ []
  · rw [hkey]; iexact Hk
  ihave #He' : wv'.end' ↦*□ e $$ []
  · rw [hend]; iexact He
  wp_apply wp_expect c h γ.h Hlx wp wv' kk e evk.kv.modRev DFrac.discard (DFrac.own 1)
      DFrac.discard DFrac.discard hposj.1 hposj.2.1 (by rw [hmodk, hr1Z]; omega)
      (by rw [hmodk, hr1Z]; omega)
    $$ [$HhF $Hwp $Hk' $He' $Hrd $Hlbx] as %ch %rr %ok ⟨-, Hwp, -, -, Hrd, %Hres⟩
  rw [hend, hmodk, hr1Z] at Hres
  unfold expRes at Hres
  rw [hexp] at Hres
  obtain ⟨rfl, rfl, rfl, hlenR⟩ := Hres
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp [hmodk]
  (try wp_auto)
  wp_apply wp_bytes_to_string ks evk.kv.key DFrac.discard $$ [$Hks] as -
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp only [decide_eq_true_eq]; rw [hevp, chEv_key]
  (try wp_auto)
  cases hdel : ch.del'
  · -- a put
    have hkv : evk = ⟨false, kvOfRec ch.key' ch.kv', none⟩ := by
      rw [hevp]; unfold chEv; simp [hdel]
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp [hkv, evType]
    (try wp_auto)
    wp_apply wp_checkKV pp _ DFrac.discard DFrac.discard DFrac.discard evk.kv.key evk.kv.value
      ch.key' ch.kv' false (by rw [hkv]; simp [kvMatches, kvOfRec]) $$ [$Hkp $Hks $Hvs] as -
    (try wp_auto)
    wp_apply wp_advance wp wv' evk.kv.modRev $$ [$Hwp] as Hwp
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, pk, advW wv' evk.kv.modRev, nev + W64 1
    iframe
    ipureintro
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    refine ⟨by word, by word, ?_, by rw [advW_key, hkey], by rw [advW_end, hend], ?_⟩
    · rw [hnev, hj1]; word
    · have ha := wPosOk_adv Hlx (kk, e, en, st) wv' _ (r1, ch) hposj
        (by rw [hregIn]; exact hexp) (by omega) (by omega) (by rw [hregIn]; exact hlenR)
      rw [hmodk, hj1, ← Nat.add_assoc]
      exact ha
  · -- a delete
    have hkv : evk = ⟨true, { zeroKv ch.key' with modRev := W64 (r1 : Int) }, none⟩ := by
      rw [hevp]; unfold chEv; simp [hdel]
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp [hkv, evType]
    ihave %Hvsl := ownSlice_len $$ Hvs
    have hc0 : evk.kv.createRev = W64 0 := by rw [hkv]; rfl
    have hv0 : evk.kv.version = W64 0 := by rw [hkv]; rfl
    have hl0 : vs.len = W64 0 := by
      rw [hkv] at Hvsl; simp [zeroKv] at Hvsl; word
    (try wp_auto)
    rw [decide_eq_true hc0]
    (try wp_auto)
    rw [decide_eq_true hv0]
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp [hl0]
    (try wp_auto)
    wp_apply wp_advance wp wv' evk.kv.modRev $$ [$Hwp] as Hwp
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, pk, advW wv' evk.kv.modRev, nev + W64 1
    iframe
    ipureintro
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    refine ⟨by word, by word, ?_, by rw [advW_key, hkey], by rw [advW_end, hend], ?_⟩
    · rw [hnev, hj1]; word
    · have ha := wPosOk_adv Hlx (kk, e, en, st) wv' _ (r1, ch) hposj
        (by rw [hregIn]; exact hexp) (by omega) (by omega) (by rw [hregIn]; exact hlenR)
      rw [hmodk, hj1, ← Nat.add_assoc]
      exact ha

end proof

end mvccrand
end EtcdGrove
end Perennial
