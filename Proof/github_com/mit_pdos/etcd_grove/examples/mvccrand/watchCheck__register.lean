/- Lean-first (no Rocq counterpart). The proof of `watchCheck.register`: the loop over the ticks
(`wp_spsc_receive`); each tick a published revision, small (`tick_bound`), so the start revision is
in `[1, pub + 1]`; the watcher's struct; under `c.mu`, `Watch` with the update for its range
(`register_au` when it is not empty: the stream open, the watcher registered in both halves of the
registry; `register_au_empty` when it is, which `Watch` gives back); the lock's map and watchers
grow by the new one (its position at its start, nothing received for its fresh id,
`recvEvs_fresh`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.watchCheck__register
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__intn
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genEnd
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check
public import Spec.context.TODO

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

theorem watchCheck.register.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (errVars : mvcc.api.errVars.law (GF := GF))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_intn : rng.intn.spec (GF := GF) (hG := hG))
    (wp_genKey : rng.genKey.spec (GF := GF) (hG := hG))
    (wp_genEnd : rng.genEnd.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG)) :
    watchCheck.register.spec (GF := GF) (hG := hG) := by
  intro c γ h wm ws r g γt ch rcvd
  haveI := fun kv => hpers.1 kv γ.kv
  haveI := fun ws => hpers.2.1 ws γ.kv γ.ws
  wp_start as ⟨Hctx, #Hws, Htt, Hr, #Hticks, Hcons, Hcl⟩
  iunfold wcCtx at Hctx
  icases Hctx with ⟨#Hpkg, #Hmpkg, #HhF, #HwF, #Hmu, #Hinv, #Hhist, %ws', %kv, #Hws', #Hkv⟩
  ihave %Hsh := (hsh.2.2.2 ws γ.kv γ.ws) $$ Hws
  obtain ⟨tyW, vW, rfl, hWatch, -, hProg, hProgAll, -, -, -⟩ := Hsh
  iunfold isTicks at Hticks
  wp_auto
  ihave IH : (∃ (rc : List w64) (pv : w64) (g1 : rng),
      "pub" ∷ pub_ptr ↦ pv ∗ "Hcons" ∷ spscConsumer (V := w64) γt rc ∗ "Hr" ∷ r ↦ g1 ∗
      "Htt" ∷ threadTok ∗ "Hcl" ∷ ghostVar γ.cl (1 : Qp).half false : IProp GF)
    $$ [pub Hcons Hr Htt Hcl]
  · iexists rcvd, _, g
    iframe
  wp_for IH
  wp_apply wp_spsc_receive γt ch (tickP γ) (fun _ => iprop(True)) rc $$ [$Hticks $Hcons]
    as %v %ok Hv
  cases ok
  · -- the channel closed: the loop's end
    simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ
    iframe
  simp only [↓reduceIte]
  iunfold tickP at Hv
  icases Hv with ⟨⟨%Hv1, #Hvlb⟩, Hcons⟩
  imod tick_bound hpers hreach kv h γ (sint.nat v) $$ [$Hinv $Hkv $Hvlb] with %Hvb
  have hvN : sint.nat v = (sint.Z v).toNat := rfl
  (try wp_auto)
  wp_apply wp_intn r g1 (v + W64 1) (by word) $$ [$Hr] as %x ⟨⟨%g2, Hr⟩, %Hx⟩
  (try wp_auto)
  wp_apply wp_genKey r g2 $$ [$Hr] as %sk ⟨⟨%g3, Hr⟩, %kk, Hsk, Hskc, %Hkk⟩
  (try wp_auto)
  wp_apply wp_genEnd r g3 $$ [$Hr] as %se ⟨⟨%g4, Hr⟩, %e, Hse, Hsec, %He⟩
  (try wp_auto)
  imod ownSlice_persist $$ Hsk with #Hsk
  imod ownSlice_persist $$ Hse with #Hse
  ihave %Hsel := ownSlice_len $$ Hse
  icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨Hwp, %Hwpn⟩
  have hst : 1 ≤ sint.Z (W64 1 + x) := by word
  have hst2 : sint.Z (W64 1 + x) < 2 ^ 63 - 1 := by word
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold cmuInv at HL
  icases HL with ⟨%rs, %W, %Hl, Hwm, Hreg, Hrcv0, #Hlb, %Hknown, Hwats⟩
  (try wp_auto)
  wp_apply wp_ctxTODO
  (try wp_auto)
  ihave #Hflt : filtersImpl slice.nil ([] : List (EvM → Bool)) $$ []
  · iunfold filtersImpl
    iexists []
    isplitl
    · iapply ownSlice_nil
    simp
    isplitl
    · itrivial
    · iempintro
  by_cases hemp : e ≠ [] ∧ ¬ go.GoStringLt kk e
  · -- an empty range: `ErrEmptyWatcherRange`, nothing registered
    have hsen : se ≠ slice.nil := fun hn => hemp.1 (He.2 hn)
    have hcov : ∀ id k, (watchRangeOf kk e se (W64 1 + x) id).covers k = false :=
      fun id k => covers_empty kk e se _ id hemp.1 hemp.2 hsen k
    ihave Hau := register_au_empty hpers h γ kk e se (W64 1 + x) hcov $$ Hinv
    wp_apply (hWatch γ.kv γ.ws todoCtxVal
        { Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) }
        sk se slice.nil kk e [] (W64 1 + x) (fun _ _ _ => iprop(True)))
      $$ [$Hmpkg $Hws $Htt $Hsk $Hse $Hflt $Hau]
    · isplitl []
      · ileft; ipureintro; rfl
      · ipureintro; word
    iintro %id %err ⟨Htt, Hres⟩
    icases Hres with (⟨%Hi, #Herr, -⟩ | ⟨%Hne, -⟩)
    rotate_left
    · exfalso
      rcases Hne with h1 | h1
      · exact hemp.1 h1
      · exact hemp.2 h1
    obtain ⟨-, -, rfl⟩ := Hi
    have hlen0 : se.len ≠ W64 0 := by
      intro h0; apply hemp.1; rw [← List.length_eq_zero_iff, Hsel.1, h0]; rfl
    ihave Hinit := errVars $$ Hmpkg
    icases Hinit with ⟨-, -, #HeEmp⟩
    iunfold errorsNewVar at HeEmp
    icases HeEmp with ⟨%xe, #HeEmp, -⟩
    ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Herr HeEmp
    subst Hag
    (try wp_auto)
    rw [decide_eq_false hlen0]
    (try wp_auto)
    simp only
    wp_apply wp_bytes_to_string se e DFrac.discard $$ [$Hse] as -
    (try wp_auto)
    wp_apply wp_bytes_to_string sk kk DFrac.discard $$ [$Hsk] as -
    (try wp_auto)
    have hle : go.GoStringLe e kk := by
      by_cases hl : go.GoStringLt e kk
      · exact Or.inr hl
      · exact Or.inl (go.goStringLt_eq_of_not_lt hl hemp.2)
    rw [decide_eq_true hle]
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock (cF go!"mu" c) (cmuInv wm γ)
      $$ [$Hmu $Hlocked Hwm Hreg Hrcv0 Hwats]
    · iunfold cmuInv
      iexists rs, W, Hl
      iframe
      iframe #
      ipureintro; exact Hknown
    (try wp_auto)
    wp_for_post
    iframe
    iexists rc ++ [v], v, g4
    iframe
  -- not empty: registered, the stream open
  have hne : e = [] ∨ go.GoStringLt kk e := by
    by_cases h1 : e = []
    · exact Or.inl h1
    · by_cases h2 : go.GoStringLt kk e
      · exact Or.inr h2
      · exact absurd ⟨h1, h2⟩ hemp
  ihave Hau := register_au hpers h γ W «$r0_ptr» kk e se (W64 1 + x) hst $$ [$Hinv $Hreg $Hcl]
  wp_apply (hWatch γ.kv γ.ws todoCtxVal
      { Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) }
      sk se slice.nil kk e [] (W64 1 + x) (regQ γ W «$r0_ptr» kk e se (W64 1 + x)))
    $$ [$Hmpkg $Hws $Htt $Hsk $Hse $Hflt $Hau]
  · isplitl []
    · ileft; ipureintro; rfl
    · ipureintro; word
  iintro %id %err ⟨Htt, Hres⟩
  icases Hres with (⟨%Hi, -, -⟩ | ⟨-, %σ, %S, HQ, Herr⟩)
  · exfalso
    rcases hne with h1 | h1
    · exact Hi.1 h1
    · exact Hi.2.1 h1
  iunfold regQ at HQ
  icases HQ with ⟨%HQ, Hcl, Hreg⟩
  rw [HQ.1]
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Herr with %Herr
  subst Herr
  (try wp_auto)
  by_cases he0 : e = []
  · have hl0 : se.len = W64 0 := by
      have h1 := Hsel.1; rw [he0] at h1; simp at h1; word
    rw [decide_eq_true hl0]
    (try wp_auto)
    (try wp_auto)
    wp_apply wp_check
    · itrivial
    (try wp_auto)
    wp_apply wp_mapInsert $$ [$Hwm] as Hwm
    rw [show <[id := «$r0_ptr»]> (GMap.fmap Prod.fst W) = GMap.fmap Prod.fst
        (<[id := («$r0_ptr», (kk, e, decide (se = slice.nil), W64 1 + x))]> W) by
      rw [GMap.fmap_insert]]
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock (cF go!"mu" c) (cmuInv wm γ)
      $$ [$Hmu $Hlocked Hwm Hreg Hrcv0 Hwats Hwp]
    · iunfold cmuInv
      iexists rs, <[id := («$r0_ptr», (kk, e, decide (se = slice.nil), W64 1 + x))]> W, Hl
      iframe
      iframe #
      isplitr
      · ipureintro; exact rcvKnown_insert Hknown id _
      iapply (BigSepM.bigSepM_insert (Φ := fun (id : w64) (x : Loc × RegInfo) =>
        watcherOwn (GF := GF) Hl rs id x.1 x.2) HQ.2).2
      iframe
      iunfold watcherOwn
      iexists _
      iframe
      iframe #
      ipureintro
      have hkk' : kk ≠ [] := by intro h0; subst h0; revert Hkk; decide
      refine ⟨rfl, hkk', hst, hst2, ?_⟩
      rw [recvEvs_fresh Hknown HQ.2]
      exact ⟨by simp only; word, by simp only; word, posOk_start _ _ _, Or.inr ⟨rfl, rfl, rfl⟩⟩
    (try wp_auto)
    wp_apply wp_intn r g4 (W64 3) (by decide) $$ [$Hr] as %sw ⟨⟨%g5, Hr⟩, %Hsw⟩
    (try wp_auto)
    wp_if_destruct
    · wp_apply (hProg γ.kv γ.ws id) $$ [$Hmpkg $Hws $Htt] as Htt
      (try wp_auto)
      wp_for_post
      iframe
      iexists rc ++ [v], v, g5
      iframe
    wp_if_destruct
    · wp_apply (hProgAll γ.kv γ.ws) $$ [$Hmpkg $Hws $Htt] as %b Htt
      (try wp_auto)
      wp_for_post
      iframe
      iexists rc ++ [v], v, g5
      iframe
    (try wp_auto)
    wp_for_post
    iframe
    iexists rc ++ [v], v, g5
    iframe
  · have hlen0 : se.len ≠ W64 0 := by
      intro h0; apply he0; rw [← List.length_eq_zero_iff, Hsel.1, h0]; rfl
    have hlt : go.GoStringLt kk e := hne.resolve_left he0
    rw [decide_eq_false hlen0]
    (try wp_auto)
    simp only
    wp_apply wp_bytes_to_string se e DFrac.discard $$ [$Hse] as -
    (try wp_auto)
    wp_apply wp_bytes_to_string sk kk DFrac.discard $$ [$Hsk] as -
    (try wp_auto)
    have hle : ¬ go.GoStringLe e kk := by
      rintro (h | h)
      · rw [h] at hlt; exact go.goStringLt_irrefl _ hlt
      · exact go.goStringLt_asymm hlt h
    rw [decide_eq_false hle]
    (try wp_auto)
    wp_apply wp_check
    · itrivial
    (try wp_auto)
    wp_apply wp_mapInsert $$ [$Hwm] as Hwm
    rw [show <[id := «$r0_ptr»]> (GMap.fmap Prod.fst W) = GMap.fmap Prod.fst
        (<[id := («$r0_ptr», (kk, e, decide (se = slice.nil), W64 1 + x))]> W) by
      rw [GMap.fmap_insert]]
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock (cF go!"mu" c) (cmuInv wm γ)
      $$ [$Hmu $Hlocked Hwm Hreg Hrcv0 Hwats Hwp]
    · iunfold cmuInv
      iexists rs, <[id := («$r0_ptr», (kk, e, decide (se = slice.nil), W64 1 + x))]> W, Hl
      iframe
      iframe #
      isplitr
      · ipureintro; exact rcvKnown_insert Hknown id _
      iapply (BigSepM.bigSepM_insert (Φ := fun (id : w64) (x : Loc × RegInfo) =>
        watcherOwn (GF := GF) Hl rs id x.1 x.2) HQ.2).2
      iframe
      iunfold watcherOwn
      iexists _
      iframe
      iframe #
      ipureintro
      have hkk' : kk ≠ [] := by intro h0; subst h0; revert Hkk; decide
      refine ⟨rfl, hkk', hst, hst2, ?_⟩
      rw [recvEvs_fresh Hknown HQ.2]
      exact ⟨by simp only; word, by simp only; word, posOk_start _ _ _, Or.inr ⟨rfl, rfl, rfl⟩⟩
    (try wp_auto)
    wp_apply wp_intn r g4 (W64 3) (by decide) $$ [$Hr] as %sw ⟨⟨%g5, Hr⟩, %Hsw⟩
    (try wp_auto)
    wp_if_destruct
    · wp_apply (hProg γ.kv γ.ws id) $$ [$Hmpkg $Hws $Htt] as Htt
      (try wp_auto)
      wp_for_post
      iframe
      iexists rc ++ [v], v, g5
      iframe
    wp_if_destruct
    · wp_apply (hProgAll γ.kv γ.ws) $$ [$Hmpkg $Hws $Htt] as %b Htt
      (try wp_auto)
      wp_for_post
      iframe
      iexists rc ++ [v], v, g5
      iframe
    (try wp_auto)
    wp_for_post
    iframe
    iexists rc ++ [v], v, g5
    iframe

end proof

end mvccrand
end EtcdGrove
end Perennial
