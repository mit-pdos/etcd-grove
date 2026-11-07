/-
Lean-first (no Rocq counterpart).

The proof of `RunLin`: the clients and porcupine's check (what `Run`'s proof was until `Run`
became `RunLin` without the linearization), then the linearization porcupine returned
(`linInfoOk`), reordered by `orderByLinearization` (`isLinearization_order`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.RunLin
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.orderByLinearization
public import Spec.github_com.anishathalye.porcupine.LinearizationInfo__PartialLinearizations
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.runClient
public import Spec.github_com.anishathalye.porcupine.CheckOperationsVerbose
public import Proof.github_com.anishathalye.porcupine.Soundness
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Spec.sync.WaitGroup__Wait
public import Perennial.Proof.sync.WaitGroupJoin
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.RunLemmas
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.Assumptions]

theorem RunLin.wp_proof
    (wp_runClient : runClient.spec (GF := GF) (hG := hG))
    (wp_CheckOperationsVerbose : porcupine.CheckOperationsVerbose.spec (GF := GF) (hG := hG))
    (wp_PartialLinearizations :
      porcupine.LinearizationInfo.PartialLinearizations.spec (GF := GF) (hG := hG))
    (wp_orderByLinearization : orderByLinearization.spec (GF := GF) (hG := hG)) :
    RunLin.spec (GF := GF) (hG := hG) :=
    fun σ S m apply gen clock inOk libState clockVal t0 Eapp Eclk clients ops dur HEapp HEclk
      Hc0 Hc31 Hops Hbound => by
  wp_start as ⟨#Hcc, #Hmodel, #Happly, #Hgen, #Hclock, Hlib, Hclk⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := GoSlice) clients) as %hsl ⟨Hhs, -⟩
  · ipureintro; exact Hc0
  ihave %Hhl := ownSlice_len _ _ _ $$ Hhs
  ihave Hcells := ownSlice_replicate_elems hsl (sint.nat clients) (zero_val GoSlice) (DFrac.own 1)
    $$ Hhs
  imod initMap_alloc (GF := GF) (sint.nat clients) ([], t0) with ⟨%γ, Hauth, Htoks⟩
  imod inv_alloc lintestN ⊤ (linInv S.M libState clockVal (sint.nat clients) γ)
    $$ [Hlib Hclk Hauth] with #Hinv
  · inext
    iexists S.M.init, t0, [], _
    iframe
    ipureintro
    exact InvOk.init S.M (sint.nat clients) t0
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, Hwg⟩
  imod sync.join.init wg_ptr γwg $$ Hwg with Hwg
  ihave Hwg := sync.join.ownAdder_wand
    iprop([∗list] c ∈ List.range (sint.nat (W64 0)), clientDone S γ hsl (sint.nat ops) c)
    wg_ptr (W32 0) iprop(True) $$ [] Hwg
  · iintro _
    rw [show sint.nat (W64 0) = 0 from rfl, List.range_zero]
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  ipersist histories
  ipersist ops
  ipersist gen
  ipersist apply
  ipersist clock
  have H00 : sint.nat (W64 0) = 0 := rfl
  ihave Hcells : ([∗list] c ∈ List.range' (sint.nat (W64 0)) (sint.nat clients - sint.nat (W64 0)),
      typedPointsto (sliceIndexRef GoSlice ((c : Nat) : Int) hsl) (zero_val GoSlice)
        (DFrac.own 1) : IProp GF) $$ [Hcells]
  · rw [H00, Nat.sub_zero, ← List.range_eq_range']; iexact Hcells
  ihave Htoks : ([∗list] c ∈ List.range' (sint.nat (W64 0)) (sint.nat clients - sint.nat (W64 0)),
      clientTok γ c ([], t0) : IProp GF) $$ [Htoks]
  · rw [H00, Nat.sub_zero, ← List.range_eq_range']; iexact Htoks
  ihave HI : (∃ (k : w64) (p : Loc) (na : w32),
      "Hiter" ∷ «$iter_id_ptr» ↦ p ∗ "idc" ∷ p ↦ k ∗
      "Hwg" ∷ sync.join.ownAdder wg_ptr na
        ([∗list] c ∈ List.range (sint.nat k), clientDone S γ hsl (sint.nat ops) c) ∗
      "Hcells" ∷ ([∗list] c ∈ List.range' (sint.nat k) (sint.nat clients - sint.nat k),
        typedPointsto (sliceIndexRef GoSlice ((c : Nat) : Int) hsl) (zero_val GoSlice)
          (DFrac.own 1)) ∗
      "Htoks" ∷ ([∗list] c ∈ List.range' (sint.nat k) (sint.nat clients - sint.nat k),
        clientTok γ c ([], t0)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z clients ∧ sint.Z na = sint.Z k⌝ : IProp GF)
    $$ [«$iter_id» id Hwg Hcells Htoks]
  · iexists W64 0, id_ptr, W32 0
    iframe
    ipureintro
    exact ⟨by decide, by word, by decide⟩
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z k < sint.Z clients := by simpa using Hif
    have hkn : sint.nat k < sint.nat clients := by word
    wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add
      (clientDone S γ hsl (sint.nat ops) (sint.nat k)) wg_ptr _ na) $$ [Hwg] as ⟨Hwg, Hdone⟩
    · iframe; ipureintro; word
    rw [show sint.nat clients - sint.nat k = (sint.nat clients - (sint.nat k + 1)) + 1 by omega,
      List.range'_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hcells with ⟨Hcell, Hcells⟩
    icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Htok, Htoks⟩
    ipersist idc
    wp_apply wp_fork_tok_body $$ [Hdone Hcell Htok]
    · iintro Htt
      wp_auto
      wp_apply wp_runClient σ S inOk libState clockVal Eapp Eclk (sint.nat clients) γ apply gen
        clock k ops t0 HEapp HEclk Hk.1 $$ [Htok Htt] as %sl ⟨%hc, %Lc, %lr', Hsl, Htok, %Hok, #Hio, Htt⟩
      · iframe #
        iframe
      have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z hsl.len := by
        have := Hhl.1
        simp only [List.length_replicate] at this
        exact ⟨Hk.1, by word⟩
      rw [ite_eq_left Hb]
      have hkk : ((sint.nat k : Nat) : Int) = sint.Z k := by word
      ihave Hcell : (typedPointsto (sliceIndexRef GoSlice (sint.Z k) hsl) (zero_val GoSlice)
          (DFrac.own 1) : IProp GF) $$ [Hcell]
      · rw [← hkk]; iexact Hcell
      wp_auto
      wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done
        (clientDone S γ hsl (sint.nat ops) (sint.nat k)) wg_ptr) $$ [Hdone Hcell Hsl Htok]
      · iframe Hdone
        unfold clientDone
        iexists sl, hc, Lc, lr', k
        rw [hkk]
        iframe
        isplitr
        · ipureintro; exact Hok
        iframe #
      iframe Htt
    wp_for_post
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    iframe
    iexists (k + W64 1), id_ptr, (na + W32 1)
    rw [hk1]
    iframe
    unfold named
    isplitl [Hwg]
    · iapply sync.join.ownAdder_wand $$ [] Hwg
      iintro ⟨H1, H2⟩
      rw [List.range_succ]
      iapply BigSepL.bigSepL_snoc.2
      iframe
    ipureintro
    refine ⟨by word, by word, by word⟩
  · have Hkc : sint.nat k = sint.nat clients := by
      have : ¬ sint.Z k < sint.Z clients := by simpa using Hif
      word
    rw [Hkc]
    iclear Hcells Htoks
    wp_apply (lc := 2) (sync.join.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait _ na wg_ptr) $$ [$Hwg]
      as ⟨Hres, -⟩
    imod lc_fupd_elim_later $$ Hlc1 Hres with Hres
    iclear Hiter idc
    ihave Hnil := ownSlice_nil (V := Operation) (GF := GF) (DFrac.own 1)
    ihave Hocap := ownSliceCap_nil (V := Operation) (GF := GF)
    ihave Htoks0 := (BigSepL.bigSepL_nil (PROP := IProp GF) (A := Nat × ClientV)
      (Φ := fun _ p => clientTok γ p.1 p.2)).2 $$ []
    · iempintro
    ihave Hres : ([∗list] c ∈ List.range' (sint.nat (W64 0)) (sint.nat clients - sint.nat (W64 0)),
        clientDone S γ hsl (sint.nat ops) c : IProp GF) $$ [Hres]
    · rw [H00, Nat.sub_zero, ← List.range_eq_range']; iexact Hres
    ihave HJ : (∃ (j : w64) (osl : GoSlice) (hs : List (List Operation))
        (ps : List (Nat × ClientV)) (hv : GoSlice),
        "i" ∷ i_ptr ↦ j ∗ "operations" ∷ operations_ptr ↦ osl ∗ "Hops" ∷ osl ↦* hs.flatten ∗
        "Hocap" ∷ ownSliceCap Operation osl (DFrac.own 1) ∗ "h" ∷ h_ptr ↦ hv ∗
        "Hres" ∷ ([∗list] c ∈ List.range' (sint.nat j) (sint.nat clients - sint.nat j),
          clientDone S γ hsl (sint.nat ops) c) ∗
        "Htoks" ∷ ([∗list] p ∈ ps, clientTok γ p.1 p.2) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z clients ∧ hs.length = sint.nat j ∧
          ClientsOk (sint.nat ops) hs ps⌝ ∗
        "#Hio" ∷ opsIoOk S hs.flatten : IProp GF) $$ [i operations Hnil Hocap h Hres Htoks0]
    · iexists W64 0, slice.nil, [], [], zero_val GoSlice
      simp only [List.flatten_nil]
      iframe
      unfold named opsIoOk
      isplitr
      · iexact Hnil
      isplitr
      · iexact Hocap
      isplitr
      · ipureintro
        exact ⟨by decide, by word, rfl, ClientsOk.nil _⟩
      iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro
    wp_for HJ
    wp_if_destruct
    · have Hlt : sint.Z j < sint.Z hsl.len := by simpa using Hif
      have hjn : sint.nat j < sint.nat clients := by
        have := Hhl.1
        simp only [List.length_replicate] at this
        word
      rw [ite_eq_left ⟨Hj.1, Hlt⟩]
      rw [show sint.nat clients - sint.nat j = (sint.nat clients - (sint.nat j + 1)) + 1 by omega,
        List.range'_succ]
      icases BigSepL.bigSepL_cons.1 $$ Hres with ⟨Hc, Hres⟩
      iunfold clientDone at Hc
      icases Hc with ⟨%sl, %hc, %Lc, %lr, %cid, Hcell, Hsl, Htok, %Hok, #Hio'⟩
      have hjj : ((sint.nat j : Nat) : Int) = sint.Z j := by word
      ihave Hcell : (typedPointsto (sliceIndexRef GoSlice (sint.Z j) hsl) sl (DFrac.own 1) :
          IProp GF) $$ [Hcell]
      · rw [← hjj]; iexact Hcell
      wp_auto
      wp_apply wp_slice_append $$ [$Hops $Hocap $Hsl] as %osl' ⟨Hops, Hocap, -⟩
      wp_for_post
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have hlen : hs.length = sint.nat j := Hj.2.2.1
      iframe
      iexists (j + W64 1), osl', hs ++ [hc], ps ++ [(hs.length, (Lc, lr))], sl
      rw [hj1, List.flatten_append, List.flatten_singleton]
      iframe
      isplitl [Htok]
      · iapply BigSepL.bigSepL_singleton.2
        rw [hlen]
        iexact Htok
      isplitr
      · ipureintro
        exact ⟨by word, by word, by simp [hlen], Hj.2.2.2.snoc cid hc Lc lr Hok.1 Hok.2⟩
      unfold opsIoOk
      iapply BigSepL.bigSepL_append.2
      iframe #
    · have Hge : ¬ sint.Z j < sint.Z hsl.len := by simpa using Hif
      have hjn : sint.nat j = sint.nat clients := by
        have := Hhl.1
        simp only [List.length_replicate] at this
        word
      iapply fupd_wp
      iinv Hinv with Hi Hclose
      imod lc_fupd_elim_later $$ Hlc2 Hi with Hi
      icases Hi with ⟨%s, %t, %L, %Ls, Hlib, Hcv, Hauth, %Hok⟩
      ihave %Hlook := toks_lookup γ 1 Ls ps $$ Hauth Htoks
      imod Hclose $$ [Hlib Hcv Hauth] with -
      · inext
        iexists s, t, L, Ls
        iframe
        ipureintro
        exact Hok
      imodintro
      have Hhn : hs.length = sint.nat clients := by rw [Hj.2.2.1, hjn]
      have Hlin := final_linearizable Hok Hj.2.2.2 Hhn Hlook
      have hn' : ((sint.nat clients : Nat) : Int) = sint.Z clients := by word
      have hm' : ((sint.nat ops : Nat) : Int) = sint.Z ops := by word
      have HhistOk := final_histOk Hj.2.2.2 Hhn
        (by simp only [Int.natCast_mul, hn', hm']; exact Hbound)
      have Hflen : (hs.flatten.length : Int) = sint.Z clients * sint.Z ops := by
        rw [final_length Hj.2.2.2 Hhn]; push_cast; rw [hn', hm']
      imod ownSlice_persist osl _ _ $$ Hops with #Hops
      wp_apply wp_CheckOperationsVerbose σ S m osl hs.flatten DFrac.discard dur $$ [$Hops]
        as %r %info ⟨%Hr, Hli⟩
      · iframe #; ipureintro; exact HhistOk
      have Hres := checkResult_complete Hr Hlin
      have Hpost : r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok") := by
        rcases Hres with rfl | ⟨rfl, Hd⟩
        · exact ⟨by decide, fun _ => rfl⟩
        · exact ⟨by decide, fun h => absurd Hd (by omega)⟩
      wp_if_destruct
      · ihave Hli := Hli $$ %trivial
        iunfold linInfoOk at Hli
        icases Hli with ⟨%psls, #Hpsls, %Hpsl, Hparts⟩
        obtain ⟨psl, rfl⟩ : ∃ psl, psls = [psl] := by
          cases psls with
          | nil => simp at Hpsl
          | cons a t => cases t with
            | nil => exact ⟨a, rfl⟩
            | cons b t => simp at Hpsl
        icases BigSepL.bigSepL_cons.1 $$ Hparts with ⟨Hpart, -⟩
        iunfold partLins at Hpart
        icases Hpart with ⟨%lsls, #Hlsls, %Hne, #Hlins⟩
        simp only [List.getD_cons_zero] at Hne ⊢
        ihave %Hpl1 := ownSlice_len _ _ _ $$ Hpsls
        ihave %Hll := ownSlice_len _ _ _ $$ Hlsls
        wp_apply wp_PartialLinearizations info_ptr (DFrac.own 1) info $$ [info] as info
        · iframe
        have hl1 : info.partialLinearizations'.len = W64 1 := by
          have := Hpl1.1; simp at this; word
        simp only [hl1, decide_true, Bool.not_true]
        wp_auto
        have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z info.partialLinearizations'.len := by
          rw [hl1]; decide
        simp only [hb0, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index info.partialLinearizations' (sint.Z (W64 0)) [psl]
          DFrac.discard psl (by decide) $$ [] as -
        · iframe #; ipureintro; rfl
        wp_if_destruct
        · -- no linearization: the history is empty
          have hl0 : lsls = [] := by
            apply List.eq_nil_of_length_eq_zero; rw [Hll.1, Hif]; rfl
          have hh0 : hs.flatten = [] := by
            cases hfl : hs.flatten with
            | nil => rfl
            | cons a t => exact absurd hl0 (Hne (by simp [histOf, hfl]))
          iapply HΦ
          isplitr
          · ipureintro; exact Hpost
          iintro -
          iexists []
          isplitr
          · iapply ownSlice_nil
          isplitr
          · unfold opsIoOk; iapply BigSepL.bigSepL_nil.2; iempintro
          ipureintro
          refine ⟨?_, isLinearization_nil S.M⟩
          rw [← Hflen, hh0]
        · obtain ⟨lsl0, lrest, rfl⟩ : ∃ a t, lsls = a :: t := by
            cases lsls with
            | nil => exfalso; apply Hif; have := Hll.1; simp at this; word
            | cons a t => exact ⟨a, t, rfl⟩
          icases BigSepL.bigSepL_cons.1 $$ Hlins with ⟨Hlin0, -⟩
          iunfold linSlice at Hlin0
          icases Hlin0 with ⟨%xs, #Hxs, %Hxl⟩
          obtain ⟨hval, hlen, hlin⟩ := isLinearization_order Hxl.1 Hxl.2
          have hb1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z psl.len := by
            have := Hll.1; have := Hll.2; simp at this ⊢; word
          simp only [hb0, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index info.partialLinearizations' (sint.Z (W64 0)) [psl]
            DFrac.discard psl (by decide) $$ [] as -
          · iframe #; ipureintro; rfl
          simp only [hb1, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index psl (sint.Z (W64 0)) (lsl0 :: lrest)
            DFrac.discard lsl0 (by decide) $$ [] as -
          · iframe #; ipureintro; rfl
          wp_apply wp_orderByLinearization osl lsl0 hs.flatten xs DFrac.discard DFrac.discard hval
            $$ [] as %rsl ⟨Hr, -, -⟩
          · iframe #
          iapply HΦ
          isplitr
          · ipureintro; exact Hpost
          iintro -
          iexists _
          iframe Hr
          isplitr
          · iapply opsIoOk_sub S hs.flatten _ (fun o ho => by
              obtain ⟨x, -, hx⟩ := List.mem_filterMap.1 ho
              exact List.mem_of_getElem? hx)
            iexact Hio
          ipureintro
          refine ⟨?_, hlin⟩
          rw [hlen, Hflen]
      · iapply HΦ
        isplitr
        · ipureintro; exact Hpost
        iintro %Hk
        exact absurd Hk Hif

end proof

end lintest
end EtcdGrove
end Perennial
