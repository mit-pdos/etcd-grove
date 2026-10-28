/-
Lean-first (no Rocq counterpart).

The proof of `RunTok` (the local copy of `Run`'s spec over `applySpecTok`,
`notes/logkv-eval-rw.md`): `Run.lean`'s proof, each client forked with its thread token
(`wp_fork_tok_body`), which it passes to `runClientTok` and gives back when it exits.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.RunTok
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.runClientTok
public import Spec.github_com.anishathalye.porcupine.CheckOperationsVerbose
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Spec.sync.WaitGroup__Wait
public import Perennial.Proof.sync.WaitGroupJoin
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.RunLemmas
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvrw

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.Assumptions]

theorem RunTok.wp_proof
    (wp_runClientTok : runClientTok.spec (GF := GF) (hG := hG))
    (wp_CheckOperationsVerbose : porcupine.CheckOperationsVerbose.spec (GF := GF) (hG := hG)) :
    RunTok.spec (GF := GF) (hG := hG) :=
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
      wp_apply wp_runClientTok σ S inOk libState clockVal Eapp Eclk (sint.nat clients) γ apply gen
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
      wp_apply wp_CheckOperationsVerbose σ S m osl hs.flatten (DFrac.own 1) dur HhistOk $$ [$Hops]
        as %r %info %Hr
      · iframe #
      iapply HΦ
      ipureintro
      exact Hr Hlin

end proof

end logkvrw
end lintest
end EtcdGrove
end Perennial
