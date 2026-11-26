/-
Proof of `CallAll.spec` (at `[any, any]`). Lean-first (no Rocq counterpart); #50 N10a.

`outs` and `oks` are made of `len(addrs)` zero elements, split into their elements' points-tos
(`ownSlice_replicate_elems`). The wait group is the thread-token join at level `0`
(`sync.tokJoinL`): each `wg.Add(1)` deposits the level token, the `go` statement gives it back and
puts the goroutine's own level `0` in its slot. Goroutine `c` gets its two elements and `P c`, calls
`call(addrs[c], ins[c])`, stores the results and calls `Done` with the elements and `Q c` of the
results (`slotRes`); `Wait` gives them all back.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CallAll
public import Perennial.Proof.sync.WaitGroupTokJoinL
public import Perennial.Proof.sync.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.RunLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- The wait group's namespace. -/
def callAllN : Namespace := nroot.@"CallAll"

/-- Goroutine `c`'s result: its two elements and `Q c` of them. -/
def slotRes (outs oks : GoSlice) (Q : Nat → GoInterface → Bool → IProp GF) (c : Nat) : IProp GF :=
  iprop(∃ (o : GoInterface) (ok : Bool),
    typedPointsto (sliceIndexRef GoInterface ((c : Nat) : Int) outs) o (DFrac.own 1) ∗
    typedPointsto (sliceIndexRef Bool ((c : Nat) : Int) oks) ok (DFrac.own 1) ∗ Q c o ok)

theorem CallAll.wp_proof : CallAll.spec (GF := GF) (hG := hG) := by
  intro addrs ins aL xs call P Q Htb Hxl
  wp_start as ⟨Htok, #Has, #Hxs, HP, #Hcall⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave %Hal := ownSlice_len _ _ _ $$ Has
  ihave %Hxsl := ownSlice_len _ _ _ $$ Hxs
  obtain ⟨n, hn⟩ : ∃ n, sint.nat addrs.len = n := ⟨_, rfl⟩
  have Han : aL.length = n := Hal.1.trans hn
  have Hxn : xs.length = n := by rw [Hxl, Han]
  have hnZ : (n : Int) = sint.Z addrs.len := by rw [← hn]; have := Hal.2; word
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := GoInterface) addrs.len) as %outs ⟨Houts, -⟩
  · ipureintro; exact Hal.2
  ihave %Hol := ownSlice_len _ _ _ $$ Houts
  ihave Hco := lintest.ownSlice_replicate_elems outs (sint.nat addrs.len) (zero_val GoInterface) (DFrac.own 1) $$ Houts
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := Bool) addrs.len) as %oks ⟨Hoks, -⟩
  · ipureintro; exact Hal.2
  ihave %Hkl := ownSlice_len _ _ _ $$ Hoks
  ihave Hck := lintest.ownSlice_replicate_elems oks (sint.nat addrs.len) (zero_val Bool) (DFrac.own 1) $$ Hoks
  simp only [List.length_replicate] at Hol Hkl
  have hOl : sint.Z outs.len = (n : Int) := by
    rw [hnZ]; have h1 := Hol.1; have h2 := Hol.2; have h3 := Hal.2; word
  have hKl : sint.Z oks.len = (n : Int) := by
    rw [hnZ]; have h1 := Hkl.1; have h2 := Hkl.2; have h3 := Hal.2; word
  rw [hn]
  (try wp_auto)
  imod sync.init_WaitGroup (callAllN.@"wg") wg_ptr $$ wg with ⟨%γwg, Hwg⟩
  imod sync.tokJoinL.init callAllN 0 wg_ptr γwg ⊤ (by omega) $$ Hwg with Hwg
  ihave Hwg := sync.tokJoinL.ownAdder_wand
    iprop([∗list] c ∈ List.range (sint.nat (W64 0)), slotRes outs oks Q c)
    callAllN 0 wg_ptr 0 iprop(True) $$ [] Hwg
  · iintro _
    rw [show sint.nat (W64 0) = 0 from rfl, List.range_zero]
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  ipersist outs
  ipersist oks
  ipersist addrs
  ipersist ins
  ipersist call
  have H00 : sint.nat (W64 0) = 0 := rfl
  rw [Han]
  ihave Hco : ([∗list] c ∈ List.range' (sint.nat (W64 0)) (n - sint.nat (W64 0)),
      typedPointsto (sliceIndexRef GoInterface ((c : Nat) : Int) outs) (zero_val GoInterface)
        (DFrac.own 1) : IProp GF) $$ [Hco]
  · rw [H00, Nat.sub_zero, ← List.range_eq_range']; iexact Hco
  ihave Hck : ([∗list] c ∈ List.range' (sint.nat (W64 0)) (n - sint.nat (W64 0)),
      typedPointsto (sliceIndexRef Bool ((c : Nat) : Int) oks) (zero_val Bool)
        (DFrac.own 1) : IProp GF) $$ [Hck]
  · rw [H00, Nat.sub_zero, ← List.range_eq_range']; iexact Hck
  ihave HP : ([∗list] c ∈ List.range' (sint.nat (W64 0)) (n - sint.nat (W64 0)), P c : IProp GF)
    $$ [HP]
  · rw [H00, Nat.sub_zero, ← List.range_eq_range']; iexact HP
  ihave IH : (∃ (k : w64),
      "i" ∷ i_ptr ↦ k ∗ "Htok" ∷ levelTok 0 ∗
      "Hwg" ∷ sync.tokJoinL.ownAdder callAllN 0 wg_ptr (sint.nat k)
        ([∗list] c ∈ List.range (sint.nat k), slotRes outs oks Q c) ∗
      "Hco" ∷ ([∗list] c ∈ List.range' (sint.nat k) (n - sint.nat k),
        typedPointsto (sliceIndexRef GoInterface ((c : Nat) : Int) outs) (zero_val GoInterface)
          (DFrac.own 1)) ∗
      "Hck" ∷ ([∗list] c ∈ List.range' (sint.nat k) (n - sint.nat k),
        typedPointsto (sliceIndexRef Bool ((c : Nat) : Int) oks) (zero_val Bool) (DFrac.own 1)) ∗
      "HP" ∷ ([∗list] c ∈ List.range' (sint.nat k) (n - sint.nat k), P c) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z addrs.len⌝ : IProp GF)
    $$ [i Htok Hwg Hco Hck HP]
  · iexists W64 0
    iframe
    ipureintro
    exact ⟨by decide, Hal.2⟩
  wp_for IH
  wp_if_destruct
  · -- goroutine `k`: `wg.Add(1)`, `go func() { outs[c], oks[c] = call(addrs[c], ins[c]); wg.Done() }()`
    have Hlt : sint.Z k < sint.Z addrs.len := by simpa using Hif
    have hkn : sint.nat k < n := by rw [← hn]; word
    have hkk : ((sint.nat k : Nat) : Int) = sint.Z k := by word
    have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z addrs.len := ⟨Hk.1, Hlt⟩
    obtain ⟨a, ha⟩ : ∃ a, aL[sint.nat k]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨x, hx⟩ : ∃ x, xs[sint.nat k]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index addrs (sint.Z k) aL DFrac.discard a Hk.1) $$ [] as -
    · iframe #; ipureintro; exact ha
    (try wp_auto)
    wp_apply (sync.tokJoinL.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add
      (slotRes outs oks Q (sint.nat k)) callAllN 0 wg_ptr (sint.nat k) _) $$ [Hwg Htok]
      as ⟨Hwg, Hpend⟩
    · iframe
    rw [show n - sint.nat k = (n - (sint.nat k + 1)) + 1 by omega, List.range'_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hco with ⟨Hco1, Hco⟩
    icases BigSepL.bigSepL_cons.1 $$ Hck with ⟨Hck1, Hck⟩
    icases BigSepL.bigSepL_cons.1 $$ HP with ⟨HP1, HP⟩
    ipersist c
    wp_apply (sync.tokJoinL.wp_fork callAllN 0 wg_ptr (slotRes outs oks Q (sint.nat k)) _ _
      (fun _ _ => CoPset.mem_full)) $$ [Hpend] [Hco1 Hck1 HP1]
    · iexact Hpend
    · iintro Hdone Hrest
      (try wp_auto)
      have ho : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z outs.len := ⟨Hk.1, by rw [hOl]; omega⟩
      have hok : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z oks.len := ⟨Hk.1, by rw [hKl]; omega⟩
      have hi : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z ins.len := ⟨Hk.1, by
        have h1 := Hxsl.1; have h2 := Hxsl.2; rw [Hxn] at h1; rw [← hn] at h1 hkn; word⟩
      (try simp only [ho, hok, hb, hi, _root_.and_self, ↓reduceIte])
      (try wp_auto)
      (try simp only [ho, hok, hb, hi, _root_.and_self, ↓reduceIte])
      (try wp_auto)
      (try simp only [ho, hok, hb, hi, _root_.and_self, ↓reduceIte])
      wp_apply (wp_load_slice_index addrs (sint.Z k) aL DFrac.discard a Hk.1) $$ [] as -
      · iframe #; ipureintro; exact ha
      (try wp_auto)
      (try simp only [ho, hok, hb, hi, _root_.and_self, ↓reduceIte])
      wp_apply (wp_load_slice_index ins (sint.Z k) xs DFrac.discard x Hk.1) $$ [] as -
      · iframe #; ipureintro; exact hx
      (try wp_auto)
      ihave Hc := Hcall $$ %(sint.nat k) %a %x []
      · ipureintro; exact ⟨ha, hx⟩
      wp_apply Hc $$ [HP1] as %o %ok HQ
      · iexact HP1
      rw [hkk]
      (try wp_auto)
      wp_apply (sync.tokJoinL.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done callAllN 0 wg_ptr
        (slotRes outs oks Q (sint.nat k))) $$ [Hdone Hco1 Hck1 HQ] as Htok0
      · iframe Hdone
        unfold slotRes
        iexists o, ok
        rw [hkk]
        iframe
      ihave Htt := (threadTok_level0 (GF := GF)).2 $$ [Htok0 Hrest]
      · iframe
      iframe Htt
      try itrivial
    iintro Htok
    (try wp_auto)
    wp_for_post
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    iframe
    iexists (k + W64 1)
    rw [hk1]
    iframe
    unfold named
    isplitl [Hwg]
    · iapply sync.tokJoinL.ownAdder_wand $$ [] Hwg
      iintro ⟨H1, H2⟩
      rw [List.range_succ]
      iapply BigSepL.bigSepL_snoc.2
      iframe
    ipureintro
    exact ⟨by word, by word⟩
  · have Hkn : sint.nat k = n := by
      have : ¬ sint.Z k < sint.Z addrs.len := by simpa using Hif
      rw [← hn]; word
    rw [Hkn]
    iclear Hco Hck HP
    wp_apply (sync.tokJoinL.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait callAllN 0
      wg_ptr _ _) $$ [$Hwg] as ⟨Hres, -⟩
    (try wp_auto)
    iapply HΦ
    iframe Htok
    isplitr
    · ipureintro; try rw [Han]
      exact ⟨hOl, hKl⟩
    try rw [Han]
    unfold slotRes
    iexact Hres

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
