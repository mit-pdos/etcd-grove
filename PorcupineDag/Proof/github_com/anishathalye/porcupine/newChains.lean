/- Lean-first (no Rocq counterpart). Proof of
`PorcupineDag/Spec/github_com/anishathalye/porcupine/newChains.lean`.

UNFINISHED (2026-11-02): the first loop (the clients, `clientAt`, `n` the chains' sizes so far)
is proved; the rest is a `sorry`. What remains, with the lemmas already in `NewChainsLemmas.lean`:
- `firstUnks := make([]int, n*numClients)`: `n = h.length` (`chains_length_sum`), no overflow
  (`AllocOk`); cut into one piece per operation id (`ownSlice_pieces`, after
  `ownSlice_trivial_slice`).
- the second (nested) loop: each client's `j`-th `clientOperation` (its `id` is the chain's
  `j`-th, `CoFresh`) gets the piece of its id, taken from a big separating conjunction over the
  ids not yet handed out (a `Nodup` list; ids are distinct by `ChainsOk`); the struct store needs
  `iStructNamed` (field access through `Access` fails on slice elements).
- `ch := chains{...}`, at the state `heads = replicate nc 0`, `nDeps` zero, `frontier = []`,
  nothing visited (`CoFresh`'s `visited = false`), `fu` all zeros: `chainsOwnCl`.
- the third loop: `computeFirstUnk(i)` (its premise on the previous operation is vacuous at
  head 0), then `nDeps` counted by the inner loop (`deps_init`, `count_succ`; `op` is a copy of
  the first `clientOperation`, its `firstUnk` holds `FUe … 0` by `FuOk`).
- the fourth loop: `addToFrontier(i)` for the clients with operations and `nDeps = 0`
  (`init_unrelated` for its premise; `cs.length < 2^62` from `AllocOk`); then
  `chainsInv_init`.
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.newChains
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__computeFirstUnk
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__addToFrontier
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.NewChainsLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

set_option maxHeartbeats 4000000 in
theorem newChains.wp_proof
    (wp_computeFirstUnk : chains.computeFirstUnk.spec (GF := GF) (hG := hG))
    (wp_addToFrontier : chains.addToFrontier.spec (GF := GF) (hG := hG)) :
    newChains.spec (GF := GF) (hG := hG) := by
  intro ohsl h cs cons hok hwf halloc
  wp_start as ⟨Hoh, #Hlin⟩
  iunfold ohistOwn at Hoh
  icases Hoh with ⟨%sls, Hsls, %Hslslen, Hcls⟩
  ihave %Hslen := ownSlice_len $$ Hsls
  wp_auto
  wp_apply +noauto (wp_slice_make2 (V := client) ohsl.len)
  · ipureintro; exact Hslen.2
  iintro %clsl ⟨Hcl, Hclcap⟩
  wp_auto
  revert i_ptr
  intro icnt_ptr
  irename : (i_ptr ↦ zero_val w64 : IProp GF) => ikey
  have hnc : sint.nat ohsl.len = cs.length := by rw [← Hslslen, Hslen.1]
  have hncZ : sint.Z ohsl.len = (cs.length : Int) := by
    rw [← hnc]; exact (Int.toNat_of_nonneg Hslen.2).symm
  -- the clients
  ihave IH1 : iprop(∃ (k nv kv : w64) (cv : GoSlice),
      "i" ∷ icnt_ptr ↦ k ∗ "ikey" ∷ i_ptr ↦ kv ∗ "c" ∷ c_ptr ↦ cv ∗ "n" ∷ n_ptr ↦ nv ∗
      "Hcl" ∷ clsl ↦* ((List.range (sint.nat k)).map (clientAt sls) ++
        List.replicate (cs.length - sint.nat k) (zero_val client)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ cs.length ∧
        sint.Z nv = (((cs.take (sint.nat k)).map List.length).sum : Nat)⌝) $$ [i ikey c n Hcl]
  · iexists W64 0, W64 0, zero_val w64, zero_val GoSlice
    simp only [show sint.nat (W64 0) = 0 from rfl, List.range_zero, List.map_nil, List.nil_append,
      Nat.sub_zero, List.take_zero]
    rw [hnc]
    iframe
    ipureintro
    refine ⟨by word, by word, by simp⟩
  wp_for IH1
  ihave %Hcllen := ownSlice_len $$ Hcl
  wp_if_destruct
  · have hkn : sint.nat k < cs.length := by word
    have hbk : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z ohsl.len := ⟨Hk.1, Hif⟩
    obtain ⟨sl, hsl⟩ : ∃ sl, sls[sint.nat k]? = some sl :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    simp only [hbk, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index ohsl (sint.Z k) sls _ sl Hk.1) $$ [Hsls] as Hsls
    · iframe Hsls; ipureintro; exact hsl
    have hcllen : ((List.range (sint.nat k)).map (clientAt sls) ++
        List.replicate (cs.length - sint.nat k) (zero_val client)).length = cs.length := by
      simp only [List.length_append, List.length_map, List.length_range, List.length_replicate]
      omega
    have hbk2 : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z clsl.len := by
      refine ⟨Hk.1, ?_⟩
      have h1 := Hcllen.1
      have h2 : ((sint.nat clsl.len : Nat) : Int) = sint.Z clsl.len := Int.toNat_of_nonneg Hcllen.2
      rw [← h1, hcllen] at h2
      rw [← h2, ← hncZ]; exact Hif
    simp only [hbk2, _root_.and_self, ↓reduceIte]
    have hval : ({ id' := k, cltOps' := sl, head' := W64 0, nDeps' := 0 } : client) =
        clientAt sls (sint.nat k) := by
      unfold clientAt
      rw [List.getD_eq_getElem?_getD, hsl]
      congr 1
      word
    rw [hval]
    wp_apply (wp_store_slice_index (V := client) clsl (sint.Z k) _ (clientAt sls (sint.nat k)))
      $$ [Hcl] as Hcl
    · iframe Hcl; ipureintro; exact ⟨Hk.1, by omega⟩
    rw [show (sint.Z k).toNat = sint.nat k from rfl, set_prefix_replicate _ _ hkn]
    icases (BigSepL.bigSepL_lookup_acc (PROP := IProp GF)
      (Φ := fun c sl => iprop(∃ cos, sl ↦* cos ∗ ⌜CoFresh h (chain cs c) cos⌝)) hsl).1 $$ Hcls
      with ⟨Hc, Hcls⟩
    icases Hc with ⟨%cos, Hcos, %Hcof⟩
    ihave %Hcoslen := ownSlice_len $$ Hcos
    ihave Hcls := Hcls $$ %sl [Hcos]
    · iexists cos; iframe; ipureintro; exact Hcof
    rw [list_set_lookup_self _ _ _ hsl]
    have hsum := sum_take_le cs (sint.nat k + 1)
    have htot := chains_length_sum hok
    have hsucc := sum_take_succ cs hkn
    have hlenk : sint.Z sl.len = ((chain cs (sint.nat k)).length : Int) := by
      rw [← Hcof.1, Hcoslen.1]; exact (Int.toNat_of_nonneg Hcoslen.2).symm
    wp_for_post
    iframe
    iexists k + W64 1, nv + sl.len, k, sl
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [hk1]
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    have h60 := hwf.1
    have : sint.Z (nv + sl.len) = sint.Z nv + sint.Z sl.len := by word
    rw [this, Hk.2.2, hlenk, hsucc]
    omega
  · have hkc : sint.nat k = cs.length := by word
    have htot := chains_length_sum hok
    have hnv : sint.Z nv = (h.length : Int) := by
      rw [Hk.2.2, hkc, List.take_length, htot]
    rw [hkc, Nat.sub_self, List.replicate_zero, List.append_nil]
    have h60 := hwf.1
    have hal := halloc
    unfold AllocOk maxAllocBytes at hal
    have hmx : (cs.length : Int) * (h.length : Int) ≤
        (cs.length : Int) * ((max h.length 6 : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hnn : ((h.length * cs.length : Nat) : Int) ≤ 2 ^ 45 := by
      push_cast
      rw [Int.mul_comm]
      generalize (cs.length : Int) * (h.length : Int) = A at *
      generalize (cs.length : Int) * ((max h.length 6 : Nat) : Int) = B at *
      omega
    have hprod : sint.Z (nv * ohsl.len) = ((h.length * cs.length : Nat) : Int) := by
      have : sint.Z nv * sint.Z ohsl.len = ((h.length * cs.length : Nat) : Int) := by
        rw [hnv, hncZ]; push_cast; rfl
      word
    wp_apply +noauto (wp_slice_make2 (V := w64) (nv * ohsl.len))
    · ipureintro; omega
    iintro %fsl ⟨Hfu, Hfucap⟩
    wp_auto
    ihave %Hfulen := ownSlice_len $$ Hfu
    have hnn' : sint.nat (nv * ohsl.len) = h.length * cs.length := by
      have : sint.nat (nv * ohsl.len) = (sint.Z (nv * ohsl.len)).toNat := rfl
      rw [this, hprod]; rfl
    rw [hnn', show (zero_val w64 : w64) = W64 0 from rfl] at *
    have hfsllen : fsl.len = W64 ((h.length * cs.length : Nat) : Int) := by
      rw [List.length_replicate] at Hfulen
      have := Hfulen.1; have := Hfulen.2; word
    icases (ownSlice_trivial_slice fsl _ _).1 $$ Hfu with Hfu
    rw [hfsllen]
    ihave Hfu := ownSlice_pieces fsl cs.length h.length (by omega) $$ Hfu
    ihave Hcls := pend_init hok sls Hslslen fsl (sint.nat (W64 0)) rfl $$ [Hcls Hfu]
    · iframe
    -- the pieces handed out
    ihave IH2 : iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ cs.length⌝ ∗
        "Hcls" ∷ [∗list] c ↦ sl ∈ sls, if c < sint.nat iv then coDone (GF := GF) h cs c sl
          else coPend h cs fsl c sl) $$ [i Hcls]
    · iexists W64 0
      iframe
      ipureintro; exact ⟨by word, by word⟩
    wp_for IH2
    wp_if_destruct
    · have hin : sint.nat iv < cs.length := by word
      obtain ⟨sl, hsl⟩ : ∃ sl, sls[sint.nat iv]? = some sl :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hcvi : (List.map (clientAt sls) (List.range cs.length))[(sint.Z iv).toNat]? =
          some (clientAt sls (sint.nat iv)) := by
        rw [show (sint.Z iv).toNat = sint.nat iv from rfl, List.getElem?_map,
          List.getElem?_range hin]; rfl
      have hclsl : sint.Z clsl.len = (cs.length : Int) := by
        have h1 := Hcllen.1
        have h2 : ((sint.nat clsl.len : Nat) : Int) = sint.Z clsl.len := Int.toNat_of_nonneg Hcllen.2
        rw [← h1] at h2
        simp only [List.length_append, List.length_map, List.length_range, hkc, Nat.sub_self,
          List.length_replicate, Nat.add_zero] at h2
        omega
      have hbi : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z clsl.len := ⟨Hi.1, by omega⟩
      icases bigSepL_if_take sls (sint.nat iv) sl hsl (fun c sl => coDone (GF := GF) h cs c sl) (fun c sl => coPend h cs fsl c sl) $$ Hcls with ⟨Hc, Hcls⟩
      iunfold coPend at Hc
      icases Hc with ⟨%cos, Hsl, %Hcof, Hpend⟩
      icases ownSlice_elem_acc (sint.Z iv) _ clsl _ _ Hi.1 hcvi $$ Hcl with ⟨Hcv, Hcl⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hcv with ⟨Hcv, %Hcvnn⟩
      iStructNamedSuffix Hcv "_cc"
      have hcltops : (clientAt sls (sint.nat iv)).cltOps' = sl := by
        unfold clientAt; simp only [List.getD_eq_getElem?_getD, hsl, Option.getD_some]
      rw [hcltops]
      ihave %Hcoslen := ownSlice_len $$ Hsl
      have hlenZ : sint.Z sl.len = ((chain cs (sint.nat iv)).length : Int) := by
        rw [← Hcof.1, Hcoslen.1]; exact (Int.toNat_of_nonneg Hcoslen.2).symm
      ihave IH3 : iprop(∃ (jv : w64) (cosj : List clientOperation), "j" ∷ j_ptr ↦ jv ∗
          "Hsl" ∷ sl ↦* cosj ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z jv ∧ sint.Z jv ≤ (chain cs (sint.nat iv)).length ∧
            CoFresh h (chain cs (sint.nat iv)) cosj⌝ ∗
          "Hdone" ∷ ([∗list] k ↦ co ∈ cosj.take (sint.nat jv),
            co.firstUnk' ↦* List.replicate cs.length (W64 0)) ∗
          "Hpend" ∷ [∗list] y ∈ (chain cs (sint.nat iv)).drop (sint.nat jv),
            fuPiece (GF := GF) fsl cs.length y) $$ [j Hsl Hpend]
      · iexists W64 0, cos
        simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
        iframe
        isplitr
        · ipureintro; exact ⟨by word, by word, Hcof⟩
        exact BigSepL.bigSepL_nil_intro
      wp_for IH3
      nc_idx [hbi]
      cleanup_bool_decide
      wp_if_destruct
      · have hjn : sint.nat jv = (sint.Z jv).toNat := rfl
        have hjl : sint.nat jv < (chain cs (sint.nat iv)).length := by omega
        have hj1 : sint.nat (jv + W64 1) = sint.nat jv + 1 := by
          have : (((chain cs (sint.nat iv)).length : Nat) : Int) < 2 ^ 60 := by
            have := chain_length_le' hok (sint.nat iv); omega
          word
        obtain ⟨co, hco⟩ : ∃ co, cosj[(sint.Z jv).toNat]? = some co :=
          ⟨_, List.getElem?_eq_getElem (by rw [Hj.2.2.1]; exact hjl)⟩
        obtain ⟨y, o, hy, hyo, hid, -⟩ := Hj.2.2.2 _ co hco
        have hbj : 0 ≤ sint.Z jv ∧ sint.Z jv < sint.Z sl.len := ⟨Hj.1, Hif⟩
        icases ownSlice_elem_acc (sint.Z jv) co sl _ cosj Hj.1 hco $$ Hsl with ⟨Hco, Hsl⟩
        icases typedPointsto_not_null_dup _ _ _ $$ Hco with ⟨Hco, %Hconn⟩
        iStructNamedSuffix Hco "_co"
        nc_idx [hbi, hbj]
        ihave %Hfucw := ownSliceCap_wf _ _ $$ Hfucap
        have hyh : y < h.length := (List.getElem?_eq_some_iff.mp hyo).1
        have hyle : (y + 1) * cs.length ≤ h.length * cs.length := Nat.mul_le_mul_right _ hyh
        have hlo : sint.Z (co.id' * ohsl.len) = ((y * cs.length : Nat) : Int) := by
          have : sint.Z co.id' * sint.Z ohsl.len = ((y * cs.length : Nat) : Int) := by
            rw [hid, hncZ]; push_cast; rfl
          have : ((y * cs.length : Nat) : Int) ≤ ((h.length * cs.length : Nat) : Int) := by
            have := Nat.mul_le_mul_right cs.length (Nat.le_of_lt hyh); omega
          word
        have hhi : sint.Z ((co.id' + W64 1) * ohsl.len) = (((y + 1) * cs.length : Nat) : Int) := by
          have h1 : sint.Z (co.id' + W64 1) = ((y + 1 : Nat) : Int) := by
            have : (y : Int) < 2 ^ 60 := by omega
            push_cast; word
          have : sint.Z (co.id' + W64 1) * sint.Z ohsl.len = (((y + 1) * cs.length : Nat) : Int) := by
            rw [h1, hncZ]; push_cast; rfl
          have : (((y + 1) * cs.length : Nat) : Int) ≤ ((h.length * cs.length : Nat) : Int) := by
            omega
          word
        have hcapb : sint.Z fsl.len = ((h.length * cs.length : Nat) : Int) := by
          rw [hfsllen]; word
        have hsb : 0 ≤ sint.Z (co.id' * ohsl.len) ∧
            sint.Z (co.id' * ohsl.len) ≤ sint.Z ((co.id' + W64 1) * ohsl.len) ∧
            sint.Z ((co.id' + W64 1) * ohsl.len) ≤ sint.Z fsl.cap := by
          rw [hlo, hhi]
          have : y * cs.length ≤ (y + 1) * cs.length := Nat.mul_le_mul_right _ (Nat.le_succ y)
          omega
        nc_idx [hsb, hbi, hbj]
        have hh63 : (((y + 1) * cs.length : Nat) : Int) < 2 ^ 63 := by omega
        have hl63 : ((y * cs.length : Nat) : Int) < 2 ^ 63 := by
          have : y * cs.length ≤ (y + 1) * cs.length := Nat.mul_le_mul_right _ (Nat.le_succ y)
          omega
        rw [w64_eq_of_sint hlo hl63, w64_eq_of_sint hhi hh63]
        obtain ⟨sp, hsp⟩ : ∃ sp, sp = slice.slice fsl w64 (W64 ((y * cs.length : Nat) : Int))
            (W64 (((y + 1) * cs.length : Nat) : Int)) := ⟨_, rfl⟩
        rw [← hsp]
        ihave Hco := typedPointsto_combine _ { co with firstUnk' := sp } _ Hconn $$
          [Op_co globalId_co id_co firstUnk_co visited_co __co]
        · simp only [TypedPointsto.typedPointstoDef]; iframe
        ihave Hsl := Hsl $$ %_ Hco
        have hjc : sint.nat jv < cosj.length := by rw [Hj.2.2.1]; exact hjl
        have hyj : (chain cs (sint.nat iv))[sint.nat jv]'hjl = y := by
          have := hy; rw [hjn.symm, List.getElem?_eq_getElem hjl] at this; exact Option.some.inj this
        rw [List.drop_eq_getElem_cons hjl, hyj]
        clear hyj
        icases Hpend with ⟨Hp, Hpend⟩
        wp_for_post
        iframe
        iexists jv + W64 1, cosj.set (sint.nat jv) { co with firstUnk' := sp }
        rw [hj1, take_set_succ hjc]
        iframe
        isplitr
        · ipureintro
          refine ⟨by word, by word, coFresh_set_fu Hj.2.2 hco _⟩
        iapply BigSepL.bigSepL_singleton.2
        unfold fuPiece
        rw [hsp]
        iexact Hp
      · have hjn : sint.nat jv = (chain cs (sint.nat iv)).length := by
          have : sint.nat jv = (sint.Z jv).toNat := rfl
          omega
        rw [hjn, List.drop_length, ← Hj.2.2.1, List.take_length]
        ihave Hcv := typedPointsto_combine _ (clientAt sls (sint.nat iv)) _ Hcvnn $$
          [id_cc cltOps_cc head_cc nDeps_cc __cc]
        · simp only [TypedPointsto.typedPointstoDef]; rw [hcltops]; iframe
        ihave Hcl := Hcl $$ %_ Hcv
        rw [list_set_lookup_self _ _ _ hcvi]
        ihave Hcls := bigSepL_if_step sls (sint.nat iv) sl hsl
          (fun c sl => coDone (GF := GF) h cs c sl) (fun c sl => coPend h cs fsl c sl) $$ [Hcls Hsl Hdone]
        · iframe
          unfold coDone
          iexists cosj
          iframe
          ipureintro; exact Hj.2.2
        wp_for_post
        iframe
        iexists iv + W64 1
        have hi1 : sint.nat (iv + W64 1) = sint.nat iv + 1 := by word
        rw [hi1]
        iframe
        ipureintro
        exact ⟨by word, by word⟩
    have hz0 : sint.Z (W64 0) = 0 := rfl
    have hivc : sint.nat iv = cs.length := by have : sint.nat iv = (sint.Z iv).toNat := rfl; omega
    rw [hivc]
    wp_apply +noauto (wp_slice_make3 (V := w64) (W64 0) ohsl.len ⟨by rw [hz0]; omega, by rw [hz0]; omega⟩)
    iintro %frsl ⟨Hfr, Hfrcap, %Hfrc⟩
    wp_auto
    simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
    have hnc62 : (cs.length : Int) < 2 ^ 62 := by
      have h6 : (cs.length : Int) * 6 ≤ (cs.length : Int) * ((max h.length 6 : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      generalize (cs.length : Int) * ((max h.length 6 : Nat) : Int) = B at *
      omega
    ihave Hch : chainsOwnCl (GF := GF) ch_ptr clsl h cs (chStInit cs) $$ [ch Hcl Hfr Hfrcap Hcls]
    · unfold chainsOwnCl chainsRepr
      iexists _
      iframe ch
      isplitr
      · ipureintro; rfl
      iexists (List.range cs.length).map (clientAt sls)
      iframe Hcl Hfrcap
      isplitr
      · ipureintro; exact ⟨by simp, hnv⟩
      isplitl [Hfr]
      · simp only [chStInit, List.map_nil]; iexact Hfr
      iapply (bigSepL_transfer sls _ (by simp [Hslslen]) ?_) $$ Hcls
      intro c sl cv hsl hcv
      have hc : c < cs.length := by rw [← Hslslen]; exact (List.getElem?_eq_some_iff.mp hsl).1
      rw [List.getElem?_map, List.getElem?_range hc] at hcv
      cases hcv
      simp only [hc, ↓reduceIte]
      exact clientOwn_init sls c sl hsl (by omega)
    have hclsl : sint.Z clsl.len = (cs.length : Int) := by
      have h1 := Hcllen.1
      have h2 : ((sint.nat clsl.len : Nat) : Int) = sint.Z clsl.len := Int.toNat_of_nonneg Hcllen.2
      rw [← h1] at h2
      simp only [List.length_append, List.length_map, List.length_range, hkc, Nat.sub_self,
        List.length_replicate, Nat.add_zero] at h2
      omega
    -- the first operations' `firstUnk` and the `nDeps`
    ihave IH4 : iprop(∃ (iv : w64) (st : ChSt), "i" ∷ i_ptr ↦ iv ∗
        "Hch" ∷ chainsOwnCl ch_ptr clsl h cs st ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ cs.length ∧ NcInv h cs (sint.nat iv) st⌝) $$ [i Hch]
    · iexists W64 0, chStInit cs
      iframe
      ipureintro; exact ⟨by rw [hz0]; omega, by rw [hz0]; omega, ncInv_init h cs⟩
    wp_for IH4
    wp_if_destruct
    · have hin : sint.nat iv < cs.length := by have : sint.nat iv = (sint.Z iv).toNat := rfl; omega
      have hbi : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z clsl.len := ⟨Hi.1, by omega⟩
      obtain ⟨hI1, hI2, hI3, hI4, hI5, hI6⟩ := Hi.2.2
      wp_apply +noauto (wp_computeFirstUnk ch_ptr clsl h cs st iv cons hok hwf hI3 hI4
        (by rw [hI1]; exact headsOk_nil) Hi.1 hin
        (fun hp => absurd hp (by rw [ncInv_head Hi.2.2]; omega))) $$ [Hch]
      · iframe; iframe #
      iintro ⟨%st1, Hch, %Hst1⟩
      wp_auto
      icases chains_open ch_ptr clsl h cs st1 (sint.Z iv) Hi.1 hin $$ Hch with
        ⟨%chV, %cvs, %cv, %Hfacts, Hchp, Hfr, Hcap, Hcv, Hw, Hrest, Hc⟩
      obtain ⟨Hchcl, Hcvslen, Hnum, Hcvi⟩ := Hfacts
      iunfold clientOwn at Hc
      icases Hc with ⟨%Hcf, %cos, Hcos, %Hcoo, Hfus⟩
      ihave %Hcoslen := ownSlice_len $$ Hcos
      icases typedPointsto_not_null_dup _ _ _ $$ Hchp with ⟨Hchp, %Hchnn⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hcv with ⟨Hcv, %Hcvnn⟩
      iStructNamedSuffix Hchp "_ch"
      iStructNamedSuffix Hcv "_cc"
      rw [Hchcl]
      wp_auto
      nc_idx [hbi]
      have hcol : sint.Z cv.cltOps'.len = ((chain cs (sint.nat iv)).length : Int) := by
        rw [← Hcoo.1, Hcoslen.1]; exact (Int.toNat_of_nonneg Hcoslen.2).symm
      have hndl : (sint.Z iv).toNat < st1.nDeps.length := by
        rw [Hst1.2.2.2.1.2.1]; exact hin
      wp_if_destruct
      · have hl : 0 < (chain cs (sint.nat iv)).length := by
          have : 0 < sint.Z cv.cltOps'.len := by simpa using Hif
          omega
        have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z cv.cltOps'.len := by
          refine ⟨by decide, ?_⟩; simpa using Hif
        obtain ⟨co0, hco0⟩ : ∃ co, cos[(sint.Z (W64 0)).toNat]? = some co :=
          ⟨_, List.getElem?_eq_getElem (by rw [Hcoo.1]; exact hl)⟩
        nc_idx [hbi, hb0]
        simp only [eq_true hb0, ↓reduceIte]
        wp_apply (wp_load_slice_index cv.cltOps' (sint.Z (W64 0)) cos _ co0 hb0.1) $$ [Hcos] as Hcos
        · iframe Hcos; ipureintro; exact hco0
        have hco0' : cos[0]? = some co0 := hco0
        icases (BigSepL.bigSepL_lookup_acc (PROP := IProp GF)
          (Φ := fun k (co : clientOperation) => co.firstUnk' ↦* st1.fuAt (sint.Z iv).toNat k) hco0').1
          $$ Hfus with ⟨Hfl, Hfus⟩
        ihave %Hfllen := ownSlice_len $$ Hfl
        have hfl0 : (st1.fuAt (sint.nat iv) 0).length = cs.length :=
          (Hst1.2.2.2.1.2.2.2.2 _ _ hl).2.2
        have hvis0 : st1.visAt (sint.nat iv) 0 = true := by
          rw [Hst1.2.2.2.2.2]; simp [ncInv_head Hi.2.2, hl]
        have hfue : ∀ d, d < cs.length → d ≠ sint.nat iv →
            sint.Z ((st1.fuAt (sint.nat iv) 0).getD d 0) = FUe h cs (sint.nat iv) d 0 :=
          fun d h1 h2 => Hst1.2.2.2.2.1 _ _ hvis0 d h1 h2
        iStructNamedSuffix op "_op"
        ihave IH5 : iprop(∃ (jv ndv : w64), "j" ∷ j_ptr ↦ jv ∗
            "nDeps_cc" ∷ (sliceIndexRef client (sint.Z iv) clsl).[client, go!"nDeps"] ↦ ndv ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z jv ∧ sint.Z jv ≤ cs.length ∧
              sint.Z ndv = (((List.range (sint.nat jv)).filter (fun d =>
                decide (d ≠ sint.nat iv ∧ 0 < FUe h cs (sint.nat iv) d 0))).length : Int)⌝)
          $$ [j nDeps_cc]
        · iexists W64 0, W64 0
          iframe
          ipureintro; exact ⟨by rw [hz0]; omega, by rw [hz0]; omega, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl⟩
        wp_for IH5
        wp_if_destruct
        · have hjn : sint.nat jv < cs.length := by
            have : sint.nat jv = (sint.Z jv).toNat := rfl
            omega
          have hj1 := sint_add_one (a := jv) Hj.1 (by omega)
          have hcnt := count_succ
            (fun d => decide (d ≠ sint.nat iv ∧ 0 < FUe h cs (sint.nat iv) d 0)) (sint.nat jv)
          have hle := List.length_filter_le
            (fun d => decide (d ≠ sint.nat iv ∧ 0 < FUe h cs (sint.nat iv) d 0))
            (List.range (sint.nat jv))
          rw [List.length_range] at hle
          wp_if_destruct
          · -- `j = i`: skipped
            wp_for_post
            iframe
            iexists jv + W64 1, ndv
            rw [hj1.2]
            iframe
            ipureintro
            refine ⟨by omega, by omega, ?_⟩
            rw [hcnt, Hj.2.2]
            subst Hif
            simp
          · have hji : sint.nat jv ≠ sint.nat iv := fun e => Hif (sint_nat_inj Hj.1 Hi.1 e)
            have hbj : 0 ≤ sint.Z jv ∧ sint.Z jv < sint.Z co0.firstUnk'.len := by
              refine ⟨Hj.1, ?_⟩
              have h1 := Hfllen.1; have h2 := Hfllen.2
              have : sint.nat jv = (sint.Z jv).toNat := rfl
              have : sint.nat co0.firstUnk'.len = (sint.Z co0.firstUnk'.len).toNat := rfl
              rw [show (sint.Z iv).toNat = sint.nat iv from rfl, hfl0] at h1
              omega
            simp only [hbj, _root_.and_self, ↓reduceIte]
            have hx : (st1.fuAt (sint.Z iv).toNat 0)[(sint.Z jv).toNat]? =
                some ((st1.fuAt (sint.nat iv) 0).getD (sint.nat jv) 0) := by
              rw [List.getD_eq_getElem?_getD, show (sint.Z jv).toNat = sint.nat jv from rfl,
                List.getElem?_eq_getElem (by rw [show (sint.Z iv).toNat = sint.nat iv from rfl, hfl0]; exact hjn)]
              rfl
            wp_apply (wp_load_slice_index co0.firstUnk' (sint.Z jv) _ _ _ Hj.1) $$ [Hfl] as Hfl
            · iframe Hfl; ipureintro; exact hx
            have hv := hfue (sint.nat jv) hjn hji
            have hz : sint.Z (W64 0) = 0 := rfl
            wp_if_destruct
            · -- a dependency: `nDeps++`
              have hpos : 0 < FUe h cs (sint.nat iv) (sint.nat jv) 0 := by omega
              have hnd1 := sint_add_one (a := ndv) (by omega) (by omega)
              nc_idx [hbi]
              wp_for_post
              iframe
              iexists jv + W64 1, ndv + W64 1
              rw [hj1.2]
              iframe
              ipureintro
              refine ⟨by omega, by omega, ?_⟩
              rw [hcnt, hnd1.1, Hj.2.2]
              simp [hji, hpos]
            · have hnpos : ¬ 0 < FUe h cs (sint.nat iv) (sint.nat jv) 0 := by omega
              wp_for_post
              iframe
              iexists jv + W64 1, ndv
              rw [hj1.2]
              iframe
              ipureintro
              refine ⟨by omega, by omega, ?_⟩
              rw [hcnt, Hj.2.2]
              simp [hnpos]
        · -- every client looked at: `nDeps[i]` is the count
          have hjc : sint.nat jv = cs.length := by
            have : sint.nat jv = (sint.Z jv).toNat := rfl
            omega
          have hndv : sint.Z ndv = (deps h cs (List.replicate cs.length 0) (sint.nat iv) : Int) := by
            rw [Hj.2.2, hjc, deps_init hl]
          ihave Hfus := Hfus $$ %co0 Hfl
          rw [list_set_lookup_self _ _ _ hco0']
          ihave Hcv := typedPointsto_combine _ { cv with nDeps' := ndv } _ Hcvnn $$
            [id_cc cltOps_cc head_cc nDeps_cc __cc]
          · simp only [TypedPointsto.typedPointstoDef]; iframe
          ihave Hchp := typedPointsto_combine _ chV _ Hchnn $$ [clients_ch numOps_ch frontier_ch __ch]
          · simp only [TypedPointsto.typedPointstoDef]; rw [Hchcl]; iframe
          ihave Hc : clientOwn h cs { st1 with nDeps := st1.nDeps.set (sint.Z iv).toNat ndv }
              (sint.Z iv).toNat { cv with nDeps' := ndv } $$ [Hcos Hfus]
          · unfold clientOwn
            isplitr
            · ipureintro
              exact ⟨Hcf.1, Hcf.2.1, by simp only; rw [List.getD_eq_getElem?_getD,
                List.getElem?_set_self hndl]; rfl⟩
            iexists cos
            iframe
            ipureintro; exact Hcoo
          ihave Hch := chains_close ch_ptr chV clsl h cs st1
            { st1 with nDeps := st1.nDeps.set (sint.Z iv).toNat ndv } cvs (sint.Z iv)
            { cv with nDeps' := ndv } Hchcl ⟨Hcvslen, Hnum⟩ (by omega)
            (fun k hk cv => clientOwn_nDeps_ne h cs st1 _ _ k hk cv) $$ [Hchp Hfr Hcap Hcv Hw Hrest Hc]
          · iframe
          have hi1 := sint_add_one (a := iv) Hi.1 (by omega)
          wp_for_post
          iframe
          iexists iv + W64 1, { st1 with nDeps := st1.nDeps.set (sint.Z iv).toNat ndv }
          rw [hi1.2]
          iframe
          ipureintro
          exact ⟨by omega, by omega, ncInv_step Hi.2.2 hin Hst1 _ (fun _ => hndv)⟩
      · -- no operations: `nDeps` stays `0`
        have hl0 : (chain cs (sint.nat iv)).length = 0 := by
          have : ¬ (0 < sint.Z cv.cltOps'.len) := by simpa using Hif
          omega
        ihave Hcv := typedPointsto_combine _ { cv with nDeps' := W64 0 } _ Hcvnn $$
          [id_cc cltOps_cc head_cc nDeps_cc __cc]
        · simp only [TypedPointsto.typedPointstoDef]; iframe
        ihave Hchp := typedPointsto_combine _ chV _ Hchnn $$ [clients_ch numOps_ch frontier_ch __ch]
        · simp only [TypedPointsto.typedPointstoDef]; rw [Hchcl]; iframe
        ihave Hc : clientOwn h cs { st1 with nDeps := st1.nDeps.set (sint.Z iv).toNat (W64 0) }
            (sint.Z iv).toNat { cv with nDeps' := W64 0 } $$ [Hcos Hfus]
        · unfold clientOwn
          isplitr
          · ipureintro
            exact ⟨Hcf.1, Hcf.2.1, by simp only; rw [List.getD_eq_getElem?_getD,
              List.getElem?_set_self hndl]; rfl⟩
          iexists cos
          iframe
          ipureintro; exact Hcoo
        ihave Hch := chains_close ch_ptr chV clsl h cs st1
          { st1 with nDeps := st1.nDeps.set (sint.Z iv).toNat (W64 0) } cvs (sint.Z iv)
          { cv with nDeps' := W64 0 } Hchcl ⟨Hcvslen, Hnum⟩ (by omega)
          (fun k hk cv => clientOwn_nDeps_ne h cs st1 _ _ k hk cv) $$ [Hchp Hfr Hcap Hcv Hw Hrest Hc]
        · iframe
        wp_for_post
        iframe
        iexists iv + W64 1, { st1 with nDeps := st1.nDeps.set (sint.Z iv).toNat (W64 0) }
        have hi1 := sint_add_one (a := iv) Hi.1 (by omega)
        rw [hi1.2]
        iframe
        ipureintro
        exact ⟨by omega, by omega, ncInv_step Hi.2.2 hin Hst1 _ (fun hp => absurd hp (by omega))⟩
    · sorry

end proof

end porcupine
end EtcdGrove
end Perennial
