module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.State
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.FormatUint10
public import Perennial.Proof.encoding.binary.Results

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Indexing a string constant `tab` at an in-range index does not panic. -/
theorem string_index_some (tab : List w8) (w : w64) (h : uint.Z w < tab.length)
    (h63 : uint.Z w < 2 ^ 63) :
    ∃ b, (if 0 ≤ sint.Z w then tab[sint.nat w]? else none) = some b := by
  have e : sint.Z w = uint.Z w := by word
  have e2 : sint.nat w = (uint.Z w).toNat := by simp only [sint.nat, e]
  have h0 : 0 ≤ uint.Z w := by word
  rw [e2, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
  exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

theorem w64_and_le (u m : w64) : uint.Z (u &&& m) ≤ uint.Z m := by
  have : (u &&& m).toNat ≤ m.toNat := by
    rw [BitVec.toNat_and]; exact Nat.and_le_right
  simp only [uint.Z]; omega

theorem pow16_ge2 (n k : Nat) (h1 : 16 ≤ n) (h2 : n < 16 ^ k) : 2 ≤ k := by
  match k, h2 with
  | 0, h2 => simp at h2; omega
  | 1, h2 => simp at h2; omega
  | _ + 2, _ => omega

theorem div16_lt (n k : Nat) (hk : 1 ≤ k) (h : n < 16 ^ k) : n / 16 < 16 ^ (k - 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.pow_succ] at h
  simp only [Nat.add_sub_cancel]
  omega

theorem w8_shr4_lt (x : w8) : uint.Z (x >>> W64 4) < 16 := by
  word

/-- The hex digits table. -/
abbrev hextab : List w8 :=
  [48#8, 49#8, 50#8, 51#8, 52#8, 53#8, 54#8, 55#8, 56#8, 57#8, 97#8, 98#8, 99#8, 100#8, 101#8, 102#8]

theorem hextab_hi (x : w8) :
    ∃ b, (if 0 ≤ sint.Z (W64 (uint.Z (x >>> W64 4))) then
      hextab[sint.nat (W64 (uint.Z (x >>> W64 4)))]? else none) = some b := by
  have := w8_shr4_lt x
  exact string_index_some _ _ (by simp only [List.length_cons, List.length_nil]; word) (by word)

theorem w8_and15_lt (x : w8) : uint.Z (x &&& W8 15) < 16 := by
  have : (x &&& W8 15).toNat ≤ 15 := by
    rw [BitVec.toNat_and]; exact Nat.and_le_right
  simp only [uint.Z]; omega

theorem hextab_lo (x : w8) :
    ∃ b, (if 0 ≤ sint.Z (W64 (uint.Z (x &&& W8 15))) then
      hextab[sint.nat (W64 (uint.Z (x &&& W8 15)))]? else none) = some b := by
  have := w8_and15_lt x
  exact string_index_some _ _ (by simp only [List.length_cons, List.length_nil]; word) (by word)

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
  [TH : TreemapHyp GF]

omit [state.Assumptions] in
/-- A byte slice has at most `maxAddr` elements. -/
theorem ownSlice_bytes_len_le (s : GoSlice) (dq : DFrac) (bs : List w8) :
    (s ↦*{dq} bs : IProp GF) ⊢ ⌜bs.length ≤ maxAddr⌝ := by
  iintro Hs
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  rw [ownSlice_unseal]; unfold ownSliceDef
  icases Hs with (%H | ⟨H, %_⟩)
  · ipureintro; rw [H.2]; simp [maxAddr]
  · by_cases hb : bs = []
    · ipureintro; rw [hb]; simp [maxAddr]
    · icases typedPointsto_byte_array_bounds _ _ _ _ hb $$ H with %Hb
      have : (sint.nat s.len : Int) = sint.Z s.len := Int.toNat_of_nonneg Hl.2
      ipureintro; omega

theorem state.hexEncodeToString.spec_holds (src : GoSlice) (dq : DFrac) (bs : List w8) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ∗
      src ↦*{dq} bs }}
    (App (Val (@! state.hexEncodeToString)) (Val #src))
  {{ (s : GoString), RET #s; src ↦*{dq} bs }} := by
  wp_start as Hs
  ihave %Hbl := ownSlice_len _ _ _ $$ Hs
  ihave %Hmax := ownSlice_bytes_len_le _ _ _ $$ Hs
  wp_auto
  have hbl : (bs.length : Int) = sint.Z src.len := by
    rw [Hbl.1]; exact Int.toNat_of_nonneg Hbl.2
  have hl2 : sint.Z (src.len * W64 2) = 2 * bs.length := by
    simp [maxAddr] at Hmax; word
  wp_apply (wp_slice_make2 (V := w8)) as %dst ⟨Hd, -⟩
  · ipureintro; omega
  ihave HI : (∃ (i : w64) (ds : List w8) (x : w8),
      "i" ∷ i_ptr ↦ i ∗ "j" ∷ j_ptr ↦ (i * W64 2) ∗ "v" ∷ v_ptr ↦ x ∗
      "Hd" ∷ dst ↦* ds ∗ "Hs" ∷ src ↦*{dq} bs ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ bs.length ∧ ds.length = 2 * bs.length⌝ :
      IProp GF) $$ [i j v Hd Hs]
  · iexists W64 0, _, _
    iframe
    ipureintro; simp; word
  wp_for HI
  wp_if_destruct
  · ihave %Hdl := ownSlice_len _ _ _ $$ Hd
    have hil : (sint.Z i).toNat < bs.length := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, Hif⟩)]
    wp_apply wp_load_slice_index src (sint.Z i) bs dq bs[(sint.Z i).toNat] Hi.1 $$ [$Hs] as Hs
    · ipureintro; exact List.getElem?_eq_getElem hil
    obtain ⟨b1, hb1⟩ := hextab_hi bs[(sint.Z i).toNat]
    rw [hb1]
    wp_auto
    have hmx : maxAddr = 2 ^ 47 := rfl
    have hj : sint.Z (i * W64 2) = 2 * sint.Z i := by word
    have hj1 : sint.Z (i * W64 2 + W64 1) = 2 * sint.Z i + 1 := by word
    have hdl : (ds.length : Int) = sint.Z dst.len := by
      rw [Hdl.1]; exact Int.toNat_of_nonneg Hdl.2
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    wp_apply wp_store_slice_index dst _ ds b1 $$ [$Hd] as Hd
    · ipureintro; omega
    obtain ⟨b2, hb2⟩ := hextab_lo bs[(sint.Z i).toNat]
    rw [hb2]
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    wp_apply wp_store_slice_index dst _ _ b2 $$ [$Hd] as Hd
    · ipureintro; rw [List.length_set, hj1]; omega
    wp_for_post
    iframe
    iexists i + W64 1, _, _
    rw [show i * W64 2 + W64 2 = (i + W64 1) * W64 2 by word]
    iframe
    have hi1 : sint.Z (i + W64 1) = sint.Z i + 1 := by word
    ipureintro
    refine ⟨by omega, by omega, by simp; omega⟩
  wp_apply wp_bytes_to_string dst ds (DFrac.own 1) $$ [$Hd] as Hd
  iapply HΦ $$ Hs

omit [state.Assumptions] in
/-- `a[i] = v'` for a byte array `a` of 65 elements at `p`. -/
theorem wp_store_byte_array (p : Loc) (vs : List w8) (i : Int) (v' : w8) (hi : 0 ≤ i ∧ i < 65) :
  {{ (p ↦ (array.mk 65 vs : GoArray w8 65) : IProp GF) }}
    (App (Val (GoInstruction (GoStore go.byte))) (Val (PairV #(arrayIndexRef w8 i p) #v')))
  {{ RET #(); p ↦ (array.mk 65 (vs.set i.toNat v') : GoArray w8 65) }} := by
  iintro %Φ Ha HΦ
  ihave %Hl := array_len _ _ _ _ $$ Ha
  have hlt : i.toNat < vs.length := by omega
  icases array_acc p i _ 65 (array.mk 65 vs) vs[i.toNat] hi.1
    (List.getElem?_eq_getElem hlt) $$ Ha with ⟨Hv, Ha⟩
  wp_apply IntoValTyped.wp_store (t := go.byte) _ _ _ $$ Hv as Hv
  iapply HΦ
  iapply Ha $$ Hv

theorem state.formatInt16.spec_holds (x : w64) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state }}
    (App (Val (@! state.formatInt16)) (Val #x))
  {{ (s : GoString), RET #s; True }} := by
  wp_start
  wp_auto
  wp_join iprop(∃ u0 : w64, "u" ∷ u_ptr ↦ u0) with [u] as ⟨%u0, u⟩
  have hz : (zero_val (GoArray w8 65)) = array.mk 65 (List.replicate 65 (W8 0)) := rfl
  rw [hz]
  ihave HI : (∃ (u : w64) (j : w64) (vs : List w8),
      "u" ∷ u_ptr ↦ u ∗ "j" ∷ j_ptr ↦ j ∗ "a" ∷ a_ptr ↦ (array.mk 65 vs : GoArray w8 65) ∗
      "%Hj" ∷ ⌜49 ≤ sint.Z j ∧ sint.Z j ≤ 65 ∧ uint.nat u < 16 ^ ((sint.Z j).toNat - 49)⌝ :
      IProp GF) $$ [u j a]
  · iexists u0, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    have : (sint.Z (W64 65)).toNat - 49 = 16 := by word
    rw [this]; word
  wp_for HI
  wp_if_destruct
  · have hu16 : 16 ≤ uint.nat u := by word
    have hk := pow16_ge2 _ _ hu16 Hj.2.2
    have hj1 : sint.Z (j - W64 1) = sint.Z j - 1 := by word
    have hm : uint.Z (u &&& (W64 16 - W64 1)) ≤ 15 :=
      Int.le_trans (w64_and_le _ _) (by word)
    obtain ⟨b1, hb1⟩ := string_index_some
      [48#8, 49#8, 50#8, 51#8, 52#8, 53#8, 54#8, 55#8, 56#8, 57#8, 97#8, 98#8, 99#8, 100#8, 101#8,
        102#8, 103#8, 104#8, 105#8, 106#8, 107#8, 108#8, 109#8, 110#8, 111#8, 112#8, 113#8, 114#8,
        115#8, 116#8, 117#8, 118#8, 119#8, 120#8, 121#8, 122#8]
      (u &&& (W64 16 - W64 1)) (by simp only [List.length_cons, List.length_nil]; omega) (by omega)
    rw [hb1]
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    wp_apply wp_store_byte_array a_ptr vs _ b1 (by omega) $$ [$a] as a
    wp_for_post
    iframe
    iexists u >>> W64 4, j - W64 1, _
    iframe
    ipureintro
    have hsh : uint.nat (u >>> W64 4) = uint.nat u / 16 := by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have he : (sint.Z (j - W64 1)).toNat - 49 = (sint.Z j).toNat - 49 - 1 := by omega
    refine ⟨by omega, by omega, ?_⟩
    rw [hsh, he]
    exact div16_lt _ _ (by omega) Hj.2.2
  have hu : uint.Z u < 16 := by word
  have hj1 : sint.Z (j - W64 1) = sint.Z j - 1 := by word
  obtain ⟨b1, hb1⟩ := string_index_some
    [48#8, 49#8, 50#8, 51#8, 52#8, 53#8, 54#8, 55#8, 56#8, 57#8, 97#8, 98#8, 99#8, 100#8, 101#8,
      102#8, 103#8, 104#8, 105#8, 106#8, 107#8, 108#8, 109#8, 110#8, 111#8, 112#8, 113#8, 114#8,
      115#8, 116#8, 117#8, 118#8, 119#8, 120#8, 121#8, 122#8]
    u (by simp only [List.length_cons, List.length_nil]; omega) (by omega)
  rw [hb1]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
  wp_apply wp_store_byte_array a_ptr vs _ b1 (by omega) $$ [$a] as a
  wp_join iprop(∃ (j' : w64) (vs' : List w8), "j" ∷ j_ptr ↦ j' ∗
      "a" ∷ a_ptr ↦ (array.mk 65 vs' : GoArray w8 65) ∗ "%Hj'" ∷ ⌜0 ≤ sint.Z j' ∧ sint.Z j' ≤ 65⌝)
    with [j a] as ⟨%j', %vs', j, a, %Hj'⟩
  · have hj2 : sint.Z (j - W64 1 - W64 1) = sint.Z j - 2 := by word
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    wp_apply wp_store_byte_array a_ptr _ _ _ (by omega) $$ [$a] as a
    isplitr
    · ipureintro; rfl
    iexists _, _; iframe; ipureintro; omega
  · iexists _, _; iframe; ipureintro; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj'.1, by word, by word⟩)]
  icases (array_split j' a_ptr _ 65 (array.mk 65 vs') ⟨Hj'.1, Hj'.2⟩).1 $$ a with ⟨-, Hsuf⟩
  ihave %Hl := array_len _ _ _ _ $$ Hsuf
  ihave Hsl : slice.mk (arrayIndexRef w8 (sint.Z j') a_ptr) (W64 65 - j') (W64 65 - j') ↦*
      ((array.mk 65 vs' : GoArray w8 65).arr.drop (sint.nat j')) $$ [Hsuf]
  · have e : sint.Z (W64 65 - j') = 65 - sint.Z j' := by word
    rw [ownSlice_unseal]; unfold ownSliceDef
    iright
    dsimp only; rw [e]
    isplitl [Hsuf]
    · iexact Hsuf
    · ipureintro; omega
  wp_apply wp_bytes_to_string _ _ (DFrac.own 1) $$ [$Hsl] as Hsl
  iapply HΦ $$ %_ []
  itrivial

theorem state.Key.String.spec_holds (l : Loc) (dq : DFrac) (k : w64) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ∗
      l ↦{dq} k }}
    (App (Val (l @!! go.GoType.PointerType state.Key.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; l ↦{dq} k }} := by
  wp_start as Hl
  wp_auto
  wp_apply state.formatInt16.spec_holds as %s -
  iapply HΦ $$ Hl

theorem state.Value.String.spec_holds (l : Loc) (dq : DFrac) (sl : GoSlice) (v : List w8) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ∗
      l ↦{dq} sl ∗ sl ↦*□ v }}
    (App (Val (l @!! go.GoType.PointerType state.Value.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; l ↦{dq} sl }} := by
  wp_start as ⟨Hl, #Hv⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_if_destruct
  · iapply HΦ $$ Hl
  wp_apply state.hexEncodeToString.spec_holds sl DFrac.discard v $$ [$Hv] as %s -
  iapply HΦ $$ Hl

theorem state.Command.String.spec_holds : state.Command.String.spec (GF := GF) := by
  intro c dq cv wc hscan
  wp_start as ⟨Hc, #Hok⟩
  unfold cmdOk
  icases Hok with ⟨%Hop, #Hv⟩
  ihave ⟨Hc, %Hnn⟩ := typedPointsto_not_null_dup $$ Hc
  iStructNamed Hc
  wp_auto
  wp_if_destruct
  · wp_apply state.Key.String.spec_holds $$ [$K] as %s1 K
    wp_apply state.Value.String.spec_holds _ _ _ wc.val $$ [$V $Hv] as %s2 V
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe Op K V
  wp_if_destruct
  · wp_apply state.Key.String.spec_holds $$ [$K] as %s1 K
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe Op K V
  wp_if_destruct
  · -- SCAN
    have h8 := hscan (by rw [← Hop.1]; exact Hif)
    ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
    · iPkgInit
    ihave #Hv8 : cv.V' ↦*□ (wc.val.take 8 ++ wc.val.drop 8) $$ []
    · rw [List.take_append_drop]; iexact Hv
    wp_apply encoding.binary.wp_LittleEndian_Uint64 cv.V' (wc.val.take 8) _ (wc.val.drop 8)
      (by simp; omega) $$ [$Hv8] as -
    wp_apply state.Key.String.spec_holds $$ [$K] as %s1 K
    wp_apply state.formatUint10.spec_holds as %s2 -
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe Op K V
  wp_apply state.Value.String.spec_holds _ _ _ wc.val $$ [$V $Hv] as %s2 V
  wp_apply state.Key.String.spec_holds $$ [$K] as %s1 K
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Op K V

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
