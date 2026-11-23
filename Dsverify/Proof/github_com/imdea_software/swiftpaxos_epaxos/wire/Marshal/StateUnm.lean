/-
`state`'s decoders: `Operation`, `Key`, `Value`, `Command` (`Unmarshal`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.RProg
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Codec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [state.Assumptions] [bufio.Assumptions] [io.Assumptions]
variable [EpBufioDeps GF]

set_option goose.wp.extras true

theorem slice_len_Z' (s : GoSlice) (dq : DFrac) (vs : List w8) :
    (s ↦*{dq} vs : IProp GF) ⊢ s ↦*{dq} vs ∗ ⌜(vs.length : Int) = sint.Z s.len⌝ := by
  iintro Hs
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  iframe Hs
  ipureintro
  rw [Hl.1]; exact Int.toNat_of_nonneg Hl.2

theorem state.Operation.Unmarshal.spec_holds : state.Operation.Unmarshal.spec (GF := GF) := by
  intro l op0 br rd R
  wp_start as ⟨Hown, #Hnext, Hl⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := w8)) as %bs ⟨Hbs, -⟩
  · ipureintro; decide
  wp_apply wp_ReadFull_br br rd R bs _ $$ [$Hpkg2 $Hown $Hbs]
    as %n %err ⟨%data, %Hd, Hbs, Hown⟩
  obtain ⟨-, hdl, hiff⟩ := Hd

  rcases err with ei | _
  · -- an error
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    iexists data
    iframe Hown
    iexists op0; iexact Hl
  have hd1 : data.length = 1 := by simpa using hiff.mp rfl
  obtain ⟨c, rfl⟩ : ∃ c, data = [c] := by
    match data, hd1 with
    | [c], _ => exact ⟨c, rfl⟩
  simp only [List.length_singleton, List.drop_one]
  ihave ⟨Hbs, %hl⟩ := slice_len_Z' _ _ _ $$ Hbs
  have hW0 : sint.Z (W64 0) = 0 := rfl
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by simp at hl; omega⟩)]
  wp_apply wp_load_slice_index bs _ _ _ c (by decide) $$ [Hbs] as Hbs
  · iframe Hbs; ipureintro; rfl
  wp_auto
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists c
  iframe Hown Hl

theorem state.Key.Unmarshal.spec_holds : state.Key.Unmarshal.spec (GF := GF) := by
  intro l k0 br rd R
  wp_start as ⟨Hown, #Hnext, Hl⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := w8)) as %bs ⟨Hbs, -⟩
  · ipureintro; decide
  wp_apply wp_ReadFull_br br rd R bs _ $$ [$Hpkg2 $Hown $Hbs]
    as %n %err ⟨%data, %Hd, Hbs, Hown⟩
  obtain ⟨-, hdl, hiff⟩ := Hd
  rcases err with ei | _
  · -- an error
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    iexists data
    iframe Hown
    iexists k0; iexact Hl
  have hd8 : data.length = 8 := by simpa using hiff.mp rfl
  rw [List.drop_eq_nil_of_le (by simp; omega), List.append_nil]
  rw [show data = data ++ [] by simp]
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  wp_auto
  wp_apply encoding.binary.wp_LittleEndian_Uint64 bs data _ [] hd8 $$ [$Hbs] as Hbs
  (try wp_auto)
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists leToU64 data
  rw [leToU64_le data hd8]
  simp only [List.append_nil]
  iframe Hown Hl

theorem state.Value.Unmarshal.spec_holds : state.Value.Unmarshal.spec (GF := GF) := by
  intro l sl0 br rd R
  wp_start as ⟨Hown, #Hnext, Hl⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := w8)) as %bs ⟨Hbs, -⟩
  · ipureintro; decide
  wp_apply wp_ReadFull_br br rd R bs _ $$ [$Hpkg2 $Hown $Hbs]
    as %n %err ⟨%d1, %Hd, Hbs, Hown⟩
  obtain ⟨-, hdl, hiff⟩ := Hd
  rcases err with ei | _
  · -- an error
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    iexists d1
    iframe Hown
    iexists sl0; iexact Hl
  have hd4 : d1.length = 4 := by simpa using hiff.mp rfl
  ihave ⟨Hown, Hp⟩ := nextIs_read br rd R d1 encValue _ $$ [$Hnext $Hown]
  imod Hp with %Hp
  obtain ⟨v, ext, hv, hp⟩ := Hp
  obtain ⟨hd1, a, b, hab, hlen⟩ := value_hdr d1 hd4 v ext hv hp
  rw [List.drop_eq_nil_of_le (by simp; omega), List.append_nil, hab]
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  rw [show [a, b, W8 0, W8 0] = [a, b] ++ [W8 0, W8 0] from rfl]
  wp_auto
  wp_apply encoding.binary.wp_LittleEndian_Uint16 bs a b _ _ $$ [$Hbs] as %r ⟨%Hr, Hbs⟩
  rw [← show d1 = [a, b] ++ [W8 0, W8 0] from hab]
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8)) as %bs2 ⟨Hbs2, -⟩
  · ipureintro; word
  (try wp_auto)
  wp_apply wp_ReadFull_br br rd (R ++ d1) bs2 _ $$ [$Hpkg2 $Hown $Hbs2]
    as %n2 %err2 ⟨%d2, %Hd2, Hbs2, Hown⟩
  obtain ⟨-, hdl2, hiff2⟩ := Hd2
  rw [List.append_assoc]
  rcases err2 with ei | _
  · -- an error
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    iexists d1 ++ d2
    iframe Hown
    iexists sl0; iexact Hl
  have hr64 : sint.nat (BitVec.setWidth 64 r) = uint.nat r := by
    have := r.isLt
    simp only [sint.nat, uint.nat, BitVec.toInt, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (by omega), if_pos (by omega)]; simp
  have hd2 : d2.length = uint.nat r := by simpa [hr64] using hiff2.mp rfl
  rw [List.drop_eq_nil_of_le (by simp [hr64] at *; omega), List.append_nil]
  wp_auto
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists d2
  have hr16 : uint.Z r < 2 ^ 16 := by have := r.isLt; simp [uint.Z]; omega
  have hlv : d2.length = v.length := by
    have : (uint.nat r : Int) = uint.Z r := by simp [uint.nat]
    omega
  isplitr
  · ipureintro; show d2.length < 2 ^ 16; omega
  rw [show d1 = u32Le (W32 (d2.length % 2 ^ 16 : Nat)) by rw [hlv]; exact hd1]
  simp only [encValue]
  iframe Hown
  iexists bs2
  iframe Hl Hbs2

theorem cmd_rest (op : w8) (k : w64) (wc : WCmd) (ext t : List w8) (hwf : cmdWf wc)
    (hp : [op] ++ u64Le k ++ t <+: encCommand wc ++ ext) :
    ∃ (v : List w8) (ext' : List w8), v.length < 2 ^ 16 ∧ t <+: encValue v ++ ext' := by
  obtain ⟨u, hu⟩ := hp
  refine ⟨wc.val, ext, hwf, u, ?_⟩
  simp only [encCommand, List.append_assoc] at hu
  have := append_prefix_of_length_eq (u := [op] ++ u64Le k) (v := [wc.op] ++ u64Le wc.key)
    (by simp [u64Le_length]) (x := t ++ u) (y := encValue wc.val ++ ext) (by simpa using hu)
  exact this.2

theorem state.Command.Unmarshal.spec_holds : state.Command.Unmarshal.spec (GF := GF) := by
  intro l cv0 br rd R
  wp_start as ⟨Hown, #Hnext, Hl⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  -- the operation
  ihave #Hn1 := nextIs_total rd R (fun op : w8 => [op]) (fun _ => True)
    (total_of_fixed _ 1 (fun _ => rfl) (fun t ht => by
      match t, ht with | [c], _ => exact ⟨c, rfl⟩))
  wp_apply state.Operation.Unmarshal.spec_holds _ cv0.Op' br rd R
    $$ [$Hpkg $Hpkg2 $Hown $Hn1 $Op] as %e1 H1
  icases H1 with (⟨%he1, %op, -, Hown, Op⟩ | ⟨%he1, %d, Hown, %op, Op⟩)
  rotate_left
  · -- an error
    rcases e1 with ei | _
    · wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; simp
      iexists d
      iframe Hown
      iexists ⟨op, cv0.K', cv0.V'⟩
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe Op K V
    · exact absurd rfl he1
  subst he1
  wp_auto
  -- the key
  ihave #Hn2 := nextIs_total rd (R ++ [op]) u64Le (fun _ => True)
    (total_of_fixed _ 8 u64Le_length (fun t ht => ⟨_, (leToU64_le t ht)⟩))
  wp_apply state.Key.Unmarshal.spec_holds _ cv0.K' br rd (R ++ [op])
    $$ [$Hpkg $Hpkg2 $Hown $Hn2 $K] as %e2 H2
  icases H2 with (⟨%he2, %k, -, Hown, K⟩ | ⟨%he2, %d, Hown, %k, K⟩)
  rotate_left
  · -- an error
    rcases e2 with ei | _
    · wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; simp
      iexists [op] ++ d
      rw [List.append_assoc]
      iframe Hown
      iexists ⟨op, k, cv0.V'⟩
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe Op K V
    · exact absurd rfl he2
  subst he2
  wp_auto
  -- the value
  ihave #Hn3 := nextIs_shift rd R ([op] ++ u64Le k) encCommand cmdWf encValue
    (fun v => v.length < 2 ^ 16) (fun wc ext t hwf hp => cmd_rest op k wc ext t hwf hp) $$ Hnext
  rw [List.append_assoc]
  wp_apply state.Value.Unmarshal.spec_holds _ cv0.V' br rd (R ++ ([op] ++ u64Le k))
    $$ [$Hpkg $Hpkg2 $Hown $Hn3 $V] as %e3 H3
  icases H3 with (⟨%he3, %v, %hv, Hown, %sl, V, Hsl⟩ | ⟨%he3, %d, Hown, %sl, V⟩)
  rotate_left
  · -- an error
    rcases e3 with ei | _
    · wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; simp
      iexists [op] ++ u64Le k ++ d
      simp only [List.append_assoc] at *
      iframe Hown
      iexists ⟨op, k, sl⟩
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe Op K V
    · exact absurd rfl he3
  subst he3
  ihave Hsl := ownSlice_persist _ _ _ $$ Hsl
  imod Hsl
  icases Hsl with #Hsl
  wp_auto
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists ⟨op, k, v⟩
  isplitr
  · ipureintro; exact hv
  simp only [encCommand, List.append_assoc] at *
  iframe Hown
  iexists ⟨op, k, sl⟩
  isplitl [Op K V]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe Op K V
  iunfold cmdOk
  iframe Hsl
  ipureintro; exact ⟨rfl, rfl⟩

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
