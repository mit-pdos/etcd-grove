/-
Shared pieces of the epaxos marshalers' proofs (internal to the wire package): a slice length
written as a varint (`wvarint`), the `[16]byte` buffer.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Bytes
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.RProg
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Codec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.StateOps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.StateUnm
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Varint
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Varint.Decode

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem varintEnc_length_le (x : w64) : (varintEnc x).length ≤ 10 :=
  uvarintEnc_length_le_10 _ (zigzag_lt x)

section
variable [GooseExts] [GoGlobalContext]

/-- A slice's length (`len(s)`, as the `int64` the code writes) as a varint: `encLen`. -/
theorem slice_len_varint (sl : GoSlice) (n : Nat) (h : (n : Int) = sint.Z sl.len) :
    varintEnc sl.len = encLen n ∧ n < 2 ^ 63 := by
  have h63 : sint.Z sl.len < 2 ^ 63 := by word
  have hn : n < 2 ^ 63 := by omega
  refine ⟨?_, hn⟩
  have hcl : sl.len = W64 (n : Int) := by
    apply BitVec.eq_of_toInt_eq
    show sint.Z sl.len = sint.Z (W64 (n : Int))
    rw [sint_Z_W64_length (by omega)]
    omega
  rw [hcl, encLen_varint _ hn]

theorem slice_len_int {V : Type} (vs : List V) (sl : GoSlice) (h : vs.length = sint.nat sl.len ∧ 0 ≤ sint.Z sl.len) :
    (vs.length : Int) = sint.Z sl.len := by
  rw [h.1]; exact Int.toNat_of_nonneg h.2

end

set_option hygiene false in
/-- `wlen := putVarint(b[:], X); if wlen >= 0 { wire.Write(b[0:wlen]) }` on the `[16]byte`
buffer `b_ptr` (`Harr : arrBytes b_ptr (W64 16)`), the progress `Hw` going from
`rest = varintEnc X ++ TODO` (proved by `hr`) to `TODO`. -/
macro "wvarint" X:term:max REST:term:max TODO:term:max hr:term:max : tactic => `(tactic| (
  have h16 : sint.Z (W64 16) = 16 := rfl
  have hW0 : sint.Z (W64 0) = 0 := rfl
  iunfold arrBytes at Harr
  icases Harr with ⟨%L, %hL, Hb⟩
  ihave ⟨Hbs, Hback⟩ := array_slice_acc b_ptr L (W64 16) (W64 16) 16 rfl hL.symm (by omega)
    (by omega) $$ Hb
  have hpv := epaxos.putVarint.spec_holds (GF := GF)
  unfold epaxos.putVarint.spec at hpv
  ihave #Hep : pkgInit_epaxos $$ []
  · iexact Hpkg
  have hvl := varintEnc_length_le $X
  have hL16 : (L.take 16).length = 16 := by simp; omega
  wp_apply hpv _ (L.take 16) $X $$ [Hbs] as Hbs
  · iframe Hbs; ipureintro; omega
  have hwlen : sint.Z (W64 (varintEnc $X).length) = (varintEnc $X).length := by
    rw [sint_Z_W64_length]; omega
  (try wp_auto)
  have hge : sint.Z (W64 0) ≤ sint.Z (W64 ((varintEnc $X).length : Int)) := by
    rw [hwlen]; show (0 : Int) ≤ _; omega
  simp only [decide_eq_true hge]
  ihave Hb := Hback $$ %_ %(by simp; omega) Hbs
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by rw [hwlen]; omega⟩)]
  have hl2 : ((varintEnc $X ++ (L.take 16).drop (varintEnc $X).length) ++
      L.drop 16).length = 16 := by
    simp only [List.length_append, List.length_drop, List.length_take]; omega
  ihave ⟨Hbs, Hback⟩ := array_slice_acc b_ptr _ (W64 ((varintEnc $X).length : Int)) (W64 16)
    (varintEnc $X).length hwlen (by rw [hl2]; rfl) (by omega) (by omega) $$ Hb
  have htk : ((varintEnc $X ++ (L.take 16).drop (varintEnc $X).length) ++
      L.drop 16).take (varintEnc $X).length = varintEnc $X := by simp
  rw [htk]
  (try wp_auto)
  wp_apply wp_wprog_Write bw wr sent pend err _ $REST (varintEnc $X) $TODO _ _ $hr
    $$ [Hpkg2 Hw Hbs] as %nn1 %e1 ⟨Hbs, Hw⟩
  · iframe Hw Hbs
  ihave Hb := Hback $$ %_ %(by simp) Hbs
  ihave Harr := arrBytes_intro b_ptr (W64 16) _ (by
    simp only [List.length_append, List.length_drop, List.length_take]; omega) $$ Hb
  (try wp_auto)))

set_option hygiene false in
/-- `wvarint` on a `[N]byte` buffer `b_ptr` (`Harr : arrBytes b_ptr (W64 N)`, `N ≥ 10`), the progress `Hw` going from
`rest = varintEnc X ++ TODO` (proved by `hr`) to `TODO`. -/
macro "wvarintN" N:num X:term:max REST:term:max TODO:term:max hr:term:max : tactic => `(tactic| (
  have hN : sint.Z (W64 $N) = $N := rfl
  have hW0 : sint.Z (W64 0) = 0 := rfl
  iunfold arrBytes at Harr
  icases Harr with ⟨%L, %hL, Hb⟩
  ihave ⟨Hbs, Hback⟩ := array_slice_acc b_ptr L (W64 $N) (W64 $N) $N rfl hL.symm (by omega)
    (by omega) $$ Hb
  have hpv := epaxos.putVarint.spec_holds (GF := GF)
  unfold epaxos.putVarint.spec at hpv
  ihave #Hep : pkgInit_epaxos $$ []
  · iexact Hpkg
  have hvl := varintEnc_length_le $X
  have hL16 : (L.take $N).length = $N := by simp; omega
  wp_apply hpv _ (L.take $N) $X $$ [Hbs] as Hbs
  · iframe Hbs; ipureintro; omega
  have hwlen : sint.Z (W64 (varintEnc $X).length) = (varintEnc $X).length := by
    rw [sint_Z_W64_length]; omega
  (try wp_auto)
  have hge : sint.Z (W64 0) ≤ sint.Z (W64 ((varintEnc $X).length : Int)) := by
    rw [hwlen]; show (0 : Int) ≤ _; omega
  simp only [decide_eq_true hge]
  ihave Hb := Hback $$ %_ %(by simp; omega) Hbs
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by rw [hwlen]; omega⟩)]
  have hl2 : ((varintEnc $X ++ (L.take $N).drop (varintEnc $X).length) ++
      L.drop $N).length = $N := by
    simp only [List.length_append, List.length_drop, List.length_take]; omega
  ihave ⟨Hbs, Hback⟩ := array_slice_acc b_ptr _ (W64 ((varintEnc $X).length : Int)) (W64 $N)
    (varintEnc $X).length hwlen (by rw [hl2]; rfl) (by omega) (by omega) $$ Hb
  have htk : ((varintEnc $X ++ (L.take $N).drop (varintEnc $X).length) ++
      L.drop $N).take (varintEnc $X).length = varintEnc $X := by simp
  rw [htk]
  (try wp_auto)
  wp_apply wp_wprog_Write bw wr sent pend err _ $REST (varintEnc $X) $TODO _ _ $hr
    $$ [Hpkg2 Hw Hbs] as %nn1 %e1 ⟨Hbs, Hw⟩
  · iframe Hw Hbs
  ihave Hb := Hback $$ %_ %(by simp) Hbs
  ihave Harr := arrBytes_intro b_ptr (W64 $N) _ (by
    simp only [List.length_append, List.length_drop, List.length_take]; omega) $$ Hb
  (try wp_auto)))

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
