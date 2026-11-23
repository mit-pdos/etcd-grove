/-
`state`'s marshalers: `Operation`, `Key`, `Value`, `Command` (`Marshal`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.WProg
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Binary16

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [state.Assumptions] [bufio.Assumptions]
variable [EpBufioDeps GF]

set_option goose.wp.extras true

theorem slice_len_Z (s : GoSlice) (dq : DFrac) (vs : List w8) :
    (s ↦*{dq} vs : IProp GF) ⊢ ⌜(vs.length : Int) = sint.Z s.len⌝ := by
  iintro Hs
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  ipureintro
  rw [Hl.1]; exact Int.toNat_of_nonneg Hl.2

theorem state.Operation.Marshal.spec_holds : state.Operation.Marshal.spec (GF := GF) := by
  intro l dq op bw wr sent pend err
  wp_start as ⟨Hown, HQ, Hl⟩
  ihave Hw := wprog_start bw wr sent pend err [op] $$ [$Hown $HQ]
  wp_auto
  wp_apply (wp_slice_make2 (V := w8)) as %bs ⟨Hbs, -⟩
  · ipureintro; decide
  ihave %hl := slice_len_Z $$ Hbs
  have hW0 : sint.Z (W64 0) = 0 := rfl
  simp only [List.length_replicate] at hl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by omega⟩)]
  wp_apply wp_store_slice_index bs (sint.Z (W64 0)) _ op $$ [Hbs] as Hbs
  · iframe Hbs; ipureintro; simp
  wp_auto
  rw [show (List.replicate 1 (zero_val w8)).set 0 op = [op] from rfl]
  wp_apply wp_wprog_Write bw wr sent pend err [] [op] [op] [] bs _ rfl $$ [$Hpkg2 $Hw $Hbs]
    as %nn %e ⟨Hbs, Hw⟩
  iapply HΦ
  iframe Hl
  iapply wprog_finish _ _ _ _ _ _ _ (by simp) $$ Hw

theorem state.Key.Marshal.spec_holds : state.Key.Marshal.spec (GF := GF) := by
  intro l dq k bw wr sent pend err
  wp_start as ⟨Hown, HQ, Hl⟩
  ihave Hw := wprog_start bw wr sent pend err (u64Le k) $$ [$Hown $HQ]
  wp_auto
  wp_apply (wp_slice_make2 (V := w8)) as %bs ⟨Hbs, -⟩
  · ipureintro; decide
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  wp_apply encoding.binary.wp_LittleEndian_PutUint64 bs (List.replicate 8 (zero_val w8)) [] k rfl
    $$ [Hbs] as Hbs
  · rw [List.append_nil]; iframe Hbs
  rw [List.append_nil]
  wp_apply wp_wprog_Write bw wr sent pend err [] (u64Le k) (u64Le k) [] bs _ (by simp) $$
    [$Hpkg2 $Hw $Hbs] as %nn %e ⟨Hbs, Hw⟩
  iapply HΦ
  iframe Hl
  iapply wprog_finish _ _ _ _ _ _ _ (by simp) $$ Hw

theorem state.Value.Marshal.spec_holds : state.Value.Marshal.spec (GF := GF) := by
  intro l dq dq' sl v bw wr sent pend err
  wp_start as ⟨Hown, HQ, Hl, Hv⟩
  ihave Hw := wprog_start bw wr sent pend err (encValue v) $$ [$Hown $HQ]
  wp_auto
  wp_apply (wp_slice_make2 (V := w8)) as %bs ⟨Hbs, -⟩
  · ipureintro; decide
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  simp only [decide_eq_false Hnn]
  wp_auto
  ihave %hvl := slice_len_Z $$ Hv
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  rw [show List.replicate 4 (zero_val w8) = [W8 0, W8 0] ++ [W8 0, W8 0] from rfl]
  wp_apply encoding.binary.wp_LittleEndian_PutUint16 bs [W8 0, W8 0] [W8 0, W8 0] _ rfl
    $$ [Hbs] as Hbs
  · iexact Hbs
  have hx : u32Le (W32 (uint.Z (W16 (sint.Z sl.len)))) = u32Le (W32 (v.length % 2 ^ 16 : Nat)) := by
    congr 2; rw [← hvl]; simp [uint.Z, W16]
  rw [encoding.binary.u16Le_u32Le, hx]
  wp_apply wp_wprog_Write bw wr sent pend err [] (encValue v) _ v bs _ rfl $$
    [$Hpkg2 $Hw $Hbs] as %nn %e ⟨Hbs, Hw⟩
  wp_apply wp_wprog_Write bw wr sent pend err _ v v [] sl _ (by simp) $$
    [$Hpkg2 $Hw $Hv] as %nn2 %e2 ⟨Hv, Hw⟩
  iapply HΦ
  iframe Hl Hv
  iapply wprog_finish _ _ _ _ _ _ _ (by simp [encValue]) $$ Hw

theorem state.Command.Marshal.spec_holds : state.Command.Marshal.spec (GF := GF) := by
  intro l dq cv wc bw wr sent pend err
  wp_start as ⟨Hown, HQ, Hl, #Hc⟩
  ihave Hw := wprog_start bw wr sent pend err (encCommand wc) $$ [$Hown $HQ]
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iunfold cmdOk at Hc
  icases Hc with ⟨%Hc, #Hv⟩
  obtain ⟨hop, hk⟩ := Hc
  iStructNamed Hl
  wp_auto
  wp_apply wp_wprog_marshal _ _ _ _ (state.Operation.Marshal.spec_holds _ dq cv.Op') bw wr
    sent pend err [] _ (u64Le wc.key ++ encValue wc.val) (by simp [encCommand, hop])
    $$ [$Hpkg $Hpkg2 $Hw $Op] as ⟨Op, Hw⟩
  (try wp_auto)
  wp_apply wp_wprog_marshal _ _ _ _ (state.Key.Marshal.spec_holds _ dq cv.K') bw wr
    sent pend err _ _ (encValue wc.val) (by simp [hk]) $$ [$Hpkg $Hpkg2 $Hw $K] as ⟨K, Hw⟩
  (try wp_auto)
  wp_apply wp_wprog_marshal _ _ _ _ (state.Value.Marshal.spec_holds _ dq _ cv.V' wc.val) bw wr
    sent pend err _ _ [] (by simp) $$ [$Hpkg $Hpkg2 $Hw $V $Hv] as ⟨⟨V, -⟩, Hw⟩
  iapply HΦ
  isplitl [Op K V]
  · isplitl [Op K V]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe Op K V
    · iunfold cmdOk; iframe Hv; ipureintro; exact ⟨hop, hk⟩
  iapply wprog_finish _ _ _ _ _ _ _ (by simp [encCommand, hop, hk]) $$ Hw

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
