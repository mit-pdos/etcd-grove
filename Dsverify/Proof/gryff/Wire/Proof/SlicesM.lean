/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Wire/Proof/SlicesM.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# U1: the slice types' `Marshal` (`PreAccept`, `EAccept`, `ECommit`, `TryPreAccept`, `PrepareReply`)
-/
module

public import Dsverify.Proof.gryff.Wire.Proof.Gryff1
public import Dsverify.Proof.gryff.Wire.Proof.VarintWp

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.wire

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions] [wire.BufioSpecs GF]
variable [src.state.Assumptions] [src.gryffproto.Assumptions] [src.epaxosproto.Assumptions]
variable [src.clientproto.Assumptions] [src.genericsmrproto.Assumptions]
variable [BinaryVarintHyps GF]

namespace gryffproto

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PreAccept.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : PreAccept.Msg) (bw : Loc)
    (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface)
    (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ PreAccept.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ PreAccept.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAccept.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ PreAccept.enc m) ∗ PreAccept.own t dq m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  iunfold PreAccept.own at Ht
  icases Ht with ⟨%s, Ht, Hs⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  simp only [PreAccept.goVal]
  iStructNamed Ht
  irename : ("_" ∷ True : IProp GF) => Htrue
  iclear Htrue
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  u1_marshal_auto
  have hs63 : sint.Z s.len < 2 ^ 63 := by word
  have hlen63 : m.Command.length < 2 ^ 63 := by
    have h1 := Hsl.1; have h2 := Hsl.2
    have : ((sint.nat s.len : Nat) : Int) = sint.Z s.len := Int.toNat_of_nonneg h2
    omega
  have hslen : s.len = W64 (m.Command.length : Int) := by
    apply BitVec.eq_of_toInt_eq
    show sint.Z s.len = sint.Z (W64 (m.Command.length : Int))
    rw [EtcdGrove.bufio.sint_Z_W64_length (by omega)]
    have h1 := Hsl.1; have h2 := Hsl.2
    have : ((sint.nat s.len : Nat) : Int) = sint.Z s.len := Int.toNat_of_nonneg h2
    omega
  have hvl := varintEnc_len_le m.Command.length hlen63
  have hlenZ : sint.Z (W64 (m.Command.length : Int)) = m.Command.length :=
    EtcdGrove.bufio.sint_Z_W64_length (by omega)
  rw [hslen]
  simp only [sint_Z_W64_0, go.arrayIndexRef_0, w64_sub_zero]
  wp_apply wp_PutVarint b_ptr (W64 24) 24 _ _ rfl (by omega) (by
    have : sint.nat (W64 24) = 24 := rfl
    omega) $$ [$b] as b
  have hvZ : sint.Z (W64 ((varintEnc (sint.Z (W64 (m.Command.length : Int)))).length : Int)) =
      (varintEnc (sint.Z (W64 (m.Command.length : Int)))).length := EtcdGrove.bufio.sint_Z_W64_length (by omega)
  wp_if_destruct
  rotate_left
  · exfalso; apply Hif; rw [hvZ, sint_Z_W64_0]; omega
  simp only [sint_Z_W64_0, go.arrayIndexRef_0, w64_sub_zero]
  rw [if_pos ⟨by omega, by rw [hvZ]; omega, by rw [hvZ]; omega⟩]
  wp_auto
  have hvN : sint.nat (W64 ((varintEnc (sint.Z (W64 (m.Command.length : Int)))).length : Int)) =
      (varintEnc (sint.Z (W64 (m.Command.length : Int)))).length := by
    simp only [sint.nat, hvZ]; simp
  wp_apply (wp_wire_Write_arr (E0 := E0)) $$ [Hw b] as %nn2 %e2 ⟨Hw, b⟩
  · iframe Hwr HQ Hw b
    ipureintro
    rw [hvN, List.take_left' rfl]
    refine ⟨?_, by rw [hvZ]; omega, by rw [hvZ]; omega, by rw [hvZ]; have : sint.Z (W64 24) = 24 := rfl; omega⟩
    u1_buf_norm
    u1_prefix_tac
  rw [hvN, List.take_left' rfl]
  icases wst_name _ _ _ _ _ _ _ _ $$ Hw with ⟨%D1, Hw, %hD1⟩
  have hD1pre : D1 ++ m.Command.flatMap state.Command.enc <+: E0 := by
    subst hD1
    u1_buf_norm
    u1_prefix_tac
  ihave HL : (∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗ "Hs" ∷ s ↦*{dq} m.Command ∗
      "Hw" ∷ wst bw wr J Q sent pend err
        (D1 ++ (m.Command.take (sint.nat iv)).flatMap state.Command.enc) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ m.Command.length⌝ : IProp GF) $$ [i Hs Hw]
  · iexists W64 0
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil, List.append_nil]
    iframe
    ipureintro; exact ⟨by decide, by rw [sint_Z_W64_0]; omega⟩
  wp_for HL
  wp_if_destruct
  · obtain ⟨hi0, hil⟩ := Hi
    have hlt : sint.Z iv < m.Command.length := by
      simp only [hlenZ] at Hif; simpa using Hif
    rw [if_pos ⟨hi0, by rw [hslen, hlenZ]; exact hlt⟩]
    obtain ⟨c, hc⟩ : ∃ c, m.Command[(sint.Z iv).toNat]? = some c :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    icases ownSlice_elem_acc (sint.Z iv) c s dq m.Command hi0 hc $$ Hs with ⟨He, Hback⟩
    wp_auto
    have hnat : sint.nat iv = (sint.Z iv).toNat := rfl
    wp_apply (state.Command.wp_Marshal_gen (E0 := E0)) $$ [Hw He] as ⟨Hw, He⟩
    · iframe Hwr HQ Hw He
      ipureintro
      rw [List.append_assoc, flatMap_take_succ _ _ _ _ (by rw [hnat]; exact hc)]
      exact List.IsPrefix.trans ((List.prefix_append_right_inj _).mpr (flatMap_take_prefix _ _ _))
        hD1pre
    ihave Hs := Hback $$ %c He
    rw [list_set_lookup_self _ _ _ hc]
    wp_for_post
    iframe
    iexists iv + W64 1
    have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
    have hnat1 : sint.nat (iv + W64 1) = sint.nat iv + 1 := by
      show (sint.Z (iv + W64 1)).toNat = (sint.Z iv).toNat + 1
      rw [hiv1]; omega
    rw [hnat1, ← flatMap_take_succ _ _ _ _ (by rw [hnat]; exact hc)]
    simp only [List.append_assoc]
    iframe
    ipureintro
    rw [hiv1]; omega
  obtain ⟨hi0, hil⟩ := Hi
  have hall : sint.nat iv = m.Command.length := by
    simp only [hlenZ] at Hif
    have : ¬ sint.Z iv < m.Command.length := by simpa using Hif
    show (sint.Z iv).toNat = _
    omega
  rw [hall, List.take_length]
  subst hD1
  ihave b := array_explicit _ _ _ _ $$ b
  simp only [Int.reduceToNat, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, List.singleton_append]
  u1_marshal_auto
  iapply HΦ
  isplitl [Hw]
  · iapply wst_congr _ _ _ _ _ _ _ _ _ (by u1_enc_norm <;> rfl) $$ Hw
  iunfold PreAccept.own
  iexists s
  iframe Hs
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, PreAccept.goVal]
  iframe

theorem PreAccept.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : PreAccept.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ PreAccept.enc m) ∗
        PreAccept.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAccept.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (PreAccept.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (PreAccept.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (PreAccept.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        PreAccept.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen PreAccept.wp_Marshal_gen

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem EAccept.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : EAccept.Msg) (bw : Loc)
    (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface)
    (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ EAccept.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ EAccept.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.EAccept.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ EAccept.enc m) ∗ EAccept.own t dq m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  iunfold EAccept.own at Ht
  icases Ht with ⟨%s, Ht, Hs⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  simp only [EAccept.goVal]
  iStructNamed Ht
  irename : ("_" ∷ True : IProp GF) => Htrue
  iclear Htrue
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  u1_marshal_auto
  have hs63 : sint.Z s.len < 2 ^ 63 := by word
  have hlen63 : m.Command.length < 2 ^ 63 := by
    have h1 := Hsl.1; have h2 := Hsl.2
    have : ((sint.nat s.len : Nat) : Int) = sint.Z s.len := Int.toNat_of_nonneg h2
    omega
  have hslen : s.len = W64 (m.Command.length : Int) := by
    apply BitVec.eq_of_toInt_eq
    show sint.Z s.len = sint.Z (W64 (m.Command.length : Int))
    rw [EtcdGrove.bufio.sint_Z_W64_length (by omega)]
    have h1 := Hsl.1; have h2 := Hsl.2
    have : ((sint.nat s.len : Nat) : Int) = sint.Z s.len := Int.toNat_of_nonneg h2
    omega
  have hvl := varintEnc_len_le m.Command.length hlen63
  have hlenZ : sint.Z (W64 (m.Command.length : Int)) = m.Command.length :=
    EtcdGrove.bufio.sint_Z_W64_length (by omega)
  rw [hslen]
  simp only [sint_Z_W64_0, go.arrayIndexRef_0, w64_sub_zero]
  wp_apply wp_PutVarint b_ptr (W64 44) 44 _ _ rfl (by omega) (by
    have : sint.nat (W64 44) = 44 := rfl
    omega) $$ [$b] as b
  have hvZ : sint.Z (W64 ((varintEnc (sint.Z (W64 (m.Command.length : Int)))).length : Int)) =
      (varintEnc (sint.Z (W64 (m.Command.length : Int)))).length := EtcdGrove.bufio.sint_Z_W64_length (by omega)
  wp_if_destruct
  rotate_left
  · exfalso; apply Hif; rw [hvZ, sint_Z_W64_0]; omega
  simp only [sint_Z_W64_0, go.arrayIndexRef_0, w64_sub_zero]
  rw [if_pos ⟨by omega, by rw [hvZ]; omega, by rw [hvZ]; omega⟩]
  wp_auto
  have hvN : sint.nat (W64 ((varintEnc (sint.Z (W64 (m.Command.length : Int)))).length : Int)) =
      (varintEnc (sint.Z (W64 (m.Command.length : Int)))).length := by
    simp only [sint.nat, hvZ]; simp
  wp_apply (wp_wire_Write_arr (E0 := E0)) $$ [Hw b] as %nn2 %e2 ⟨Hw, b⟩
  · iframe Hwr HQ Hw b
    ipureintro
    rw [hvN, List.take_left' rfl]
    refine ⟨?_, by rw [hvZ]; omega, by rw [hvZ]; omega, by rw [hvZ]; have : sint.Z (W64 44) = 44 := rfl; omega⟩
    u1_buf_norm
    u1_prefix_tac
  rw [hvN, List.take_left' rfl]
  icases wst_name _ _ _ _ _ _ _ _ $$ Hw with ⟨%D1, Hw, %hD1⟩
  have hD1pre : D1 ++ m.Command.flatMap state.Command.enc <+: E0 := by
    subst hD1
    u1_buf_norm
    u1_prefix_tac
  wp_auto
  ihave HL : (∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗ "Hs" ∷ s ↦*{dq} m.Command ∗
      "Hw" ∷ wst bw wr J Q sent pend err
        (D1 ++ (m.Command.take (sint.nat iv)).flatMap state.Command.enc) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ m.Command.length⌝ : IProp GF) $$ [i Hs Hw]
  · iexists W64 0
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil, List.append_nil]
    iframe
    ipureintro; exact ⟨by decide, by rw [sint_Z_W64_0]; omega⟩
  wp_for HL
  wp_if_destruct
  · obtain ⟨hi0, hil⟩ := Hi
    have hlt : sint.Z iv < m.Command.length := by
      simp only [hlenZ] at Hif; simpa using Hif
    rw [if_pos ⟨hi0, by rw [hslen, hlenZ]; exact hlt⟩]
    obtain ⟨c, hc⟩ : ∃ c, m.Command[(sint.Z iv).toNat]? = some c :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    icases ownSlice_elem_acc (sint.Z iv) c s dq m.Command hi0 hc $$ Hs with ⟨He, Hback⟩
    wp_auto
    have hnat : sint.nat iv = (sint.Z iv).toNat := rfl
    wp_apply (state.Command.wp_Marshal_gen (E0 := E0)) $$ [Hw He] as ⟨Hw, He⟩
    · iframe Hwr HQ Hw He
      ipureintro
      rw [List.append_assoc, flatMap_take_succ _ _ _ _ (by rw [hnat]; exact hc)]
      exact List.IsPrefix.trans ((List.prefix_append_right_inj _).mpr (flatMap_take_prefix _ _ _))
        hD1pre
    ihave Hs := Hback $$ %c He
    rw [list_set_lookup_self _ _ _ hc]
    wp_for_post
    iframe
    iexists iv + W64 1
    have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
    have hnat1 : sint.nat (iv + W64 1) = sint.nat iv + 1 := by
      show (sint.Z (iv + W64 1)).toNat = (sint.Z iv).toNat + 1
      rw [hiv1]; omega
    rw [hnat1, ← flatMap_take_succ _ _ _ _ (by rw [hnat]; exact hc)]
    simp only [List.append_assoc]
    iframe
    ipureintro
    rw [hiv1]; omega
  obtain ⟨hi0, hil⟩ := Hi
  have hall : sint.nat iv = m.Command.length := by
    simp only [hlenZ] at Hif
    have : ¬ sint.Z iv < m.Command.length := by simpa using Hif
    show (sint.Z iv).toNat = _
    omega
  rw [hall, List.take_length]
  subst hD1
  u1_marshal_auto
  iapply HΦ
  isplitl [Hw]
  · iapply wst_congr _ _ _ _ _ _ _ _ _ (by u1_enc_norm <;> rfl) $$ Hw
  iunfold EAccept.own
  iexists s
  iframe Hs
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, EAccept.goVal]
  iframe

theorem EAccept.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : EAccept.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ EAccept.enc m) ∗
        EAccept.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.EAccept.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (EAccept.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (EAccept.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (EAccept.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        EAccept.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen EAccept.wp_Marshal_gen

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ECommit.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : ECommit.Msg) (bw : Loc)
    (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface)
    (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ ECommit.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ ECommit.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ECommit.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ ECommit.enc m) ∗ ECommit.own t dq m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  iunfold ECommit.own at Ht
  icases Ht with ⟨%s, Ht, Hs⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  simp only [ECommit.goVal]
  iStructNamed Ht
  irename : ("_" ∷ True : IProp GF) => Htrue
  iclear Htrue
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  u1_marshal_auto
  have hs63 : sint.Z s.len < 2 ^ 63 := by word
  have hlen63 : m.Command.length < 2 ^ 63 := by
    have h1 := Hsl.1; have h2 := Hsl.2
    have : ((sint.nat s.len : Nat) : Int) = sint.Z s.len := Int.toNat_of_nonneg h2
    omega
  have hslen : s.len = W64 (m.Command.length : Int) := by
    apply BitVec.eq_of_toInt_eq
    show sint.Z s.len = sint.Z (W64 (m.Command.length : Int))
    rw [EtcdGrove.bufio.sint_Z_W64_length (by omega)]
    have h1 := Hsl.1; have h2 := Hsl.2
    have : ((sint.nat s.len : Nat) : Int) = sint.Z s.len := Int.toNat_of_nonneg h2
    omega
  have hvl := varintEnc_len_le m.Command.length hlen63
  have hlenZ : sint.Z (W64 (m.Command.length : Int)) = m.Command.length :=
    EtcdGrove.bufio.sint_Z_W64_length (by omega)
  rw [hslen]
  simp only [sint_Z_W64_0, go.arrayIndexRef_0, w64_sub_zero]
  wp_apply wp_PutVarint b_ptr (W64 24) 24 _ _ rfl (by omega) (by
    have : sint.nat (W64 24) = 24 := rfl
    omega) $$ [$b] as b
  have hvZ : sint.Z (W64 ((varintEnc (sint.Z (W64 (m.Command.length : Int)))).length : Int)) =
      (varintEnc (sint.Z (W64 (m.Command.length : Int)))).length := EtcdGrove.bufio.sint_Z_W64_length (by omega)
  wp_if_destruct
  rotate_left
  · exfalso; apply Hif; rw [hvZ, sint_Z_W64_0]; omega
  simp only [sint_Z_W64_0, go.arrayIndexRef_0, w64_sub_zero]
  rw [if_pos ⟨by omega, by rw [hvZ]; omega, by rw [hvZ]; omega⟩]
  wp_auto
  have hvN : sint.nat (W64 ((varintEnc (sint.Z (W64 (m.Command.length : Int)))).length : Int)) =
      (varintEnc (sint.Z (W64 (m.Command.length : Int)))).length := by
    simp only [sint.nat, hvZ]; simp
  wp_apply (wp_wire_Write_arr (E0 := E0)) $$ [Hw b] as %nn2 %e2 ⟨Hw, b⟩
  · iframe Hwr HQ Hw b
    ipureintro
    rw [hvN, List.take_left' rfl]
    refine ⟨?_, by rw [hvZ]; omega, by rw [hvZ]; omega, by rw [hvZ]; have : sint.Z (W64 24) = 24 := rfl; omega⟩
    u1_buf_norm
    u1_prefix_tac
  rw [hvN, List.take_left' rfl]
  icases wst_name _ _ _ _ _ _ _ _ $$ Hw with ⟨%D1, Hw, %hD1⟩
  have hD1pre : D1 ++ m.Command.flatMap state.Command.enc <+: E0 := by
    subst hD1
    u1_buf_norm
    u1_prefix_tac
  ihave HL : (∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗ "Hs" ∷ s ↦*{dq} m.Command ∗
      "Hw" ∷ wst bw wr J Q sent pend err
        (D1 ++ (m.Command.take (sint.nat iv)).flatMap state.Command.enc) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ m.Command.length⌝ : IProp GF) $$ [i Hs Hw]
  · iexists W64 0
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil, List.append_nil]
    iframe
    ipureintro; exact ⟨by decide, by rw [sint_Z_W64_0]; omega⟩
  wp_for HL
  wp_if_destruct
  · obtain ⟨hi0, hil⟩ := Hi
    have hlt : sint.Z iv < m.Command.length := by
      simp only [hlenZ] at Hif; simpa using Hif
    rw [if_pos ⟨hi0, by rw [hslen, hlenZ]; exact hlt⟩]
    obtain ⟨c, hc⟩ : ∃ c, m.Command[(sint.Z iv).toNat]? = some c :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    icases ownSlice_elem_acc (sint.Z iv) c s dq m.Command hi0 hc $$ Hs with ⟨He, Hback⟩
    wp_auto
    have hnat : sint.nat iv = (sint.Z iv).toNat := rfl
    wp_apply (state.Command.wp_Marshal_gen (E0 := E0)) $$ [Hw He] as ⟨Hw, He⟩
    · iframe Hwr HQ Hw He
      ipureintro
      rw [List.append_assoc, flatMap_take_succ _ _ _ _ (by rw [hnat]; exact hc)]
      exact List.IsPrefix.trans ((List.prefix_append_right_inj _).mpr (flatMap_take_prefix _ _ _))
        hD1pre
    ihave Hs := Hback $$ %c He
    rw [list_set_lookup_self _ _ _ hc]
    wp_for_post
    iframe
    iexists iv + W64 1
    have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
    have hnat1 : sint.nat (iv + W64 1) = sint.nat iv + 1 := by
      show (sint.Z (iv + W64 1)).toNat = (sint.Z iv).toNat + 1
      rw [hiv1]; omega
    rw [hnat1, ← flatMap_take_succ _ _ _ _ (by rw [hnat]; exact hc)]
    simp only [List.append_assoc]
    iframe
    ipureintro
    rw [hiv1]; omega
  obtain ⟨hi0, hil⟩ := Hi
  have hall : sint.nat iv = m.Command.length := by
    simp only [hlenZ] at Hif
    have : ¬ sint.Z iv < m.Command.length := by simpa using Hif
    show (sint.Z iv).toNat = _
    omega
  rw [hall, List.take_length]
  subst hD1
  ihave b := array_explicit _ _ _ _ $$ b
  simp only [Int.reduceToNat, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, List.singleton_append]
  u1_marshal_auto
  iapply HΦ
  isplitl [Hw]
  · iapply wst_congr _ _ _ _ _ _ _ _ _ (by u1_enc_norm <;> rfl) $$ Hw
  iunfold ECommit.own
  iexists s
  iframe Hs
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, ECommit.goVal]
  iframe

theorem ECommit.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : ECommit.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ ECommit.enc m) ∗
        ECommit.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ECommit.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (ECommit.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (ECommit.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (ECommit.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        ECommit.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen ECommit.wp_Marshal_gen

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem TryPreAccept.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : TryPreAccept.Msg) (bw : Loc)
    (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface)
    (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ TryPreAccept.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ TryPreAccept.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.TryPreAccept.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ TryPreAccept.enc m) ∗ TryPreAccept.own t dq m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  iunfold TryPreAccept.own at Ht
  icases Ht with ⟨%s, Ht, Hs⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  simp only [TryPreAccept.goVal]
  iStructNamed Ht
  irename : ("_" ∷ True : IProp GF) => Htrue
  iclear Htrue
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  u1_marshal_auto
  have hs63 : sint.Z s.len < 2 ^ 63 := by word
  have hlen63 : m.Command.length < 2 ^ 63 := by
    have h1 := Hsl.1; have h2 := Hsl.2
    have : ((sint.nat s.len : Nat) : Int) = sint.Z s.len := Int.toNat_of_nonneg h2
    omega
  have hslen : s.len = W64 (m.Command.length : Int) := by
    apply BitVec.eq_of_toInt_eq
    show sint.Z s.len = sint.Z (W64 (m.Command.length : Int))
    rw [EtcdGrove.bufio.sint_Z_W64_length (by omega)]
    have h1 := Hsl.1; have h2 := Hsl.2
    have : ((sint.nat s.len : Nat) : Int) = sint.Z s.len := Int.toNat_of_nonneg h2
    omega
  have hvl := varintEnc_len_le m.Command.length hlen63
  have hlenZ : sint.Z (W64 (m.Command.length : Int)) = m.Command.length :=
    EtcdGrove.bufio.sint_Z_W64_length (by omega)
  rw [hslen]
  simp only [sint_Z_W64_0, go.arrayIndexRef_0, w64_sub_zero]
  wp_apply wp_PutVarint b_ptr (W64 24) 24 _ _ rfl (by omega) (by
    have : sint.nat (W64 24) = 24 := rfl
    omega) $$ [$b] as b
  have hvZ : sint.Z (W64 ((varintEnc (sint.Z (W64 (m.Command.length : Int)))).length : Int)) =
      (varintEnc (sint.Z (W64 (m.Command.length : Int)))).length := EtcdGrove.bufio.sint_Z_W64_length (by omega)
  wp_if_destruct
  rotate_left
  · exfalso; apply Hif; rw [hvZ, sint_Z_W64_0]; omega
  simp only [sint_Z_W64_0, go.arrayIndexRef_0, w64_sub_zero]
  rw [if_pos ⟨by omega, by rw [hvZ]; omega, by rw [hvZ]; omega⟩]
  wp_auto
  have hvN : sint.nat (W64 ((varintEnc (sint.Z (W64 (m.Command.length : Int)))).length : Int)) =
      (varintEnc (sint.Z (W64 (m.Command.length : Int)))).length := by
    simp only [sint.nat, hvZ]; simp
  wp_apply (wp_wire_Write_arr (E0 := E0)) $$ [Hw b] as %nn2 %e2 ⟨Hw, b⟩
  · iframe Hwr HQ Hw b
    ipureintro
    rw [hvN, List.take_left' rfl]
    refine ⟨?_, by rw [hvZ]; omega, by rw [hvZ]; omega, by rw [hvZ]; have : sint.Z (W64 24) = 24 := rfl; omega⟩
    u1_buf_norm
    u1_prefix_tac
  rw [hvN, List.take_left' rfl]
  icases wst_name _ _ _ _ _ _ _ _ $$ Hw with ⟨%D1, Hw, %hD1⟩
  have hD1pre : D1 ++ m.Command.flatMap state.Command.enc <+: E0 := by
    subst hD1
    u1_buf_norm
    u1_prefix_tac
  ihave HL : (∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗ "Hs" ∷ s ↦*{dq} m.Command ∗
      "Hw" ∷ wst bw wr J Q sent pend err
        (D1 ++ (m.Command.take (sint.nat iv)).flatMap state.Command.enc) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ m.Command.length⌝ : IProp GF) $$ [i Hs Hw]
  · iexists W64 0
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil, List.append_nil]
    iframe
    ipureintro; exact ⟨by decide, by rw [sint_Z_W64_0]; omega⟩
  wp_for HL
  wp_if_destruct
  · obtain ⟨hi0, hil⟩ := Hi
    have hlt : sint.Z iv < m.Command.length := by
      simp only [hlenZ] at Hif; simpa using Hif
    rw [if_pos ⟨hi0, by rw [hslen, hlenZ]; exact hlt⟩]
    obtain ⟨c, hc⟩ : ∃ c, m.Command[(sint.Z iv).toNat]? = some c :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    icases ownSlice_elem_acc (sint.Z iv) c s dq m.Command hi0 hc $$ Hs with ⟨He, Hback⟩
    wp_auto
    have hnat : sint.nat iv = (sint.Z iv).toNat := rfl
    wp_apply (state.Command.wp_Marshal_gen (E0 := E0)) $$ [Hw He] as ⟨Hw, He⟩
    · iframe Hwr HQ Hw He
      ipureintro
      rw [List.append_assoc, flatMap_take_succ _ _ _ _ (by rw [hnat]; exact hc)]
      exact List.IsPrefix.trans ((List.prefix_append_right_inj _).mpr (flatMap_take_prefix _ _ _))
        hD1pre
    ihave Hs := Hback $$ %c He
    rw [list_set_lookup_self _ _ _ hc]
    wp_for_post
    iframe
    iexists iv + W64 1
    have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
    have hnat1 : sint.nat (iv + W64 1) = sint.nat iv + 1 := by
      show (sint.Z (iv + W64 1)).toNat = (sint.Z iv).toNat + 1
      rw [hiv1]; omega
    rw [hnat1, ← flatMap_take_succ _ _ _ _ (by rw [hnat]; exact hc)]
    simp only [List.append_assoc]
    iframe
    ipureintro
    rw [hiv1]; omega
  obtain ⟨hi0, hil⟩ := Hi
  have hall : sint.nat iv = m.Command.length := by
    simp only [hlenZ] at Hif
    have : ¬ sint.Z iv < m.Command.length := by simpa using Hif
    show (sint.Z iv).toNat = _
    omega
  rw [hall, List.take_length]
  subst hD1
  ihave b := array_explicit _ _ _ _ $$ b
  simp only [Int.reduceToNat, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, List.singleton_append]
  u1_marshal_auto
  iapply HΦ
  isplitl [Hw]
  · iapply wst_congr _ _ _ _ _ _ _ _ _ (by u1_enc_norm <;> rfl) $$ Hw
  iunfold TryPreAccept.own
  iexists s
  iframe Hs
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, TryPreAccept.goVal]
  iframe

theorem TryPreAccept.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : TryPreAccept.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ TryPreAccept.enc m) ∗
        TryPreAccept.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.TryPreAccept.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (TryPreAccept.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (TryPreAccept.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (TryPreAccept.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        TryPreAccept.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen TryPreAccept.wp_Marshal_gen

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PrepareReply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : PrepareReply.Msg) (bw : Loc)
    (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface)
    (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ PrepareReply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ PrepareReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PrepareReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ PrepareReply.enc m) ∗ PrepareReply.own t dq m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  iunfold PrepareReply.own at Ht
  icases Ht with ⟨%s, Ht, Hs⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  simp only [PrepareReply.goVal]
  iStructNamed Ht
  irename : ("_" ∷ True : IProp GF) => Htrue
  iclear Htrue
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  u1_marshal_auto
  have hs63 : sint.Z s.len < 2 ^ 63 := by word
  have hlen63 : m.Command.length < 2 ^ 63 := by
    have h1 := Hsl.1; have h2 := Hsl.2
    have : ((sint.nat s.len : Nat) : Int) = sint.Z s.len := Int.toNat_of_nonneg h2
    omega
  have hslen : s.len = W64 (m.Command.length : Int) := by
    apply BitVec.eq_of_toInt_eq
    show sint.Z s.len = sint.Z (W64 (m.Command.length : Int))
    rw [EtcdGrove.bufio.sint_Z_W64_length (by omega)]
    have h1 := Hsl.1; have h2 := Hsl.2
    have : ((sint.nat s.len : Nat) : Int) = sint.Z s.len := Int.toNat_of_nonneg h2
    omega
  have hvl := varintEnc_len_le m.Command.length hlen63
  have hlenZ : sint.Z (W64 (m.Command.length : Int)) = m.Command.length :=
    EtcdGrove.bufio.sint_Z_W64_length (by omega)
  rw [hslen]
  simp only [sint_Z_W64_0, go.arrayIndexRef_0, w64_sub_zero]
  wp_apply wp_PutVarint b_ptr (W64 24) 24 _ _ rfl (by omega) (by
    have : sint.nat (W64 24) = 24 := rfl
    omega) $$ [$b] as b
  have hvZ : sint.Z (W64 ((varintEnc (sint.Z (W64 (m.Command.length : Int)))).length : Int)) =
      (varintEnc (sint.Z (W64 (m.Command.length : Int)))).length := EtcdGrove.bufio.sint_Z_W64_length (by omega)
  wp_if_destruct
  rotate_left
  · exfalso; apply Hif; rw [hvZ, sint_Z_W64_0]; omega
  simp only [sint_Z_W64_0, go.arrayIndexRef_0, w64_sub_zero]
  rw [if_pos ⟨by omega, by rw [hvZ]; omega, by rw [hvZ]; omega⟩]
  wp_auto
  have hvN : sint.nat (W64 ((varintEnc (sint.Z (W64 (m.Command.length : Int)))).length : Int)) =
      (varintEnc (sint.Z (W64 (m.Command.length : Int)))).length := by
    simp only [sint.nat, hvZ]; simp
  wp_apply (wp_wire_Write_arr (E0 := E0)) $$ [Hw b] as %nn2 %e2 ⟨Hw, b⟩
  · iframe Hwr HQ Hw b
    ipureintro
    rw [hvN, List.take_left' rfl]
    refine ⟨?_, by rw [hvZ]; omega, by rw [hvZ]; omega, by rw [hvZ]; have : sint.Z (W64 24) = 24 := rfl; omega⟩
    u1_buf_norm
    u1_prefix_tac
  rw [hvN, List.take_left' rfl]
  icases wst_name _ _ _ _ _ _ _ _ $$ Hw with ⟨%D1, Hw, %hD1⟩
  have hD1pre : D1 ++ m.Command.flatMap state.Command.enc <+: E0 := by
    subst hD1
    u1_buf_norm
    u1_prefix_tac
  ihave HL : (∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗ "Hs" ∷ s ↦*{dq} m.Command ∗
      "Hw" ∷ wst bw wr J Q sent pend err
        (D1 ++ (m.Command.take (sint.nat iv)).flatMap state.Command.enc) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ m.Command.length⌝ : IProp GF) $$ [i Hs Hw]
  · iexists W64 0
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil, List.append_nil]
    iframe
    ipureintro; exact ⟨by decide, by rw [sint_Z_W64_0]; omega⟩
  wp_for HL
  wp_if_destruct
  · obtain ⟨hi0, hil⟩ := Hi
    have hlt : sint.Z iv < m.Command.length := by
      simp only [hlenZ] at Hif; simpa using Hif
    rw [if_pos ⟨hi0, by rw [hslen, hlenZ]; exact hlt⟩]
    obtain ⟨c, hc⟩ : ∃ c, m.Command[(sint.Z iv).toNat]? = some c :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    icases ownSlice_elem_acc (sint.Z iv) c s dq m.Command hi0 hc $$ Hs with ⟨He, Hback⟩
    wp_auto
    have hnat : sint.nat iv = (sint.Z iv).toNat := rfl
    wp_apply (state.Command.wp_Marshal_gen (E0 := E0)) $$ [Hw He] as ⟨Hw, He⟩
    · iframe Hwr HQ Hw He
      ipureintro
      rw [List.append_assoc, flatMap_take_succ _ _ _ _ (by rw [hnat]; exact hc)]
      exact List.IsPrefix.trans ((List.prefix_append_right_inj _).mpr (flatMap_take_prefix _ _ _))
        hD1pre
    ihave Hs := Hback $$ %c He
    rw [list_set_lookup_self _ _ _ hc]
    wp_for_post
    iframe
    iexists iv + W64 1
    have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
    have hnat1 : sint.nat (iv + W64 1) = sint.nat iv + 1 := by
      show (sint.Z (iv + W64 1)).toNat = (sint.Z iv).toNat + 1
      rw [hiv1]; omega
    rw [hnat1, ← flatMap_take_succ _ _ _ _ (by rw [hnat]; exact hc)]
    simp only [List.append_assoc]
    iframe
    ipureintro
    rw [hiv1]; omega
  obtain ⟨hi0, hil⟩ := Hi
  have hall : sint.nat iv = m.Command.length := by
    simp only [hlenZ] at Hif
    have : ¬ sint.Z iv < m.Command.length := by simpa using Hif
    show (sint.Z iv).toNat = _
    omega
  rw [hall, List.take_length]
  subst hD1
  ihave b := array_explicit _ _ _ _ $$ b
  simp only [Int.reduceToNat, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, List.singleton_append]
  u1_marshal_auto
  iapply HΦ
  isplitl [Hw]
  · iapply wst_congr _ _ _ _ _ _ _ _ _ (by u1_enc_norm <;> rfl) $$ Hw
  iunfold PrepareReply.own
  iexists s
  iframe Hs
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, PrepareReply.goVal]
  iframe

theorem PrepareReply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : PrepareReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ PrepareReply.enc m) ∗
        PrepareReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PrepareReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (PrepareReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (PrepareReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (PrepareReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        PrepareReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen PrepareReply.wp_Marshal_gen

end gryffproto
end proofs
end Perennial.gryff.wire
