/-
`epaxos.PreAcceptReply`'s `Marshal` (internal to the wire package).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosCommon

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [bufio.Assumptions] [io.Assumptions]

set_option goose.wp.extras true

theorem epaxos.PreAcceptReply.Marshal.wp (l : Loc) (dq dq1 dq2 : DFrac)
    (m : model.PreAcceptReply) :
    marshalTriple (pkgInit_epaxos (GF := GF)) (l @!! go.GoType.PointerType epaxos.PreAcceptReply.ty @!! go!"Marshal")
      (ownPreAcceptReply l m dq dq1 dq2) (model.encPreAcceptReply m) := by
  intro bw wr sent pend err
  wp_start as ⟨Hown, HQ, Hl⟩
  ihave Hw := wprog_start bw wr sent pend err (model.encPreAcceptReply m) $$ [$Hown $HQ]
  iunfold ownPreAcceptReply at Hl
  icases Hl with ⟨%ds, %cds, Hl, Hds, Hcds⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨Replica, Instance, Ballot, VBallot, Seq, Deps, CommittedDeps, Status, -⟩
  wp_auto
  ihave Hb := zero_array b_ptr (W64 21) 21 rfl 21 rfl $$ b
  ihave ⟨Hbs, Hback⟩ := array_slice_acc b_ptr _ (W64 21) (W64 21) 21 rfl
    (by simp only [List.length_replicate]; rfl) (by simp) (by simp) $$ Hb
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  wstore; wstore; wstore; wstore; wstore
  wbytes
  wp_apply wp_wprog_Write bw wr sent pend err [] _
    (u32Le m.replica ++ (u32Le m.inst ++ (u32Le m.ballot ++ (u32Le m.vballot ++ (u32Le m.seq ++ [m.status])))))
    (encDeps m.deps ++ encDeps m.committedDeps) _ _
    (by simp [encPreAcceptReply]) $$ [$Hpkg2 $Hw $Hbs] as %nn %e ⟨Hbs, Hw⟩
  ihave Hb := Hback $$ %_ %(by simp [u32Le_length]) Hbs
  ihave Harr := arrBytes_intro b_ptr (W64 21) _ (by blen) $$ Hb
  (try wp_auto)
  -- the dependencies' count
  iunfold ownDeps at Hds Hcds
  ihave %hdsl := ownSlice_len _ _ _ $$ Hds
  have hdZ := slice_len_int _ _ hdsl
  obtain ⟨hvd, hdlen63⟩ := slice_len_varint ds m.deps.length hdZ
  wvarintN 21 ds.len (encDeps m.deps ++ encDeps m.committedDeps)
    ((m.deps.map u32Le).flatten ++ encDeps m.committedDeps) (by simp [encDeps, hvd])
  ihave HL1 : (∃ (j : Nat) (sv : GoSlice) (tv : w32), "i" ∷ i_ptr ↦ W64 (j : Int) ∗
      "bs" ∷ bs_ptr ↦ sv ∗ "tmp32" ∷ tmp32_ptr ↦ tv ∗ "Harr" ∷ arrBytes b_ptr (W64 21) ∗
      "Hw" ∷ wprog bw wr sent pend err
        ([] ++ (u32Le m.replica ++ (u32Le m.inst ++ (u32Le m.ballot ++ (u32Le m.vballot ++ (u32Le m.seq ++ [m.status]))))) ++ varintEnc ds.len ++ ((m.deps.take j).map u32Le).flatten)
        (((m.deps.drop j).map u32Le).flatten ++ encDeps m.committedDeps) ∗
      "%Hj" ∷ ⌜j ≤ m.deps.length⌝ : IProp GF) $$ [i bs tmp32 Harr Hw]
  · iexists 0, _, _
    simp
    iframe
  wp_for HL1
  have hjZ : sint.Z (W64 (j : Int)) = j := sint_Z_W64_length (by omega)
  by_cases hlt : j < m.deps.length
  · rw [decide_eq_true (by rw [hjZ]; omega)]
    simp only [ite_true]
    ihave ⟨%L4, %hL4, Hbs, Hback⟩ := arrBytes_slice b_ptr (W64 4) (W64 21) 4 rfl (by decide)
      (by decide) $$ Harr
    obtain ⟨a0, a1, a2, a3, rfl⟩ := list4 L4 hL4
    wp_auto
    rw [show sint.Z (W64 (j : Int)) = (j : Int) from hjZ]
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
    have hdj : m.deps[j]? = some (m.deps[j]'hlt) := List.getElem?_eq_getElem hlt
    wp_apply wp_load_slice_index ds (j : Int) _ dq1 (m.deps[j]'hlt) (by omega) $$ [Hds] as Hds
    · iframe Hds; ipureintro; simpa using hdj
    (try wp_auto)
    wstore; wstore; wstore; wstore
    wbytes
    have hdrop : (m.deps.drop j) = m.deps[j] :: m.deps.drop (j + 1) :=
      List.drop_eq_getElem_cons (by omega)
    have htake : m.deps.take (j + 1) = m.deps.take j ++ [m.deps[j]] := by
      rw [List.take_succ, hdj]; rfl
    wp_apply wp_wprog_Write bw wr sent pend err _ (((m.deps.drop j).map u32Le).flatten ++ encDeps m.committedDeps)
      (u32Le m.deps[j])
      (((m.deps.drop (j + 1)).map u32Le).flatten ++ encDeps m.committedDeps) _ _
      (by rw [hdrop, List.map_cons, List.flatten_cons]; try rw [List.append_assoc])
      $$ [$Hpkg2 $Hw $Hbs] as %nn3 %e3 ⟨Hbs, Hw⟩
    ihave Harr := Hback $$ %_ %(by simp [u32Le_length]) Hbs
    wp_for_post
    rw [w64_succ]
    iframe
    iexists j + 1, _, _
    rw [htake]
    simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] at *
    iframe
    ipureintro; omega
  · rw [decide_eq_false (by rw [hjZ]; omega)]
    have hjn : j = m.deps.length := by omega
    subst hjn
    simp only [Bool.false_eq_true, ↓reduceIte, ]
    wp_auto
    simp only [List.take_length, List.drop_length, List.map_nil, List.flatten_nil,
      List.nil_append]
    -- the committed dependencies' count
    ihave %hcdl := ownSlice_len _ _ _ $$ Hcds
    have hcZ := slice_len_int _ _ hcdl
    obtain ⟨hvc, hclen63⟩ := slice_len_varint cds m.committedDeps.length hcZ
    wvarintN 21 cds.len (encDeps m.committedDeps) ((m.committedDeps.map u32Le).flatten)
      (by simp [encDeps, hvc])
    ihave HL2 : (∃ (j : Nat) (sv : GoSlice) (tv : w32), "i" ∷ i_ptr ↦ W64 (j : Int) ∗
        "bs" ∷ bs_ptr ↦ sv ∗ "tmp32" ∷ tmp32_ptr ↦ tv ∗ "Harr" ∷ arrBytes b_ptr (W64 21) ∗
        "Hw" ∷ wprog bw wr sent pend err
          ([] ++ (u32Le m.replica ++ (u32Le m.inst ++ (u32Le m.ballot ++ (u32Le m.vballot ++ (u32Le m.seq ++ [m.status]))))) ++ varintEnc ds.len ++ (m.deps.map u32Le).flatten ++ varintEnc cds.len ++ ((m.committedDeps.take j).map u32Le).flatten)
          (((m.committedDeps.drop j).map u32Le).flatten) ∗
        "%Hj" ∷ ⌜j ≤ m.committedDeps.length⌝ : IProp GF) $$ [i bs tmp32 Harr Hw]
    · iexists 0, _, _
      simp
      iframe
    wp_for HL2
    have hjZ : sint.Z (W64 (j : Int)) = j := sint_Z_W64_length (by omega)
    by_cases hlt : j < m.committedDeps.length
    · rw [decide_eq_true (by rw [hjZ]; omega)]
      simp only [ite_true]
      ihave ⟨%L4, %hL4, Hbs, Hback⟩ := arrBytes_slice b_ptr (W64 4) (W64 21) 4 rfl (by decide)
        (by decide) $$ Harr
      obtain ⟨a0, a1, a2, a3, rfl⟩ := list4 L4 hL4
      wp_auto
      rw [show sint.Z (W64 (j : Int)) = (j : Int) from hjZ]
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
      have hdj : m.committedDeps[j]? = some (m.committedDeps[j]'hlt) := List.getElem?_eq_getElem hlt
      wp_apply wp_load_slice_index cds (j : Int) _ dq2 (m.committedDeps[j]'hlt) (by omega) $$ [Hcds] as Hcds
      · iframe Hcds; ipureintro; simpa using hdj
      (try wp_auto)
      wstore; wstore; wstore; wstore
      wbytes
      have hdrop : (m.committedDeps.drop j) = m.committedDeps[j] :: m.committedDeps.drop (j + 1) :=
        List.drop_eq_getElem_cons (by omega)
      have htake : m.committedDeps.take (j + 1) = m.committedDeps.take j ++ [m.committedDeps[j]] := by
        rw [List.take_succ, hdj]; rfl
      wp_apply wp_wprog_Write bw wr sent pend err _ (((m.committedDeps.drop j).map u32Le).flatten)
        (u32Le m.committedDeps[j])
        (((m.committedDeps.drop (j + 1)).map u32Le).flatten) _ _
        (by rw [hdrop, List.map_cons, List.flatten_cons]; try rw [List.append_assoc])
        $$ [$Hpkg2 $Hw $Hbs] as %nn3 %e3 ⟨Hbs, Hw⟩
      ihave Harr := Hback $$ %_ %(by simp [u32Le_length]) Hbs
      wp_for_post
      rw [w64_succ]
      iframe
      iexists j + 1, _, _
      rw [htake]
      simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] at *
      iframe
      ipureintro; omega
    · rw [decide_eq_false (by rw [hjZ]; omega)]
      have hjn : j = m.committedDeps.length := by omega
      subst hjn
      simp only [Bool.false_eq_true, ↓reduceIte, ]
      wp_auto
      simp only [List.take_length, List.drop_length, List.map_nil, List.flatten_nil,
        List.nil_append]
      iapply HΦ
      isplitl [Replica Instance Ballot VBallot Seq Deps CommittedDeps Status Hds Hcds]
      · iunfold ownPreAcceptReply
        iexists ds, cds
        isplitl [Replica Instance Ballot VBallot Seq Deps CommittedDeps Status]
        · iapply typedPointsto_combine _ _ _ Hnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe Replica Instance Ballot VBallot Seq Deps CommittedDeps Status
        isplitl [Hds]
        · iunfold ownDeps
          iexact Hds
        iunfold ownDeps
        iexact Hcds
      iapply wprog_finish _ _ _ _ _ _ _ (by simp [encPreAcceptReply, encDeps, hvd, hvc])
        $$ Hw

theorem epaxos.Marshal.spec_preAcceptReply : epaxos.Marshal.spec (GF := GF) MsgKind.preAcceptReply := by
  intro l dq dq1 dq2 m hk
  cases m <;> simp [Msg.kind] at hk
  exact epaxos.PreAcceptReply.Marshal.wp l dq dq1 dq2 _

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
