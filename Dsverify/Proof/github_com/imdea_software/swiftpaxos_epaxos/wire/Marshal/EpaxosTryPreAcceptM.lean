/-
`epaxos.TryPreAccept`'s `Marshal` (internal to the wire package).
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

theorem epaxos.TryPreAccept.Marshal.wp (l : Loc) (dq dq1 dq2 : DFrac)
    (m : model.TryPreAccept) :
    marshalTriple (pkgInit_epaxos (GF := GF)) (l @!! go.GoType.PointerType epaxos.TryPreAccept.ty @!! go!"Marshal")
      (ownTryPreAccept l m dq dq1 dq2) (model.encTryPreAccept m) := by
  intro bw wr sent pend err
  wp_start as ⟨Hown, HQ, Hl⟩
  ihave Hw := wprog_start bw wr sent pend err (model.encTryPreAccept m) $$ [$Hown $HQ]
  iunfold ownTryPreAccept at Hl
  icases Hl with ⟨%cs, %ds, Hl, Hcs, Hds⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨LeaderId, Replica, Instance, Ballot, Command, Seq, Deps, -⟩
  wp_auto
  ihave Hb := zero_array b_ptr (W64 16) 16 rfl 16 rfl $$ b
  ihave ⟨Hbs, Hback⟩ := array_slice_acc b_ptr _ (W64 16) (W64 16) 16 rfl
    (by simp only [List.length_replicate]; rfl) (by simp) (by simp) $$ Hb
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  wbytes
  wp_apply wp_wprog_Write bw wr sent pend err [] _
    (u32Le m.leaderId ++ (u32Le m.replica ++ (u32Le m.inst ++ u32Le m.ballot)))
    (encCmds m.command ++ u32Le m.seq ++ encDeps m.deps) _ _
    (by simp [encTryPreAccept]) $$ [$Hpkg2 $Hw $Hbs] as %nn %e ⟨Hbs, Hw⟩
  ihave Hb := Hback $$ %_ %(by simp [u32Le_length]) Hbs
  ihave Harr := arrBytes_intro b_ptr (W64 16) _ (by blen) $$ Hb
  (try wp_auto)
  -- the commands' count
  iunfold ownCmds at Hcs
  icases Hcs with ⟨%vs, Hcs, %Hvs, Hcl⟩
  ihave %hcsl := ownSlice_len _ _ _ $$ Hcs
  have hZ := slice_len_int _ _ hcsl
  obtain ⟨hve, hlen63⟩ := slice_len_varint cs m.command.length (by rw [← Hvs]; exact hZ)
  wvarint cs.len (encCmds m.command ++ u32Le m.seq ++ encDeps m.deps)
    ((m.command.map encCommand).flatten ++ u32Le m.seq ++ encDeps m.deps)
    (by simp [encCmds, hve])
  -- the commands
  ihave HL : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 (j : Int) ∗
      "Hw" ∷ wprog bw wr sent pend err
        ([] ++ (u32Le m.leaderId ++ (u32Le m.replica ++ (u32Le m.inst ++ u32Le m.ballot))) ++
          varintEnc cs.len ++ ((m.command.take j).map encCommand).flatten)
        (((m.command.drop j).map encCommand).flatten ++ u32Le m.seq ++ encDeps m.deps) ∗
      "%Hj" ∷ ⌜j ≤ m.command.length⌝ : IProp GF) $$ [i Hw]
  · iexists 0
    simp
    iframe
  icases Hcl with #Hcl
  wp_for HL
  have hjZ : sint.Z (W64 (j : Int)) = j := sint_Z_W64_length (by omega)
  by_cases hlt : j < m.command.length
  · rw [decide_eq_true (by rw [hjZ]; omega)]
    simp only [ite_true]
    wp_auto
    rw [show sint.Z (W64 (j : Int)) = (j : Int) from hjZ]
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
    obtain ⟨c, hc⟩ : ∃ c, vs[j]? = some c :=
      ⟨vs[j]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    ihave ⟨Hc, Hcback⟩ := ownSlice_elem_acc (j : Int) c cs dq1 vs (by omega) (by simpa using hc) $$ Hcs
    ihave Hcj := BigSepL.bigSepL_lookup hc $$ Hcl
    icases Hcj with ⟨%wc, %hwc, #Hcok⟩
    wp_auto
    ihave #Hst : pkgInit_state $$ []
    · iPkgInit
    have hdrop : (m.command.drop j) = wc :: m.command.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by omega)]
      congr 1
      rw [List.getElem?_eq_getElem (by omega)] at hwc; exact Option.some.inj hwc
    have htake : m.command.take (j + 1) = m.command.take j ++ [wc] := by
      rw [List.take_succ, hwc]; rfl
    wp_apply wp_wprog_marshal _ _ _ _ (state.Command.Marshal.spec_holds _ dq1 c wc) bw wr
      sent pend err _ _ (((m.command.drop (j + 1)).map encCommand).flatten ++ u32Le m.seq ++
        encDeps m.deps) (by rw [hdrop]; simp) $$ [$Hst $Hpkg2 $Hw $Hc $Hcok] as ⟨⟨Hc, -⟩, Hw⟩
    ihave Hcs := Hcback $$ Hc
    rw [list_set_lookup_self _ _ _ (by simpa using hc)]
    wp_for_post
    rw [w64_succ]
    iframe
    iexists j + 1
    rw [htake]
    simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] at *
    iframe
    ipureintro; omega
  · rw [decide_eq_false (by rw [hjZ]; omega)]
    have hjn : j = m.command.length := by omega
    subst hjn
    simp only [Bool.false_eq_true, ↓reduceIte, ]
    simp only [List.take_length, List.drop_length, List.map_nil, List.flatten_nil, List.nil_append]
    ihave ⟨%L4, %hL4, Hbs, Hback⟩ := arrBytes_slice b_ptr (W64 4) (W64 16) 4 rfl (by decide)
      (by decide) $$ Harr
    obtain ⟨a0, a1, a2, a3, rfl⟩ := list4 L4 hL4
    wp_auto
    wstore; wstore; wstore; wstore
    wbytes
    wp_apply wp_wprog_Write bw wr sent pend err _ _ (u32Le m.seq) (encDeps m.deps) _ _
      (by simp) $$ [$Hpkg2 $Hw $Hbs] as %nn2 %e2 ⟨Hbs, Hw⟩
    ihave Harr := Hback $$ %_ %(by simp [u32Le_length]) Hbs
    (try wp_auto)
    -- the dependencies' count
    iunfold ownDeps at Hds
    ihave %hdsl := ownSlice_len _ _ _ $$ Hds
    have hdZ := slice_len_int _ _ hdsl
    obtain ⟨hvd, hdlen63⟩ := slice_len_varint ds m.deps.length hdZ
    wvarint ds.len (encDeps m.deps) ((m.deps.map u32Le).flatten) (by simp [encDeps, hvd])
    ihave HL : (∃ (j : Nat) (sv : GoSlice) (tv : w32), "i" ∷ i_ptr ↦ W64 (j : Int) ∗
        "bs" ∷ bs_ptr ↦ sv ∗ "tmp32" ∷ tmp32_ptr ↦ tv ∗ "Harr" ∷ arrBytes b_ptr (W64 16) ∗
        "Hw" ∷ wprog bw wr sent pend err
          ([] ++ (u32Le m.leaderId ++ (u32Le m.replica ++ (u32Le m.inst ++ u32Le m.ballot))) ++
            varintEnc cs.len ++ (m.command.map encCommand).flatten ++ u32Le m.seq ++
            varintEnc ds.len ++ ((m.deps.take j).map u32Le).flatten)
          (((m.deps.drop j).map u32Le).flatten) ∗
        "%Hj" ∷ ⌜j ≤ m.deps.length⌝ : IProp GF) $$ [i bs tmp32 Harr Hw]
    · iexists 0, _, _
      simp
      iframe
    wp_for HL
    have hjZ : sint.Z (W64 (j : Int)) = j := sint_Z_W64_length (by omega)
    by_cases hlt : j < m.deps.length
    · rw [decide_eq_true (by rw [hjZ]; omega)]
      simp only [ite_true]
      ihave ⟨%L4, %hL4, Hbs, Hback⟩ := arrBytes_slice b_ptr (W64 4) (W64 16) 4 rfl (by decide)
        (by decide) $$ Harr
      obtain ⟨a0, a1, a2, a3, rfl⟩ := list4 L4 hL4
      wp_auto
      rw [show sint.Z (W64 (j : Int)) = (j : Int) from hjZ]
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
      have hdj : m.deps[j]? = some (m.deps[j]'hlt) := List.getElem?_eq_getElem hlt
      wp_apply wp_load_slice_index ds (j : Int) _ dq2 (m.deps[j]'hlt) (by omega) $$ [Hds] as Hds
      · iframe Hds; ipureintro; simpa using hdj
      (try wp_auto)
      wstore; wstore; wstore; wstore
      wbytes
      have hdrop : (m.deps.drop j) = m.deps[j] :: m.deps.drop (j + 1) :=
        List.drop_eq_getElem_cons (by omega)
      have htake : m.deps.take (j + 1) = m.deps.take j ++ [m.deps[j]] := by
        rw [List.take_succ, hdj]; rfl
      wp_apply wp_wprog_Write bw wr sent pend err _ ((m.deps.drop j).map u32Le).flatten
        (u32Le m.deps[j])
        ((m.deps.drop (j + 1)).map u32Le).flatten _ _ (by rw [hdrop, List.map_cons, List.flatten_cons])
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
        List.append_nil]
      iapply HΦ
      isplitl [LeaderId Replica Instance Ballot Command Seq Deps Hcs Hds]
      · iunfold ownTryPreAccept
        iexists cs, ds
        isplitl [LeaderId Replica Instance Ballot Command Seq Deps]
        · iapply typedPointsto_combine _ _ _ Hnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe LeaderId Replica Instance Ballot Command Seq Deps
        isplitl [Hcs]
        · iunfold ownCmds
          iexists vs
          iframe Hcs Hcl
          ipureintro; exact Hvs
        iunfold ownDeps
        iexact Hds
      iapply wprog_finish _ _ _ _ _ _ _ (by simp [encTryPreAccept, encCmds, encDeps, hve, hvd])
        $$ Hw

theorem epaxos.Marshal.spec_tryPreAccept : epaxos.Marshal.spec (GF := GF) MsgKind.tryPreAccept := by
  intro l dq dq1 dq2 m hk
  cases m <;> simp [Msg.kind] at hk
  exact epaxos.TryPreAccept.Marshal.wp l dq dq1 dq2 _

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
