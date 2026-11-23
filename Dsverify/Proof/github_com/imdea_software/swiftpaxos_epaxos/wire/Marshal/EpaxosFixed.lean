/-
`epaxos`'s fixed-size messages (no slices): `Prepare`, `AcceptReply`, `TryPreAcceptReply`
(`Marshal` / `Unmarshal`), and every kind's `New`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Bytes
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
variable [epaxos.Assumptions] [bufio.Assumptions] [io.Assumptions]

set_option goose.wp.extras true

theorem epaxos.Prepare.Marshal.wp (l : Loc) (dq : DFrac) (m : model.Prepare) :
    marshalTriple (pkgInit_epaxos (GF := GF)) (l @!! go.GoType.PointerType epaxos.Prepare.ty @!! go!"Marshal")
      (ownPrepare l m dq) (model.encPrepare m) := by
  intro bw wr sent pend err
  wp_start as ⟨Hown, HQ, Hl⟩
  ihave Hw := wprog_start bw wr sent pend err (encPrepare m) $$ [$Hown $HQ]
  iunfold ownPrepare at Hl
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hbs := zero_array_slice b_ptr 16 16 rfl (by decide) $$ b
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  wbytes
  wp_apply wp_wprog_Write bw wr sent pend err [] (encPrepare m)
    (u32Le m.leaderId ++ (u32Le m.replica ++ (u32Le m.inst ++ u32Le m.ballot))) [] _ _
    (by simp [encPrepare]) $$ [$Hpkg2 $Hw $Hbs] as %nn %e ⟨Hbs, Hw⟩
  iapply HΦ
  isplitl [LeaderId Replica Instance Ballot]
  · iunfold ownPrepare
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe LeaderId Replica Instance Ballot
  iapply wprog_finish _ _ _ _ _ _ _ (by simp [encPrepare]) $$ Hw

theorem epaxos.AcceptReply.Marshal.wp (l : Loc) (dq : DFrac) (m : model.AcceptReply) :
    marshalTriple (pkgInit_epaxos (GF := GF))
      (l @!! go.GoType.PointerType epaxos.AcceptReply.ty @!! go!"Marshal")
      (ownAcceptReply l m dq) (model.encAcceptReply m) := by
  intro bw wr sent pend err
  wp_start as ⟨Hown, HQ, Hl⟩
  ihave Hw := wprog_start bw wr sent pend err (encAcceptReply m) $$ [$Hown $HQ]
  iunfold ownAcceptReply at Hl
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hbs := zero_array_slice b_ptr 12 12 rfl (by decide) $$ b
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  wstore; wstore; wstore; wstore
  wbytes
  wp_apply wp_wprog_Write bw wr sent pend err [] (encAcceptReply m)
    (u32Le m.replica ++ (u32Le m.inst ++ u32Le m.ballot)) [] _ _
    (by simp [encAcceptReply]) $$ [$Hpkg2 $Hw $Hbs] as %nn %e ⟨Hbs, Hw⟩
  iapply HΦ
  isplitl [Replica Instance Ballot]
  · iunfold ownAcceptReply
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe Replica Instance Ballot
  iapply wprog_finish _ _ _ _ _ _ _ (by simp [encAcceptReply]) $$ Hw

theorem epaxos.TryPreAcceptReply.Marshal.wp (l : Loc) (dq : DFrac) (m : model.TryPreAcceptReply) :
    marshalTriple (pkgInit_epaxos (GF := GF))
      (l @!! go.GoType.PointerType epaxos.TryPreAcceptReply.ty @!! go!"Marshal")
      (ownTryPreAcceptReply l m dq) (model.encTryPreAcceptReply m) := by
  intro bw wr sent pend err
  wp_start as ⟨Hown, HQ, Hl⟩
  ihave Hw := wprog_start bw wr sent pend err (encTryPreAcceptReply m) $$ [$Hown $HQ]
  iunfold ownTryPreAcceptReply at Hl
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hbs := zero_array_slice b_ptr 29 29 rfl (by decide) $$ b
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  wstore; wstore; wstore; wstore; wstore
  wbytes
  wp_apply wp_wprog_Write bw wr sent pend err [] (encTryPreAcceptReply m)
    (u32Le m.acceptorId ++ (u32Le m.replica ++ (u32Le m.inst ++ (u32Le m.ballot ++
      (u32Le m.vballot ++ (u32Le m.conflictReplica ++ (u32Le m.conflictInstance ++
        [m.conflictStatus]))))))) [] _ _
    (by simp [encTryPreAcceptReply]) $$ [$Hpkg2 $Hw $Hbs] as %nn %e ⟨Hbs, Hw⟩
  iapply HΦ
  isplitl [AcceptorId Replica Instance Ballot VBallot ConflictReplica ConflictInstance
    ConflictStatus]
  · iunfold ownTryPreAcceptReply
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe AcceptorId Replica Instance Ballot VBallot ConflictReplica ConflictInstance
      ConflictStatus
  iapply wprog_finish _ _ _ _ _ _ _ (by simp [encTryPreAcceptReply]) $$ Hw

theorem list12 {α} (d : List α) (h : d.length = 12) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11,
      d = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] := by
  match d, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, rfl⟩

theorem list16 {α} (d : List α) (h : d.length = 16) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15,
      d = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := by
  match d, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, rfl⟩

theorem epaxos.Unmarshal.spec_prepare : epaxos.Unmarshal.spec (GF := GF) MsgKind.prepare := by
  dsimp only [epaxos.Unmarshal.spec, MsgKind.ty]
  intro l br rd R
  wp_start as ⟨Hown, #Hnext, Hl⟩
  iunfold ownAny at Hl
  icases Hl with ⟨%v0, Hl⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hbs := zero_array_slice b_ptr 16 16 rfl (by decide) $$ b
  wp_apply wp_ReadAtLeast_br br rd R _ _ (W64 16) (by simp; decide) $$ [$Hpkg2 $Hown $Hbs]
    as %n %err ⟨%d, %Hd, Hbs, Hown⟩
  obtain ⟨-, hdl, hiff⟩ := Hd
  rcases err with ei | _
  · -- an error
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    iexists d
    iframe Hown
    iunfold ownAny
    iexists v0
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe LeaderId Replica Instance Ballot
  have hd : d.length = 16 := by
    have := hiff.mp rfl
    have h16 : sint.Z (W64 16) = 16 := rfl
    simp only [List.length_replicate] at hdl; omega
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, rfl⟩ :=
    list16 d hd
  simp only [List.length_cons, List.length_nil,
    List.append_nil, Nat.reduceAdd, List.drop_replicate, Nat.sub_self, List.replicate_zero]
  wp_auto
  wload; wload; wload; wload; wload; wload; wload; wload
  wload; wload; wload; wload; wload; wload; wload; wload
  rw [← encoding.binary.leToU32_4 a0, ← encoding.binary.leToU32_4 a4,
    ← encoding.binary.leToU32_4 a8, ← encoding.binary.leToU32_4 a12]
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists Msg.prepare ⟨leToU32 [a0, a1, a2, a3], leToU32 [a4, a5, a6, a7],
    leToU32 [a8, a9, a10, a11], leToU32 [a12, a13, a14, a15]⟩
  isplitr
  · ipureintro; exact ⟨rfl, trivial⟩
  isplitl [Hown]
  · simp only [Msg.body, encPrepare, leToU32_le [a0, a1, a2, a3] rfl,
      leToU32_le [a4, a5, a6, a7] rfl, leToU32_le [a8, a9, a10, a11] rfl,
      leToU32_le [a12, a13, a14, a15] rfl, List.append_assoc]
    simp only [List.cons_append, List.nil_append]
    iexact Hown
  simp only [ownMsg, ownPrepare]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe LeaderId Replica Instance Ballot

theorem epaxos.Unmarshal.spec_acceptReply : epaxos.Unmarshal.spec (GF := GF) MsgKind.acceptReply := by
  dsimp only [epaxos.Unmarshal.spec, MsgKind.ty]
  intro l br rd R
  wp_start as ⟨Hown, #Hnext, Hl⟩
  iunfold ownAny at Hl
  icases Hl with ⟨%v0, Hl⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hbs := zero_array_slice b_ptr 12 12 rfl (by decide) $$ b
  wp_apply wp_ReadAtLeast_br br rd R _ _ (W64 12) (by simp; decide) $$ [$Hpkg2 $Hown $Hbs]
    as %n %err ⟨%d, %Hd, Hbs, Hown⟩
  obtain ⟨-, hdl, hiff⟩ := Hd
  rcases err with ei | _
  · -- an error
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    iexists d
    iframe Hown
    iunfold ownAny
    iexists v0
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe Replica Instance Ballot
  have hd : d.length = 12 := by
    have := hiff.mp rfl
    have h12 : sint.Z (W64 12) = 12 := rfl
    simp only [List.length_replicate] at hdl; omega
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, rfl⟩ :=
    list12 d hd
  simp only [List.length_cons, List.length_nil,
    List.append_nil, Nat.reduceAdd, List.drop_replicate, Nat.sub_self, List.replicate_zero]
  wp_auto
  wload; wload; wload; wload; wload; wload; wload; wload
  wload; wload; wload; wload
  rw [← encoding.binary.leToU32_4 a0, ← encoding.binary.leToU32_4 a4,
    ← encoding.binary.leToU32_4 a8]
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists Msg.acceptReply ⟨leToU32 [a0, a1, a2, a3], leToU32 [a4, a5, a6, a7],
    leToU32 [a8, a9, a10, a11]⟩
  isplitr
  · ipureintro; exact ⟨rfl, trivial⟩
  isplitl [Hown]
  · simp only [Msg.body, encAcceptReply, leToU32_le [a0, a1, a2, a3] rfl,
      leToU32_le [a4, a5, a6, a7] rfl, leToU32_le [a8, a9, a10, a11] rfl, List.append_assoc]
    simp only [List.cons_append, List.nil_append]
    iexact Hown
  simp only [ownMsg, ownAcceptReply]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Replica Instance Ballot


theorem list29 {α} (d : List α) (h : d.length = 29) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28,
      d = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28] := by
  match d, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, rfl⟩

theorem epaxos.Unmarshal.spec_tryPreAcceptReply :
    epaxos.Unmarshal.spec (GF := GF) MsgKind.tryPreAcceptReply := by
  dsimp only [epaxos.Unmarshal.spec, MsgKind.ty]
  intro l br rd R
  wp_start as ⟨Hown, #Hnext, Hl⟩
  iunfold ownAny at Hl
  icases Hl with ⟨%v0, Hl⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hbs := zero_array_slice b_ptr 29 29 rfl (by decide) $$ b
  wp_apply wp_ReadAtLeast_br br rd R _ _ (W64 29) (by simp; decide) $$ [$Hpkg2 $Hown $Hbs]
    as %n %err ⟨%d, %Hd, Hbs, Hown⟩
  obtain ⟨-, hdl, hiff⟩ := Hd
  rcases err with ei | _
  · -- an error
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    iexists d
    iframe Hown
    iunfold ownAny
    iexists v0
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe AcceptorId Replica Instance Ballot VBallot ConflictReplica ConflictInstance
      ConflictStatus
  have hd : d.length = 29 := by
    have := hiff.mp rfl
    have h29 : sint.Z (W64 29) = 29 := rfl
    simp only [List.length_replicate] at hdl; omega
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, rfl⟩ :=
    list29 d hd
  simp only [List.length_cons, List.length_nil,
    List.append_nil, Nat.reduceAdd, List.drop_replicate, Nat.sub_self, List.replicate_zero]
  wp_auto
  wload; wload; wload; wload; wload; wload; wload; wload
  wload; wload; wload; wload; wload; wload; wload; wload
  wload; wload; wload; wload; wload; wload; wload; wload
  wload; wload; wload; wload; wload
  rw [← encoding.binary.leToU32_4 a0, ← encoding.binary.leToU32_4 a4,
    ← encoding.binary.leToU32_4 a8, ← encoding.binary.leToU32_4 a12,
    ← encoding.binary.leToU32_4 a16, ← encoding.binary.leToU32_4 a20,
    ← encoding.binary.leToU32_4 a24]
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists Msg.tryPreAcceptReply ⟨leToU32 [a0, a1, a2, a3], leToU32 [a4, a5, a6, a7],
    leToU32 [a8, a9, a10, a11], leToU32 [a12, a13, a14, a15], leToU32 [a16, a17, a18, a19],
    leToU32 [a20, a21, a22, a23], leToU32 [a24, a25, a26, a27], a28⟩
  isplitr
  · ipureintro; exact ⟨rfl, trivial⟩
  isplitl [Hown]
  · simp only [Msg.body, encTryPreAcceptReply,
      leToU32_le [a0, a1, a2, a3] rfl,
      leToU32_le [a4, a5, a6, a7] rfl,
      leToU32_le [a8, a9, a10, a11] rfl,
      leToU32_le [a12, a13, a14, a15] rfl,
      leToU32_le [a16, a17, a18, a19] rfl,
      leToU32_le [a20, a21, a22, a23] rfl,
      leToU32_le [a24, a25, a26, a27] rfl, List.append_assoc]
    simp only [List.cons_append, List.nil_append]
    iexact Hown
  simp only [ownMsg, ownTryPreAcceptReply]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe AcceptorId Replica Instance Ballot VBallot ConflictReplica ConflictInstance
    ConflictStatus


theorem epaxos.New.spec_all : ∀ k, epaxos.New.spec (GF := GF) k := by
  intro k l
  cases k <;> dsimp only [MsgKind.ty] <;>
  · wp_start as _
    wp_auto
    wp_alloc l' as Hl'
    wp_auto
    iapply HΦ
    iexists l'
    isplitr
    · ipureintro; rfl
    iunfold ownAny
    iexists _
    iexact Hl'


/-! The frozen per-kind `Marshal` specs of the three fixed-size kinds (a check that `ownMsg` and
`Msg.body` reduce to the per-type forms). -/

theorem epaxos.Marshal.spec_prepare : epaxos.Marshal.spec (GF := GF) MsgKind.prepare := by
  intro l dq _ _ m hk
  cases m <;> simp [Msg.kind] at hk
  exact epaxos.Prepare.Marshal.wp l dq _

theorem epaxos.Marshal.spec_acceptReply : epaxos.Marshal.spec (GF := GF) MsgKind.acceptReply := by
  intro l dq _ _ m hk
  cases m <;> simp [Msg.kind] at hk
  exact epaxos.AcceptReply.Marshal.wp l dq _

theorem epaxos.Marshal.spec_tryPreAcceptReply : epaxos.Marshal.spec (GF := GF) MsgKind.tryPreAcceptReply := by
  intro l dq _ _ m hk
  cases m <;> simp [Msg.kind] at hk
  exact epaxos.TryPreAcceptReply.Marshal.wp l dq _

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
