/-
`replica/defs`'s marshalers and decoders: `Propose`, `ProposeReplyTS`, `Beacon`, `BeaconReply`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.StateOps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.StateUnm
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Bytes

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [state.Assumptions] [replica.defs.Assumptions] [bufio.Assumptions] [io.Assumptions]

set_option goose.wp.extras true

theorem replica.defs.Propose.Marshal.spec_holds : replica.defs.Propose.Marshal.spec (GF := GF) := by
  intro l dq p bw wr sent pend err
  wp_start as ⟨Hown, HQ, Hl⟩
  ihave Hw := wprog_start bw wr sent pend err p.enc $$ [$Hown $HQ]
  iunfold ownPropose at Hl
  icases Hl with ⟨%cv, Hl, #Hc⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hbs := zero_array_slice b_ptr 8 8 rfl (by decide) $$ b
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  wbytes
  wp_apply wp_wprog_Write bw wr sent pend err [] p.enc (u32Le p.cmdId ++ u32Le p.clientId)
    (encCommand p.cmd ++ u64Le p.ts) _ _ (by simp [ProposeV.enc, encPropose]) $$
    [$Hpkg2 $Hw $Hbs] as %nn %e ⟨Hbs, Hw⟩
  ihave #Hst : pkgInit_state $$ []
  · iPkgInit
  wp_apply wp_wprog_marshal _ _ _ _ (state.Command.Marshal.spec_holds _ dq cv p.cmd) bw wr
    sent pend err _ _ (u64Le p.ts) rfl $$ [$Hst $Hpkg2 $Hw $Command $Hc] as ⟨⟨Command, -⟩, Hw⟩
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  rw [set_all8 _ (by simp [u32Le_length])]
  simp only [u64Le_sbytes_cons, List.append_nil]
  wp_apply wp_wprog_Write bw wr sent pend err _ _ (u64Le p.ts) [] _ _ (by simp) $$
    [$Hpkg2 $Hw $Hbs] as %nn2 %e2 ⟨Hbs, Hw⟩
  iapply HΦ
  isplitl [CommandId ClientId Command Timestamp]
  · iunfold ownPropose
    iexists cv
    iframe Hc
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe CommandId ClientId Command Timestamp
  iapply wprog_finish _ _ _ _ _ _ _ _ _ (by simp [ProposeV.enc, encPropose]) $$ Hw

theorem replica.defs.Propose.Unmarshal.spec_holds : replica.defs.Propose.Unmarshal.spec (GF := GF) := by
  intro l v0 br rd R
  wp_start as ⟨Hown, #Hnext, Hl⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hbs := zero_array_slice b_ptr 8 8 rfl (by decide) $$ b
  wp_apply wp_ReadAtLeast_br br rd R _ _ (W64 8) (by simp; decide) $$ [$Hpkg2 $Hown $Hbs]
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
    iexists v0
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe CommandId ClientId Command Timestamp
  have hd8 : d.length = 8 := by
    have := hiff.mp rfl
    have h8 : sint.Z (W64 8) = 8 := rfl
    simp only [List.length_replicate] at hdl; omega
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩ := list8 d hd8
  simp only [List.length_cons, List.length_nil, List.drop_eq_nil_of_le, List.length_replicate,
    List.append_nil, Nat.reduceAdd, List.drop_replicate, Nat.sub_self, List.replicate_zero]
  wp_auto
  wload; wload; wload; wload
  wload; wload; wload; wload
  rw [← encoding.binary.leToU32_4 w0, ← encoding.binary.leToU32_4 w4]
  ihave #Hn2 := nextIs_shift I R [w0, w1, w2, w3, w4, w5, w6, w7] ProposeV.enc
    (fun p => cmdWf p.cmd) encCommand cmdWf (fun p ext t hwf hp =>
      ⟨p.cmd, u64Le p.ts ++ ext, hwf, prefix_skip [w0, w1, w2, w3, w4, w5, w6, w7]
        (u32Le p.cmdId ++ u32Le p.clientId) t _ (by simp [u32Le_length])
        (by simp only [ProposeV.enc, encPropose, List.append_assoc] at hp ⊢; exact hp)⟩) $$ Hnext
  ihave #Hst : pkgInit_state $$ []
  · iPkgInit
  wp_apply state.Command.Unmarshal.spec_holds _ v0.Command' br rd _
    $$ [$Hst $Hpkg2 $Hown $Hn2 $Command] as %e1 H1
  icases H1 with (⟨%he1, %wc, %hwc, Hown, %cv, Command, #Hc⟩ | ⟨%he1, #He1, %d1, Hown, %cv, Command⟩)
  rotate_left
  · -- an error
    rcases e1 with ei | _
    · wp_auto
      iapply HΦ
      iright
      iframe He1
      isplitr
      · ipureintro; simp
      iexists _ ++ d1
      simp only [List.append_assoc]
      iframe Hown
      iexists replica.defs.Propose.mk (leToU32 [w0, w1, w2, w3]) (leToU32 [w4, w5, w6, w7]) cv
        v0.Timestamp'
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe CommandId ClientId Command Timestamp
    · exact absurd rfl he1
  subst he1
  wp_auto
  wp_apply wp_ReadAtLeast_br br rd _ _ _ (W64 8) (by simp; decide) $$ [$Hpkg2 $Hown $Hbs]
    as %n2 %err2 ⟨%d2, %Hd2, Hbs, Hown, #Herr2⟩
  obtain ⟨-, hdl2, hiff2⟩ := Hd2
  rcases err2 with ei | _
  · -- an error
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    iexists _ ++ encCommand wc ++ d2
    simp only [List.append_assoc]
    iframe Hown
    iexists replica.defs.Propose.mk (leToU32 [w0, w1, w2, w3]) (leToU32 [w4, w5, w6, w7]) cv
        v0.Timestamp'
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe CommandId ClientId Command Timestamp
  have hd8 : d2.length = 8 := by
    have := hiff2.mp rfl
    have h8 : sint.Z (W64 8) = 8 := rfl
    simp only [List.length_cons, List.length_nil] at hdl2; omega
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩ := list8 d2 hd8
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, List.drop_eq_nil_of_le,
    List.drop_succ_cons, List.drop_zero, List.append_nil]
  wp_auto
  wload; wload; wload; wload; wload; wload; wload; wload
  rw [← encoding.binary.leToU64_8 x0]
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists ⟨leToU32 [w0, w1, w2, w3], leToU32 [w4, w5, w6, w7], wc, leToU64 [x0, x1, x2, x3, x4, x5, x6, x7]⟩
  isplitr
  · ipureintro; exact hwc
  isplitl [Hown]
  · simp only [ProposeV.enc, encPropose, leToU32_le [w0, w1, w2, w3] rfl,
      leToU32_le [w4, w5, w6, w7] rfl, leToU64_le [x0, x1, x2, x3, x4, x5, x6, x7] rfl,
      List.append_assoc]
    simp only [List.cons_append, List.nil_append]
    iexact Hown
  iunfold ownPropose
  iexists cv
  iframe Hc
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe CommandId ClientId Command Timestamp

theorem replica.defs.ProposeReplyTS.Marshal.spec_holds : replica.defs.ProposeReplyTS.Marshal.spec (GF := GF) := by
  intro l dq dq' p sl bw wr sent pend err
  wp_start as ⟨Hown, HQ, Hl, Hv⟩
  ihave Hw := wprog_start bw wr sent pend err p.enc $$ [$Hown $HQ]
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hb := zero_array b_ptr (W64 8) 8 rfl 8 rfl $$ b
  ihave ⟨Hbs, Hback⟩ := array_slice_acc b_ptr _ (W64 5) (W64 8) 5 rfl
    (by simp only [List.length_replicate]; rfl) (by simp) (by simp) $$ Hb
  wstore; wstore; wstore; wstore; wstore
  wbytes
  wp_apply wp_wprog_Write bw wr sent pend err [] p.enc (p.ok :: u32Le p.cmdId)
    (encValue p.val ++ u64Le p.ts) _ _ (by simp [ProposeReplyV.enc, encProposeReplyTS]) $$
    [$Hpkg2 $Hw $Hbs] as %nn %e ⟨Hbs, Hw⟩
  ihave #Hst : pkgInit_state $$ []
  · iPkgInit
  wp_apply wp_wprog_marshal _ _ _ _ (state.Value.Marshal.spec_holds _ dq dq' sl p.val) bw wr
    sent pend err _ _ (u64Le p.ts) rfl $$ [$Hst $Hpkg2 $Hw $Value $Hv] as ⟨⟨Value, Hv⟩, Hw⟩
  ihave Hb := Hback $$ %_ %(by simp [u32Le_length]) Hbs
  (try wp_auto)
  ihave ⟨Hbs, Hback⟩ := array_slice_acc b_ptr _ (W64 8) (W64 8) 8 rfl
    (by simp only [List.length_append, List.length_cons, List.length_drop, List.length_replicate,
      u32Le_length]; rfl) (by simp [u32Le_length]) (by simp) $$ Hb
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  rw [set_all8 _ (by simp [u32Le_length])]
  simp only [u64Le_sbytes_cons, List.append_nil]
  wp_apply wp_wprog_Write bw wr sent pend err _ _ (u64Le p.ts) [] _ _ (by simp) $$
    [$Hpkg2 $Hw $Hbs] as %nn2 %e2 ⟨Hbs, Hw⟩
  iapply HΦ
  isplitl [OK CommandId Value Timestamp Hv]
  · iframe Hv
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe OK CommandId Value Timestamp
  iapply wprog_finish _ _ _ _ _ _ _ _ _ (by simp [ProposeReplyV.enc, encProposeReplyTS]) $$ Hw

theorem replica.defs.Beacon.Marshal.spec_holds : replica.defs.Beacon.Marshal.spec (GF := GF) := by
  intro l dq ts bw wr sent pend err
  wp_start as ⟨Hown, HQ, Hl⟩
  ihave Hw := wprog_start bw wr sent pend err (encBeacon ts) $$ [$Hown $HQ]
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hbs := zero_array_slice b_ptr 8 8 rfl (by decide) $$ b
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  wbytes
  wp_apply wp_wprog_Write bw wr sent pend err [] (encBeacon ts) (u64Le ts) [] _ _
    (by simp [encBeacon]) $$ [$Hpkg2 $Hw $Hbs] as %nn %e ⟨Hbs, Hw⟩
  iapply HΦ
  isplitl [Timestamp]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe Timestamp
  iapply wprog_finish _ _ _ _ _ _ _ _ _ (by simp [encBeacon]) $$ Hw

theorem replica.defs.BeaconReply.Marshal.spec_holds : replica.defs.BeaconReply.Marshal.spec (GF := GF) := by
  intro l dq ts bw wr sent pend err
  wp_start as ⟨Hown, HQ, Hl⟩
  ihave Hw := wprog_start bw wr sent pend err (encBeacon ts) $$ [$Hown $HQ]
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hbs := zero_array_slice b_ptr 8 8 rfl (by decide) $$ b
  wstore; wstore; wstore; wstore; wstore; wstore; wstore; wstore
  wbytes
  wp_apply wp_wprog_Write bw wr sent pend err [] (encBeacon ts) (u64Le ts) [] _ _
    (by simp [encBeacon]) $$ [$Hpkg2 $Hw $Hbs] as %nn %e ⟨Hbs, Hw⟩
  iapply HΦ
  isplitl [Timestamp]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe Timestamp
  iapply wprog_finish _ _ _ _ _ _ _ _ _ (by simp [encBeacon]) $$ Hw

theorem replica.defs.Beacon.Unmarshal.spec_holds : replica.defs.Beacon.Unmarshal.spec (GF := GF) := by
  intro l v0 br rd R
  wp_start as ⟨Hown, #Hnext, Hl⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hbs := zero_array_slice b_ptr 8 8 rfl (by decide) $$ b
  wp_apply wp_ReadAtLeast_br br rd R _ _ (W64 8) (by simp; decide) $$ [$Hpkg2 $Hown $Hbs]
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
    iexists v0
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe Timestamp
  have hd8 : d.length = 8 := by
    have := hiff.mp rfl
    have h8 : sint.Z (W64 8) = 8 := rfl
    simp only [List.length_replicate] at hdl; omega
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩ := list8 d hd8
  simp only [List.length_cons, List.length_nil, List.length_replicate,
    List.append_nil, Nat.reduceAdd, List.drop_replicate, Nat.sub_self, List.replicate_zero]
  wp_auto
  wload; wload; wload; wload; wload; wload; wload; wload
  rw [← encoding.binary.leToU64_8 w0]
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists leToU64 [w0, w1, w2, w3, w4, w5, w6, w7]
  isplitr
  · ipureintro; trivial
  simp only [encBeacon, leToU64_le [w0, w1, w2, w3, w4, w5, w6, w7] rfl]
  iframe Hown
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Timestamp

theorem replica.defs.BeaconReply.Unmarshal.spec_holds : replica.defs.BeaconReply.Unmarshal.spec (GF := GF) := by
  intro l v0 br rd R
  wp_start as ⟨Hown, #Hnext, Hl⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hbs := zero_array_slice b_ptr 8 8 rfl (by decide) $$ b
  wp_apply wp_ReadAtLeast_br br rd R _ _ (W64 8) (by simp; decide) $$ [$Hpkg2 $Hown $Hbs]
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
    iexists v0
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe Timestamp
  have hd8 : d.length = 8 := by
    have := hiff.mp rfl
    have h8 : sint.Z (W64 8) = 8 := rfl
    simp only [List.length_replicate] at hdl; omega
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩ := list8 d hd8
  simp only [List.length_cons, List.length_nil, List.length_replicate,
    List.append_nil, Nat.reduceAdd, List.drop_replicate, Nat.sub_self, List.replicate_zero]
  wp_auto
  wload; wload; wload; wload; wload; wload; wload; wload
  rw [← encoding.binary.leToU64_8 w0]
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists leToU64 [w0, w1, w2, w3, w4, w5, w6, w7]
  isplitr
  · ipureintro; trivial
  simp only [encBeacon, leToU64_le [w0, w1, w2, w3, w4, w5, w6, w7] rfl]
  iframe Hown
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Timestamp

theorem list5 {α} (d : List α) (h : d.length = 5) : ∃ a0 a1 a2 a3 a4, d = [a0, a1, a2, a3, a4] := by
  match d, h with
  | [a0, a1, a2, a3, a4], _ => exact ⟨a0, a1, a2, a3, a4, rfl⟩

theorem replica.defs.ProposeReplyTS.Unmarshal.spec_holds :
    replica.defs.ProposeReplyTS.Unmarshal.spec := by
  intro l v0 br rd R
  wp_start as ⟨Hown, #Hnext, Hl⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  iStructNamed Hl
  wp_auto
  ihave Hb := zero_array b_ptr (W64 8) 8 rfl 8 rfl $$ b
  ihave ⟨Hbs, Hback⟩ := array_slice_acc b_ptr _ (W64 5) (W64 8) 5 rfl
    (by simp only [List.length_replicate]; rfl) (by simp) (by simp) $$ Hb
  wp_apply wp_ReadAtLeast_br br rd R _ _ (W64 5) (by simp; decide) $$ [$Hpkg2 $Hown $Hbs]
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
    iexists v0
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe OK CommandId Value Timestamp
  have hd5 : d.length = 5 := by
    have := hiff.mp rfl
    have h5 : sint.Z (W64 5) = 5 := rfl
    simp only [List.length_take, List.length_replicate] at hdl; omega
  obtain ⟨w0, w1, w2, w3, w4, rfl⟩ := list5 d hd5
  simp only [List.length_cons, List.length_nil, List.length_take, List.length_replicate,
    List.append_nil, Nat.reduceAdd, List.take_replicate, List.drop_replicate, Nat.sub_self,
    List.replicate_zero, Nat.min_def, Nat.reduceLeDiff, ite_true]
  wp_auto
  wload; wload; wload; wload; wload
  rw [← encoding.binary.leToU32_4 w1]
  ihave #Hn2 := nextIs_shift I R [w0, w1, w2, w3, w4] ProposeReplyV.enc
    (fun p => p.val.length < 2 ^ 16) encValue (fun v => v.length < 2 ^ 16) (fun p ext t hwf hp =>
      ⟨p.val, u64Le p.ts ++ ext, hwf, prefix_skip [w0, w1, w2, w3, w4]
        ([p.ok] ++ u32Le p.cmdId) t _ (by simp [u32Le_length])
        (by simp only [ProposeReplyV.enc, encProposeReplyTS, List.append_assoc] at hp ⊢
            exact hp)⟩) $$ Hnext
  ihave #Hst : pkgInit_state $$ []
  · iPkgInit
  wp_apply state.Value.Unmarshal.spec_holds _ v0.Value' br rd _
    $$ [$Hst $Hpkg2 $Hown $Hn2 $Value] as %e1 H1
  icases H1 with (⟨%he1, %v, %hv, Hown, %sl, Value, Hsl⟩ | ⟨%he1, #He1, %d1, Hown, %sl, Value⟩)
  rotate_left
  · -- an error
    rcases e1 with ei | _
    · wp_auto
      iapply HΦ
      iright
      iframe He1
      isplitr
      · ipureintro; simp
      iexists _ ++ d1
      simp only [List.append_assoc]
      iframe Hown
      iexists replica.defs.ProposeReplyTS.mk w0 (leToU32 [w1, w2, w3, w4]) sl v0.Timestamp'
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe OK CommandId Value Timestamp
    · exact absurd rfl he1
  subst he1
  ihave Hb := Hback $$ %_ %rfl Hbs
  wp_auto
  ihave ⟨Hbs, Hback⟩ := array_slice_acc b_ptr _ (W64 8) (W64 8) 8 rfl
    (by simp only [List.length_append, List.length_cons, List.length_drop, List.length_replicate,
      List.length_nil]; rfl) (by simp) (by simp) $$ Hb
  wp_apply wp_ReadAtLeast_br br rd _ _ _ (W64 8) (by simp; decide) $$ [$Hpkg2 $Hown $Hbs]
    as %n2 %err2 ⟨%d2, %Hd2, Hbs, Hown, #Herr2⟩
  obtain ⟨-, hdl2, hiff2⟩ := Hd2
  rcases err2 with ei | _
  · -- an error
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    iexists _ ++ encValue v ++ d2
    simp only [List.append_assoc]
    iframe Hown
    iexists replica.defs.ProposeReplyTS.mk w0 (leToU32 [w1, w2, w3, w4]) sl v0.Timestamp'
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe OK CommandId Value Timestamp
  have hd8 : d2.length = 8 := by
    have := hiff2.mp rfl
    have h8 : sint.Z (W64 8) = 8 := rfl
    simp only [List.length_take, List.length_append, List.length_cons, List.length_nil,
      List.length_drop, List.length_replicate] at hdl2; omega
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩ := list8 d2 hd8
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, List.take_succ_cons, List.take_zero,
    List.drop_succ_cons, List.drop_zero, List.append_nil, List.drop_eq_nil_of_le]
  wp_auto
  wload; wload; wload; wload; wload; wload; wload; wload
  rw [← encoding.binary.leToU64_8 x0]
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists ⟨w0, leToU32 [w1, w2, w3, w4], v, leToU64 [x0, x1, x2, x3, x4, x5, x6, x7]⟩
  isplitr
  · ipureintro; exact hv
  isplitl [Hown]
  · simp only [ProposeReplyV.enc, encProposeReplyTS, leToU32_le [w1, w2, w3, w4] rfl,
      leToU64_le [x0, x1, x2, x3, x4, x5, x6, x7] rfl, List.append_assoc]
    simp only [List.cons_append, List.nil_append]
    iexact Hown
  iexists sl
  iframe Hsl
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe OK CommandId Value Timestamp

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
