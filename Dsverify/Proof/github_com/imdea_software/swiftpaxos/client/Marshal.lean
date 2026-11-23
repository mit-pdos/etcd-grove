/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Marshal.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The marshaling the client uses (internal specs with their proofs; `Spec/swift/Wire.lean`'s
format): `state.Operation`, `Key`, `Value`, `Command` and `defs.Propose`'s `Marshal` over a sink
(`Proof/client/Sink.lean`), and `state.NIL`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Sink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Wire
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.state
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.replica.defs
public import Perennial.Proof.encoding.binary

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net wire Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

theorem w8_sint32 (y : w32) : W8 (sint.Z y) = y.setWidth 8 := by
  have : W8 (sint.Z y) = W8 (uint.Z y) := by word
  rw [this]; simp [W8, uint.Z]
theorem w8_uint32 (y : w32) : W8 (uint.Z y) = y.setWidth 8 := by simp [W8, uint.Z]
theorem w8_sint64 (y : w64) : W8 (sint.Z y) = y.setWidth 8 := by
  have : W8 (sint.Z y) = W8 (uint.Z y) := by word
  rw [this]; simp [W8, uint.Z]
theorem w8_uint64 (y : w64) : W8 (uint.Z y) = y.setWidth 8 := by simp [W8, uint.Z]

/-- The bytes `Propose.Marshal` stores for an `int32`: its little-endian bytes. -/
theorem le32_sbytes (x : w32) :
    [W8 (sint.Z x), W8 (sint.Z (BitVec.sshiftRight' x (W64 8))),
      W8 (sint.Z (BitVec.sshiftRight' x (W64 16))), W8 (sint.Z (BitVec.sshiftRight' x (W64 24)))] =
      sp.le32 x := by
  unfold sp.le32
  rw [encoding.binary.u32Le_4]
  simp only [w8_sint32, w8_uint32, List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;>
  first
  | trivial
  | ext i hi
    simp [W64, BitVec.sshiftRight', BitVec.getLsbD_sshiftRight, show ¬32 ≤ i by omega]
    intro; omega

/-- The bytes `Propose.Marshal` stores for an `int64`: its little-endian bytes. -/
theorem le64_sbytes (x : w64) :
    [W8 (sint.Z x), W8 (sint.Z (BitVec.sshiftRight' x (W64 8))),
      W8 (sint.Z (BitVec.sshiftRight' x (W64 16))), W8 (sint.Z (BitVec.sshiftRight' x (W64 24))),
      W8 (sint.Z (BitVec.sshiftRight' x (W64 32))), W8 (sint.Z (BitVec.sshiftRight' x (W64 40))),
      W8 (sint.Z (BitVec.sshiftRight' x (W64 48))), W8 (sint.Z (BitVec.sshiftRight' x (W64 56)))] =
      sp.le64 x := by
  unfold sp.le64
  rw [encoding.binary.u64Le_8]
  simp only [w8_sint64, w8_uint64, List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
  first
  | trivial
  | ext i hi
    simp [W64, BitVec.sshiftRight', BitVec.getLsbD_sshiftRight, show ¬64 ≤ i by omega]
    intro; omega

theorem le32x2_sbytes (x y : w32) :
    [W8 (sint.Z x), W8 (sint.Z (BitVec.sshiftRight' x (W64 8))),
      W8 (sint.Z (BitVec.sshiftRight' x (W64 16))), W8 (sint.Z (BitVec.sshiftRight' x (W64 24))),
      W8 (sint.Z y), W8 (sint.Z (BitVec.sshiftRight' y (W64 8))),
      W8 (sint.Z (BitVec.sshiftRight' y (W64 16))), W8 (sint.Z (BitVec.sshiftRight' y (W64 24)))] =
      sp.le32 x ++ sp.le32 y := by
  rw [← le32_sbytes, ← le32_sbytes]; rfl

theorem set8 {A : Type} (l : List A) (hl : l.length = 8) (a b c d e f g h : A) :
    ((((((((l.set (Int.toNat 0) a).set 1 b).set 2 c).set 3 d).set 4 e).set 5 f).set 6 g).set 7 h) =
      [a, b, c, d, e, f, g, h] := by
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem set8' {A : Type} (l : List A) (hl : l.length = 8) (a b c d e f g h : A) :
    ((((((((l.set 0 a).set 1 b).set 2 c).set 3 d).set 4 e).set 5 f).set 6 g).set 7 h) =
      [a, b, c, d, e, f, g, h] := by
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ => rfl

set_option hygiene false in
/-- One store `bs[i] = x` into the 8-byte buffer `Hsl` (the bounds check first). -/
local macro "store8" : tactic => `(tactic| (
  (try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by decide⟩)])
  wp_pures
  wp_apply wp_store_slice_index _ _ _ _ $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro
    simp only [List.length_set, List.length_replicate, List.length_append, sp.le32,
      u32Le_length]
    decide
  (try wp_auto)))

section proofs

variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF] [github_com.imdea_software.swiftpaxos.SwiftHyps GF]
variable [state.Assumptions] [encoding.binary.Assumptions] [replica.defs.Assumptions]

set_option goose.wp.extras true

/-- `state.NIL()`: an empty value. -/
theorem wp_NIL :
    {{ (True : IProp GF) }}
      (App (Val (@! state.NIL)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* ([] : List w8) }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iExactEq Hsl
  rfl

theorem wp_Operation_Marshal (t : Loc) (dq : DFrac) (op : w8) (wr : GoInterface)
    (S Q : List w8 → IProp GF) (W : List w8) :
    {{ sinkOk wr S Q ∗ S W ∗ □ Q (W ++ [op]) ∗ t ↦{dq} op }}
      (App (Val (t @!! go.GoType.PointerType state.Operation.ty @!! go!"Marshal")) (Val #wr))
    {{ RET #(); S (W ++ [op]) ∗ t ↦{dq} op }} := by
  wp_start as ⟨#Hsink, HS, #HQ, Ht⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := w8)) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_replicate] at Hlen
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by word⟩)]
  wp_apply wp_store_slice_index sl _ _ op $$ [$Hsl] as Hsl
  · ipureintro; simp
  have hset : (List.replicate 1 (zero_val w8)).set 0 op = [op] := rfl
  rw [hset]
  iunfold sinkOk at Hsink
  icases Hsink with ⟨%e, %He, #HW⟩
  subst He
  wp_auto
  wp_apply HW $$ HS HQ Hsl as %nn %err HS Hsl
  iapply HΦ
  iframe

/-- `binary.LittleEndian.PutUint16` (Perennial specifies only the 32- and 64-bit ones; proved
here from `encoding/binary`'s code). -/
theorem wp_LittleEndian_PutUint16 (b : GoSlice) (space rem : List w8) (v : w16)
    (Hlen : space.length = 2) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦* (space ++ rem) }}
      (App (App (Val ((globalAddr encoding.binary.LittleEndian) @!!
          go.GoType.PointerType encoding.binary.littleEndian.ty @!! go!"PutUint16"))
        (Val #b)) (Val #v))
    {{ RET #(); b ↦* ([W8 (uint.Z v), W8 (uint.Z (v >>> W64 8))] ++ rem) }} := by
  obtain ⟨w0, w1, rfl⟩ : ∃ w0 w1, space = [w0, w1] := by
    match space, Hlen with
    | [w0, w1], _ => exact ⟨w0, w1, rfl⟩
  wp_start as Hb
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hinit := encoding.binary.isInit_access $$ Hpkg
  icases Hinit with ⟨#Hle, -⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  simp only [List.length_append, List.length_cons, List.length_nil] at Hl
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by word⟩)]
  wp_apply wp_load_slice_index b _ _ _ w1 (by decide) $$ [Hb] as Hb
  · iframe Hb; ipureintro; rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by word⟩)]
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] as Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [encoding.binary.sint_W64_lit]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil] at *
    word⟩)]
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] as Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [encoding.binary.sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  iapply HΦ
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero, List.nil_append]
  iexact Hb

theorem wp_Key_Marshal (t : Loc) (dq : DFrac) (k : w64) (wr : GoInterface)
    (S Q : List w8 → IProp GF) (W : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ sinkOk wr S Q ∗ S W ∗
        □ Q (W ++ sp.le64 k) ∗ t ↦{dq} k }}
      (App (Val (t @!! go.GoType.PointerType state.Key.ty @!! go!"Marshal")) (Val #wr))
    {{ RET #(); S (W ++ sp.le64 k) ∗ t ↦{dq} k }} := by
  wp_start as ⟨#Hsink, HS, #HQ, Ht⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := w8)) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  wp_apply encoding.binary.wp_LittleEndian_PutUint64 sl (List.replicate 8 (zero_val w8)) [] k
    (by simp) $$ [Hsl] as Hsl
  · simp only [List.append_nil]; iexact Hsl
  iunfold sinkOk at Hsink
  icases Hsink with ⟨%e, %He, #HW⟩
  subst He
  wp_auto
  rw [List.append_nil]
  rw [show u64Le k = sp.le64 k from rfl]
  wp_apply HW $$ HS HQ Hsl as %nn %err HS Hsl
  iapply HΦ
  iframe

theorem encValue_head (v : List w8) (n : w64) (hn : sint.nat n = v.length) (hn0 : 0 ≤ sint.Z n) :
    [W8 (uint.Z (W16 (sint.Z n))), W8 (uint.Z (W16 (sint.Z n) >>> W64 8)), zero_val w8,
      zero_val w8] ++ v = sp.encValue v := by
  unfold sp.encValue
  have h1 : W8 (uint.Z (W16 (sint.Z n))) = W8 (v.length % 256 : Nat) := by
    rw [← hn]; word
  have h2 : W8 (uint.Z (W16 (sint.Z n) >>> W64 8)) = W8 (v.length / 256 % 256 : Nat) := by
    rw [← hn]; word
  rw [h1, h2]; rfl

theorem wp_Value_Marshal (t : Loc) (dq : DFrac) (vsl : GoSlice) (v : List w8) (wr : GoInterface)
    (S Q : List w8 → IProp GF) (W : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ sinkOk wr S Q ∗ S W ∗
        bufio.prefixClosed Q ∗ □ Q (W ++ sp.encValue v) ∗ t ↦{dq} vsl ∗ vsl ↦*□ v }}
      (App (Val (t @!! go.GoType.PointerType state.Value.ty @!! go!"Marshal")) (Val #wr))
    {{ RET #(); S (W ++ sp.encValue v) ∗ t ↦{dq} vsl }} := by
  wp_start as ⟨#Hsink, HS, #Hpc, #HQ, Ht, #Hv⟩
  ihave %Htn := typedPointsto_not_null $$ Ht
  ihave %Hvl := ownSlice_len _ _ _ $$ Hv
  wp_auto
  wp_apply (wp_slice_make2 (V := w8)) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  wp_if_destruct
  · exact absurd rfl Htn
  have h4 : List.replicate 4 (zero_val w8) =
      List.replicate 2 (zero_val w8) ++ List.replicate 2 (zero_val w8) := rfl
  rw [h4]
  wp_apply wp_LittleEndian_PutUint16 sl (List.replicate 2 (zero_val w8)) (List.replicate 2 (zero_val w8)) _
    (by simp) $$ [$Hsl] as Hsl
  iunfold sinkOk at Hsink
  icases Hsink with ⟨%e, %He, #HW⟩
  subst He
  wp_auto
  rw [← encValue_head v vsl.len Hvl.1.symm Hvl.2, ← List.append_assoc]
  rw [show ∀ a b : w8, [a, b] ++ List.replicate 2 (zero_val w8) =
    [a, b, zero_val w8, zero_val w8] from fun _ _ => rfl]
  iunfold bufio.prefixClosed at Hpc
  ihave #HQ1 := Hpc $$ %_ %v HQ
  wp_apply HW $$ HS HQ1 Hsl as %nn %err HS Hsl
  wp_apply HW $$ HS HQ Hv as %nn' %err' HS -
  iapply HΦ
  iframe

theorem wp_Command_Marshal (t : Loc) (dq : DFrac) (cv : state.Command) (c : sp.Cmd)
    (wr : GoInterface) (S Q : List w8 → IProp GF) (W : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ sinkOk wr S Q ∗ S W ∗
        bufio.prefixClosed Q ∗ □ Q (W ++ sp.encCmd c) ∗ t ↦{dq} cv ∗ cv.V' ↦*□ c.val ∗
        ⌜cv.Op' = c.op ∧ cv.K' = c.key⌝ }}
      (App (Val (t @!! go.GoType.PointerType state.Command.ty @!! go!"Marshal")) (Val #wr))
    {{ RET #(); S (W ++ sp.encCmd c) ∗ t ↦{dq} cv }} := by
  wp_start as ⟨#Hsink, HS, #Hpc, #HQ, Ht, #Hv, %Hc⟩
  obtain ⟨hop, hk⟩ := Hc
  ihave %Htn := typedPointsto_not_null $$ Ht
  iStructNamed Ht
  wp_auto
  unfold sp.encCmd
  rw [show W ++ ([c.op] ++ sp.le64 c.key ++ sp.encValue c.val) =
    W ++ [c.op] ++ sp.le64 c.key ++ sp.encValue c.val by simp only [List.append_assoc]]
  ihave #Hpc0 := Hpc
  iunfold bufio.prefixClosed at Hpc
  ihave #HQ2 := Hpc $$ %_ %(sp.encValue c.val) HQ
  ihave #HQ1 := Hpc $$ %_ %(sp.le64 c.key) HQ2
  rw [← hop, ← hk]
  wp_apply wp_Operation_Marshal $$ [$Hsink $HS $HQ1 $Op] as ⟨HS, Op⟩
  wp_apply wp_Key_Marshal $$ [$Hsink $HS $HQ2 $K] as ⟨HS, K⟩
  wp_apply wp_Value_Marshal $$ [$Hsink $HS $Hpc0 $HQ $V $Hv] as ⟨HS, V⟩
  iapply HΦ
  iframe HS
  iapply typedPointsto_combine _ _ _ Htn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem wp_Propose_Marshal (t : Loc) (dq : DFrac) (pv : replica.defs.Propose) (seq cl : w32)
    (c : sp.Cmd) (ts : w64) (wr : GoInterface) (S Q : List w8 → IProp GF) (W : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ sinkOk wr S Q ∗ S W ∗
        bufio.prefixClosed Q ∗ □ Q (W ++ (sp.Msg.propose seq cl c ts).body) ∗ t ↦{dq} pv ∗
        pv.Command'.V' ↦*□ c.val ∗
        ⌜pv.CommandId' = seq ∧ pv.ClientId' = cl ∧ pv.Command'.Op' = c.op ∧
          pv.Command'.K' = c.key ∧ pv.Timestamp' = ts⌝ }}
      (App (Val (t @!! go.GoType.PointerType replica.defs.Propose.ty @!! go!"Marshal")) (Val #wr))
    {{ RET #(); S (W ++ (sp.Msg.propose seq cl c ts).body) ∗ t ↦{dq} pv }} := by
  wp_start as ⟨#Hsink, HS, #Hpc, #HQ, Ht, #Hv, %Hc⟩
  obtain ⟨hseq, hcl, hop, hk, hts⟩ := Hc
  ihave %Htn := typedPointsto_not_null $$ Ht
  iStructNamed Ht
  wp_auto
  ihave Hsl := slice_array b_ptr 8 (zero_val (GoArray w8 8)) (by decide) $$ b
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl]
  rw [show (zero_val (GoArray w8 8)).arr = List.replicate 8 (W8 0) from rfl]
  store8
  store8
  store8
  store8
  store8
  store8
  store8
  store8
  rw [set8 _ (by simp)]
  rw [le32x2_sbytes, hseq, hcl]
  have hbody : W ++ (sp.Msg.propose seq cl c ts).body =
      W ++ (sp.le32 seq ++ sp.le32 cl) ++ sp.encCmd c ++ sp.le64 ts := by
    simp only [sp.Msg.body, List.append_assoc]
  rw [hbody]
  ihave #Hpc0 := Hpc
  iunfold bufio.prefixClosed at Hpc
  ihave #HQ2 := Hpc $$ %_ %(sp.le64 ts) HQ
  ihave #HQ1 := Hpc $$ %_ %(sp.encCmd c) HQ2
  iunfold sinkOk at Hsink
  icases Hsink with ⟨%e, %He, #HW⟩
  subst He
  wp_pures
  wp_apply HW $$ HS HQ1 Hsl as %nn %err HS Hsl
  ihave #Hsink : sinkOk (GoInterface.ok e) S Q $$ []
  · iunfold sinkOk; iexists e; isplitr
    · ipureintro; rfl
    iexact HW
  wp_apply wp_Command_Marshal _ _ _ c $$ [$Hsink $HS $Hpc0 $HQ2 $Command $Hv] as ⟨HS, Command⟩
  · ipureintro; exact ⟨hop, hk⟩
  store8
  store8
  store8
  store8
  store8
  store8
  store8
  store8
  rw [set8' _ (by simp [sp.le32, u32Le_length]), le64_sbytes, hts]
  wp_pures
  wp_apply HW $$ HS HQ Hsl as %nn' %err' HS Hsl
  iapply HΦ
  iframe HS
  iapply typedPointsto_combine _ _ _ Htn
  simp only [TypedPointsto.typedPointstoDef]
  rw [hseq, hcl, hts]
  iframe

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
