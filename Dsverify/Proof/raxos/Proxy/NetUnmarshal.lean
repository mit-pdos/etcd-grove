/-
Package `proxy`: `ClientBatch.Unmarshal` with the decoded encoding's length bound (`unmarshalB`):
the proof of `unmarshal_proof` (`WireProof.lean`), whose length read is below `2^63`; the
frozen `ClientBatch.Unmarshal.spec` does not state it, `connectionListener` needs it to align
the bytes read with the stream's frames.
-/
module

public import Dsverify.Proof.raxos.Proxy.NetFrames

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open models_lab.pbcodec (PbCodec)

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.proto.client.Assumptions] [raxos.replica.src.Assumptions]

/-- `ClientBatch.Unmarshal.spec` with `bs.length < 2 ^ 63`. -/
abbrev unmarshalB.spec : Prop :=
  ∀ (t : Loc) (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.proto.client ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ codecSet (GF := GF) ∗
      kitCodecOk (GF := GF) ∗ t ↦ (zero_val raxos.proto.client.ClientBatch) ∗
      bufio.readerOk rd I ∗ bufio.ownReader br rd I R ∗
      □ (∀ d e, I (R ++ d ++ e) -∗ ⌜d.length = 8 → leNum d < 2 ^ 63⌝) }}
    (App (Val (t @!! go.GoType.PointerType raxos.proto.client.ClientBatch.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (e : GoInterface), RET #e; ∃ data : List w8, bufio.ownReader br rd I (R ++ data) ∗
      (⌜e ≠ interface.nil⌝ ∨
       ∃ (bs : List w8) (b : Batch), ⌜e = interface.nil ∧ data = le8 bs.length ++ bs ∧
         (∀ b0, batchOk b0 → encBatch b0 = bs → b = b0) ∧ bs.length < 2 ^ 63⌝ ∗
         repCB t (DFrac.own 1) b) }}

theorem unmarshal_bounded : unmarshalB.spec (GF := GF) (hG := hG) := by
  intro t br rd I R
  wp_start as ⟨#Hcs, #Hok, Ht, #Hrd, Hown, #Hlen⟩
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hreads := bufio.bufioReadsOk br rd I $$ [Hbufio Hrd]
  · iframe Hbufio Hrd
  wp_auto
  have h0 : sint.Z (W64 0) = 0 := rfl
  have h8 : W64 8 - W64 0 = W64 8 := rfl
  rw [h0, go.arrayIndexRef_0, h8]
  ihave Hsl := slice_array b_ptr 8 _ (by decide) $$ b
  wp_apply bufio.wp_ReadFull _ (bufio.ownReader br rd I) R _ _ $$ [Hown Hsl]
    as %n %e1 ⟨%d1, %Hd1, Hsl, Hown, -⟩
  · iframe Hreads Hown Hsl
  cases e1 with
  | ok i1 =>
    wp_auto
    wp_end
    iexists d1
    iframe Hown
    ileft; ipureintro; intro h; cases h
  | nil =>
  have Hz8 : (zero_val (GoArray w8 8)).arr.length = 8 := by rfl
  have Hd8 : d1.length = 8 := by have := Hd1.2.2.1 rfl; rw [this, Hz8]
  rw [show (zero_val (GoArray w8 8)).arr.drop d1.length = [] by rw [Hd8]; rfl, List.append_nil]
  wp_auto
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hle := encoding.binary.isInit_access $$ Hbin
  icases Hle with ⟨#Hle, -⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply (encoding.binary.littleEndian.wp_Uint64 _ _ d1 [] (DFrac.own 1) Hd8) $$ [Hsl] as Hsl
  · simp only [List.append_nil]; iexact Hsl
  iunfold bufio.ownReader at Hown
  icases Hown with ⟨%pend0, %perr0, HI, Hrr⟩
  ihave %Hlt := Hlen $$ %d1 %pend0 [HI]
  · rw [List.append_assoc]; iexact HI
  have Hpos : 0 ≤ sint.Z (leToU64 d1) := leToU64_sint_nonneg d1 (Hlt Hd8)
  ihave Hown : bufio.ownReader br rd I (R ++ d1) $$ [HI Hrr]
  · iunfold bufio.ownReader
    iexists pend0, perr0
    iframe HI Hrr
  wp_apply (wp_slice_make2 (V := w8)) as %dsl ⟨Hdsl, Hdcap⟩
  · ipureintro; exact Hpos
  wp_apply bufio.wp_ReadFull _ (bufio.ownReader br rd I) (R ++ d1) _ _ $$ [Hown Hdsl]
    as %n2 %e2 ⟨%d2, %Hd2, Hdsl, Hown, -⟩
  · iframe Hreads Hown Hdsl
  cases e2 with
  | ok i2 =>
    wp_auto
    wp_end
    iexists d1 ++ d2
    rw [List.append_assoc]
    iframe Hown
    ileft; ipureintro; intro h; cases h
  | nil =>
  have Hd2l : d2.length = sint.nat (leToU64 d1) := by have := Hd2.2.2.1 rfl; simpa using this
  rw [show (List.replicate (sint.nat (leToU64 d1)) (zero_val w8)).drop d2.length = [] by
    simp [Hd2l], List.append_nil]
  ihave %Hcapwf := ownSliceCap_wf $$ Hdcap
  ihave %Hdl := ownSlice_len $$ Hdsl
  simp only [List.append_nil] at Hdl
  have Hn2 : n2 = dsl.len := by rw [Hd2.1]; word
  subst Hn2
  have Hsb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z dsl.len ∧ sint.Z dsl.len ≤ sint.Z dsl.cap :=
    ⟨by word, by word, Hcapwf.2⟩
  simp only [List.append_nil]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true Hsb)]
  ihave Hdsl := (ownSlice_trivial_slice dsl (DFrac.own 1) d2).1 $$ Hdsl
  wp_auto
  wp_apply (google_golang_org.protobuf.proto.Unmarshal.wp_proof _ (DFrac.own 1) d2 _
    (fun ok => if ok then iprop(∃ b0, repCB t (DFrac.own 1) b0 ∗
      ⌜∀ b1, batchOk b1 → encBatch b1 = d2 → b0 = b1⌝) else iprop(True))) $$ [Hdsl Ht]
    as %e3 ⟨%ok, -, %He3, Hpost, -⟩
  · iframe Hcs Hok Hdsl
    simp only [google_golang_org.protobuf.proto.PbCodec.unmarshal, unmarshalPre]
    iright; iright; iright; iright; iright; iright
    iexists t
    iframe Ht
    isplitr
    · ipureintro; rfl
    iunfold decInto
    isplit
    · iintro %v Hv %Hv0
      simp only [↓reduceIte]
      iexists v
      iframe Hv
      ipureintro; exact Hv0
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  cases e3 with
  | ok i3 =>
    wp_auto
    wp_end
    iexists d1 ++ d2
    rw [List.append_assoc]
    iframe Hown
    ileft; ipureintro; intro h; cases h
  | nil =>
    obtain rfl : ok = true := He3.1 rfl
    simp only [↓reduceIte]
    icases Hpost with ⟨%b0, Hb0, %Hb0⟩
    wp_auto
    wp_end
    iexists d1 ++ d2
    rw [List.append_assoc]
    iframe Hown
    iright
    iexists d2, b0
    iframe Hb0
    ipureintro
    refine ⟨rfl, ?_, Hb0, ?_⟩
    congr 1
    rw [← leToU64_le d1 Hd8, u64Le_le8, Hd2l]
    congr 1
    word
    have hlt := Hlt Hd8
    have h1 : uint.nat (leToU64 d1) = leNum d1 := by
      simp only [leToU64, leToU64Def, leNum_combine] at *
      simp [uint.nat]
      omega
    rw [Hd2l]
    word

end proofs

end Perennial.raxos
