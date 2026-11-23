/-
Package `proxy`: `ClientBatch.Unmarshal` from a `*bufio.Reader` with the decoded encoding's length
bound (`unmarshalB`), for `connectionListener` (it aligns the bytes read with the stream's frames).

Changed against the lab: the reader is the landed `bufio`'s `ownBufReader br ri Pre S E R` (every
non-empty read allowed), read with Perennial's `io.ReadFull` (`io.wp_ReadFull`, over
`bufio.ownBufReader_readerOk`); the 8-byte length's bound comes from a persistent, prefix-closed
fact `Φ` of the stream that the state `S` gives a step later (`hS`; for a connection
`Φ := protoPrefix P cn`, `net.connReader_proto`), asked of the length's bytes once they are read
(the lab asked it of the reader's state before the read); `proto.Unmarshal` is the hypothesis
`hyp.PbHyp.unmarshal`.
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
open EtcdGrove (bufio.ownBufReader)

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.proto.client.Assumptions] [raxos.replica.src.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions] [pb : hyp.PbHyp GF]

/-- `t.Unmarshal(br)` into a fresh `ClientBatch`, from a `*bufio.Reader` whose every non-empty read
is allowed, at a position `R` where the stream's fact `Φ` bounds the next 8 bytes' length: an
8-byte length and that many bytes read; on success they encode the decoded batch `b`. -/
abbrev unmarshalB.spec : Prop :=
  ∀ (t br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (R : List w8) (Φ : List w8 → IProp GF),
  (∀ r, Persistent (Φ r)) → (∀ r, S r ⊢ S r ∗ ▷ Φ r) → (∀ x y, Φ (x ++ y) ⊢ Φ x) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.proto.client ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ t ↦ (zero_val raxos.proto.client.ClientBatch) ∗
      bufio.ownBufReader br ri Pre S E R ∗ ⌜∀ r m, 0 < m → Pre r m⌝ ∗
      □ (∀ d, Φ (R ++ d) -∗ ⌜d.length = 8 → leNum d < 2 ^ 63⌝) }}
    (App (Val (t @!! go.GoType.PointerType raxos.proto.client.ClientBatch.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType Perennial.bufio.Reader.ty) #br)))
  {{ (e : GoInterface), RET #e; ∃ data : List w8, bufio.ownBufReader br ri Pre S E (R ++ data) ∗
      (⌜e ≠ interface.nil⌝ ∨
       ∃ (bs : List w8) (b : Batch), ⌜e = interface.nil ∧ data = le8 bs.length ++ bs ∧
         (∀ b0, batchOk b0 → encBatch b0 = bs → b = b0) ∧ bs.length < 2 ^ 63⌝ ∗
         (⌜∃ b0, batchOk b0 ∧ encBatch b0 = bs⌝ -∗ repCB t (DFrac.own 1) b)) }}

theorem um_len_eq (n2 l : w64) (d2 : List w8) (h1 : sint.Z n2 = d2.length)
    (h2 : d2.length = sint.nat l ∧ 0 ≤ sint.Z l) : n2 = l := by word

theorem um_len_lt (d1 d2 : List w8) (h : d2.length = sint.nat (leToU64 d1)) : d2.length < 2 ^ 63 := by
  rw [h]; word

theorem unmarshal_bounded : unmarshalB.spec (GF := GF) (hG := hG) := by
  intro t br ri Pre S E R Fs hFs hS hpre
  wp_start as ⟨Ht, Hown, %HPre, #Hlen⟩
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hio := EtcdGrove.bufio.io_init_of_bufio $$ Hbufio
  ihave #Hi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  iunfold errors.newVar at HEOF HUEOF
  icases HEOF with ⟨%xe, #HEOF, -⟩
  icases HUEOF with ⟨%xu, #HUEOF, -⟩
  ihave #Hrok := EtcdGrove.bufio.ownBufReader_readerOk EtcdGrove.bufio.Reader.Read.wp_proofOk
    br ri Pre S E
  have HPre' : ∀ (r0 : List w8) (n : Nat) (ys : List w8), ys.length ≤ n →
      (fun R m => 0 < m → Pre R m) (r0 ++ ys) (n - ys.length) :=
    fun r0 n ys _ hm => HPre _ _ hm
  wp_auto
  have h0 : sint.Z (W64 0) = 0 := rfl
  have h8 : W64 8 - W64 0 = W64 8 := rfl
  rw [h0, go.arrayIndexRef_0, h8]
  ihave Hsl := slice_array b_ptr 8 _ (by decide) $$ b
  rw [show interface.mkOk (go.GoType.PointerType Perennial.bufio.Reader.ty) #br =
    GoInterface.ok (EtcdGrove.bufio.readerIface br) from rfl]
  wp_apply (_root_.Perennial.io.wp_ReadFull (EtcdGrove.bufio.readerIface br)
      (fun R m => 0 < m → Pre R m) (bufio.ownBufReader br ri Pre S E) (EtcdGrove.bufio.errE E) R _ _
      _ _) $$ [Hown Hsl]
    as %n %e1 ⟨%d1, %Hd1, Hsl, Hown, #Hres⟩
  · iframe Hrok HEOF HUEOF Hown Hsl
    ipureintro; exact HPre' R _
  cases e1 with
  | ok i1 =>
    wp_auto
    wp_end
    iexists d1
    iframe Hown
    ileft; ipureintro; intro h; cases h
  | nil =>
  ihave %Hd8' : ⌜d1.length = (zero_val (GoArray w8 8)).arr.length⌝ $$ [Hres]
  · iunfold _root_.Perennial.io.readFullRes at Hres
    icases Hres with (%h | ⟨%e, %h, -⟩)
    · ipureintro; exact h.1
    · exfalso
      obtain ⟨-, hne, h1, h2⟩ := h
      by_cases hc : e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xe ∧ d1 ≠ []
      · exact absurd (h1 hc) (by intro h; cases h)
      · exact hne (h2 hc).symm
  have Hz8 : (zero_val (GoArray w8 8)).arr.length = 8 := by rfl
  have Hd8 : d1.length = 8 := by rw [Hd8', Hz8]
  rw [show (zero_val (GoArray w8 8)).arr.drop d1.length = [] by rw [Hd8]; rfl, List.append_nil]
  ihave ⟨Hown, #HFs⟩ := EtcdGrove.bufio.ownBufReader_fact br ri Pre S E (R ++ d1)
    (fun r => iprop(▷ Fs r)) hS (fun x y => later_mono (hpre x y)) $$ Hown
  wp_auto
  ihave %Hlt := Hlen $$ %d1 HFs
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hle := encoding.binary.isInit_access $$ Hbin
  icases Hle with ⟨#Hle, -⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply (encoding.binary.littleEndian.wp_Uint64 _ _ d1 [] (DFrac.own 1) Hd8) $$ [Hsl] as Hsl
  · simp only [List.append_nil]; iexact Hsl
  have Hpos : 0 ≤ sint.Z (leToU64 d1) := leToU64_sint_nonneg d1 (Hlt Hd8)
  wp_apply (wp_slice_make2 (V := w8)) as %dsl ⟨Hdsl, Hdcap⟩
  · ipureintro; exact Hpos
  wp_apply (_root_.Perennial.io.wp_ReadFull (EtcdGrove.bufio.readerIface br)
      (fun R m => 0 < m → Pre R m) (bufio.ownBufReader br ri Pre S E) (EtcdGrove.bufio.errE E)
      (R ++ d1) _ _ _ _) $$ [Hown Hdsl]
    as %n2 %e2 ⟨%d2, %Hd2, Hdsl, Hown, #Hres2⟩
  · iframe Hrok HEOF HUEOF Hown Hdsl
    ipureintro; exact HPre' (R ++ d1) _
  cases e2 with
  | ok i2 =>
    wp_auto
    wp_end
    iexists d1 ++ d2
    rw [List.append_assoc]
    iframe Hown
    ileft; ipureintro; intro h; cases h
  | nil =>
  ihave %Hd2l' : ⌜d2.length = (List.replicate (sint.nat (leToU64 d1)) (zero_val w8)).length⌝ $$ [Hres2]
  · iunfold _root_.Perennial.io.readFullRes at Hres2
    icases Hres2 with (%h | ⟨%e, %h, -⟩)
    · ipureintro; exact h.1
    · exfalso
      obtain ⟨-, hne, h1, h2⟩ := h
      by_cases hc : e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xe ∧ d2 ≠ []
      · exact absurd (h1 hc) (by intro h; cases h)
      · exact hne (h2 hc).symm
  have Hd2l : d2.length = sint.nat (leToU64 d1) := by simpa using Hd2l'
  rw [show (List.replicate (sint.nat (leToU64 d1)) (zero_val w8)).drop d2.length = [] by
    simp [Hd2l], List.append_nil]
  ihave %Hcapwf := ownSliceCap_wf $$ Hdcap
  ihave %Hdl := ownSlice_len $$ Hdsl
  simp only [List.append_nil] at Hdl
  have Hn2 : n2 = dsl.len := um_len_eq n2 dsl.len d2 Hd2.1 Hdl
  subst Hn2
  have Hsb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z dsl.len ∧ sint.Z dsl.len ≤ sint.Z dsl.cap :=
    ⟨by word, by word, Hcapwf.2⟩
  simp only [List.append_nil]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true Hsb)]
  ihave Hdsl := (ownSlice_trivial_slice dsl (DFrac.own 1) d2).1 $$ Hdsl
  wp_auto
  wp_apply (pb.unmarshal _ (DFrac.own 1) d2 _
    (fun ok => if ok then iprop(∃ b0,
      (⌜∃ b1, batchOk b1 ∧ encBatch b1 = d2⌝ -∗ repCB t (DFrac.own 1) b0) ∗
      ⌜∀ b1, batchOk b1 → encBatch b1 = d2 → b0 = b1⌝) else iprop(True))) $$ [Hdsl Ht]
    as %e3 ⟨%ok, -, %He3, Hpost, -⟩
  · iframe Hdsl
    unfold unmarshalPre
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
    refine ⟨rfl, ?_, Hb0, um_len_lt d1 d2 Hd2l⟩
    congr 1
    rw [← leToU64_le d1 Hd8, u64Le_le8, Hd2l]
    congr 1
    word

end proofs
end Perennial.raxos
