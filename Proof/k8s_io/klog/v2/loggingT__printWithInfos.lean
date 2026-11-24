/-
The proof of `klog.loggingT.printWithInfos.spec` (`Spec/k8s_io/klog/v2/loggingT__printWithInfos.lean`),
over its translated body (`klog.go:742-758`; klog-infos, 2026-11-23, etcd-grove#25): no logger, no
filter; `fmt.Fprint(buf, args...)` (Perennial's `fmt.wp_Fprint`, the one operand a `*bytes.Buffer`
whose `String()` is lent its buffer, `fmt.printArgOk_bytesBuffer`; the writer the embedded
`bytes.Buffer`'s `Write`); `buf.Len() == 0 || buf.Bytes()[buf.Len()-1] != '\n'` (in bounds: the
second test only on a non-empty buffer), a newline appended if so, and `output`. Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.loggingT__printWithInfos
public import Spec.k8s_io.klog.v2.loggingT__output
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.bytes.BufferWriter
public import Perennial.Proof.fmt.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.klog.v2.Assumptions]

theorem klog.loggingT.printWithInfos.wp_proof
    (wp_output : klog.loggingT.output.spec (GF := GF) (hG := hG)) :
    klog.loggingT.printWithInfos.spec (GF := GF) (hG := hG) := by
  intro b hdr file line s logger filter depth args dq lb bs
  wp_start as ⟨%h, Hbuf, Hargs, Hlb⟩
  obtain ⟨rfl, rfl, hs⟩ := h
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  -- `*buffer.Buffer`'s `Write`, promoted from the embedded `bytes.Buffer`'s, is a writer for `Fprint`
  have hW : ∀ bs0 : List w8, ⊢ fmt.writeSpec (GF := GF)
      ⟨go.GoType.PointerType k8s_io.klog.v2.internal.buffer.Buffer.ty, #b⟩
      (bytes.ownBuffer (structFieldRef k8s_io.klog.v2.internal.buffer.Buffer go!"Buffer" b) bs0)
      (fun s0 _ _ => bytes.ownBuffer (structFieldRef k8s_io.klog.v2.internal.buffer.Buffer go!"Buffer" b) (bs0 ++ s0)) := by
    intro bs0
    unfold fmt.writeSpec
    iintro %sl %s0 %Φw HP Hsl HΦw
    dsimp only
    wp_method_call
    try wp_auto
    wp_apply bytes.Buffer.wp_Write _ bs0 sl (DFrac.own 1) s0 $$ [$HP $Hsl] as ⟨HP, Hsl⟩
    iapply HΦw $$ Hsl HP
  ihave #Hx := fmt.printArgOk_bytesBuffer bytes.Buffer.wp_String lb bs
  wp_apply (fmt.wp_Fprint _ args _ dq
      (bytes.ownBuffer (structFieldRef k8s_io.klog.v2.internal.buffer.Buffer go!"Buffer" b) hdr)
      (bytes.ownBuffer lb bs)
      (fun s0 _ _ => bytes.ownBuffer
        (structFieldRef k8s_io.klog.v2.internal.buffer.Buffer go!"Buffer" b) (hdr ++ s0))) $$
      [$Hfmt $Hargs $Hlb $Hbuf] as %n %err ⟨Hargs, Hlb, %out, Hbuf⟩
  · isplitl []
    · iapply (BigSepL.bigSepL_singleton).2
      iexact Hx
    iexists _
    isplitr
    · ipureintro; rfl
    · iapply hW
  try wp_auto
  -- `buf.Len() == 0 || buf.Bytes()[buf.Len()-1] != '\n'`: through `bytes.Buffer`'s `Len` and `Bytes`
  -- bodies, on the buffer's fields (as `printfDepth`'s proof)
  iunfold bytes.ownBuffer at Hbuf
  icases Hbuf with ⟨%bb0, %all, Hl, Hsl, Hcap, %Hoff⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hwf := ownSlice_wf $$ Hsl
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨bb, off, lr⟩ := bb0
  simp only at Hoff Hlen Hwf ⊢
  iStructNamedSuffix Hl "B"
  wp_method_call
  try wp_auto
  wp_method_call
  try wp_auto
  -- the buffer back, unchanged
  have rebuild : ∀ all' : List w8, all' = all →
      (bb ↦* all' ∗ ownSliceCap w8 bb (DFrac.own 1) ∗
        typedPointsto (structFieldRef bytes.Buffer go!"buf"
          (structFieldRef k8s_io.klog.v2.internal.buffer.Buffer go!"Buffer" b)) bb (DFrac.own 1) ∗
        typedPointsto (structFieldRef bytes.Buffer go!"off"
          (structFieldRef k8s_io.klog.v2.internal.buffer.Buffer go!"Buffer" b)) off (DFrac.own 1) ∗
        typedPointsto (structFieldRef bytes.Buffer go!"lastRead"
          (structFieldRef k8s_io.klog.v2.internal.buffer.Buffer go!"Buffer" b)) lr (DFrac.own 1) :
          IProp GF) ⊢
      bytes.ownBuffer (structFieldRef k8s_io.klog.v2.internal.buffer.Buffer go!"Buffer" b)
        (hdr ++ out) := by
    rintro all' rfl
    iintro ⟨Hsl, Hcap, bufB, offB, lastReadB⟩
    unfold bytes.ownBuffer
    iexists ⟨bb, off, lr⟩, all'
    iframe Hsl Hcap
    isplitl
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ipureintro
    exact Hoff
  by_cases h0 : bb.len - off = W64 0
  · simp only [h0, decide_true]
    try wp_auto
    ihave Hbuf := rebuild all rfl $$ [Hsl Hcap bufB offB lastReadB]
    · iframe
    wp_method_call
    try wp_auto
    wp_apply bytes.Buffer.wp_WriteByte $$ [$Hbuf] as Hbuf
    try wp_auto
    wp_apply wp_output $$ []
    · ipureintro; exact ⟨rfl, hs⟩
    try wp_auto
    iapply HΦ
    iframe
  simp only [h0, decide_false]
  try wp_auto
  wp_method_call
  try wp_auto
  wp_method_call
  try wp_auto
  have Hb : 0 ≤ sint.Z off ∧ sint.Z off ≤ sint.Z bb.len ∧ sint.Z bb.len ≤ sint.Z bb.cap :=
    ⟨Hoff.1, by word, Hwf.2⟩
  simp only [Hb, _root_.and_self, ↓reduceIte]
  icases (ownSlice_split_all off bb _ _ ⟨Hoff.1, by word⟩).1 $$ Hsl with ⟨Hsl1, Hsl2⟩
  try wp_auto
  wp_method_call
  try wp_auto
  wp_method_call
  try wp_auto
  have hvl2 : (List.drop (sint.nat off) all).length = sint.nat bb.len - sint.nat off := by
    rw [List.length_drop]; omega
  have hlen1 : 1 ≤ sint.nat bb.len - sint.nat off := by
    have : bb.len - off ≠ W64 0 := h0
    have : sint.Z off ≠ sint.Z bb.len := by
      intro h; apply this; word
    have : sint.Z off ≤ sint.Z bb.len := by word
    word
  have hi : 0 ≤ sint.Z (bb.len - off - W64 1) ∧ sint.Z (bb.len - off - W64 1) < sint.Z (bb.len - off) := by
    constructor <;> word
  have hi2 : (sint.Z (bb.len - off - W64 1)).toNat < (List.drop (sint.nat off) all).length := by
    rw [hvl2]; word
  simp only [hi, _root_.and_self, ↓reduceIte]
  icases ownSlice_elem_acc (sint.Z (bb.len - off - W64 1)) _ _ _ _ hi.1
      (List.getElem?_eq_getElem hi2) $$ Hsl2 with ⟨Hc, Hsl2⟩
  try wp_auto
  ihave Hsl2 := Hsl2 $$ Hc
  rw [List.set_getElem_self]
  ihave Hsl := ownSlice_combine (GF := GF) (V := w8) off bb (DFrac.own 1) _ _ (W64 0) bb.len
      ⟨by rw [List.length_take]; word, by decide, Hoff.1, by word⟩ $$ Hsl1 Hsl2
  ihave Hsl := ownSlice_trivial_slice_2 $$ Hsl
  rw [List.take_append_drop]
  ihave Hbuf := rebuild all rfl $$ [Hsl Hcap bufB offB lastReadB]
  · iframe
  wp_if_destruct
  · try wp_auto
    wp_apply wp_output $$ []
    · ipureintro; exact ⟨rfl, hs⟩
    try wp_auto
    iapply HΦ
    iframe
  · try wp_auto
    wp_method_call
    try wp_auto
    wp_apply bytes.Buffer.wp_WriteByte $$ [$Hbuf] as Hbuf
    try wp_auto
    wp_apply wp_output $$ []
    · ipureintro; exact ⟨rfl, hs⟩
    try wp_auto
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
