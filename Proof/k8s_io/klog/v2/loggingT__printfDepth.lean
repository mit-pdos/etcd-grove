/-
The proof of `klog.loggingT.printfDepth.spec` (`Spec/k8s_io/klog/v2/loggingT__printfDepth.lean`),
over klog's translated `printfDepth` (`klog.go:764-784`; klog-printf, 2026-11-23, etcd-grove#25):
`header` gives a `*buffer.Buffer` holding a header not ending in a newline; with no logger and no
filter, `fmt.Fprintf` formats the arguments into it (Perennial's `fmt.wp_Fprintf_bytes`, the
`[]string` arguments lent, `klog.argsOk_lend`; the writer the embedded `bytes.Buffer`'s `Write`); the
last byte is read (`buf.Bytes()[buf.Len()-1]`, in bounds: the buffer holds at least the header), a
newline appended if it is not one (`bytes.Buffer.WriteByte`), and `output` called. Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.loggingT__printfDepth
public import Spec.k8s_io.klog.v2.loggingT__header
public import Spec.k8s_io.klog.v2.loggingT__output
public import Proof.k8s_io.klog.v2.ArgsLend
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.bytes.BufferWriter
public import Perennial.Proof.fmt.BytesResults
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

theorem klog.loggingT.printfDepth.wp_proof
    (wp_header : klog.loggingT.header.spec (GF := GF) (hG := hG))
    (wp_output : klog.loggingT.output.spec (GF := GF) (hG := hG)) :
    klog.loggingT.printfDepth.spec (GF := GF) (hG := hG) := by
  intro s logger filter depth f args xs dq
  wp_start as ⟨%h, Hargs, Hok⟩
  obtain ⟨rfl, rfl, hs⟩ := h
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_header as %b %file %line ⟨%bs, %hbs, Hbuf⟩
  try wp_auto
  -- the embedded `bytes.Buffer` of the `*buffer.Buffer` `b`
  -- (`bf`)
  -- `*buffer.Buffer`'s `Write`, promoted from the embedded `bytes.Buffer`'s, is a writer for `Fprintf`
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
  imod klog.argsOk_lend f xs $$ Hok with ⟨%B, Hown, #HokB, Hok⟩
  wp_apply (fmt.wp_Fprintf_bytes B DFrac.discard _ f args xs dq
      (bytes.ownBuffer (structFieldRef k8s_io.klog.v2.internal.buffer.Buffer go!"Buffer" b) bs)
      (fun s0 _ _ => bytes.ownBuffer
        (structFieldRef k8s_io.klog.v2.internal.buffer.Buffer go!"Buffer" b) (bs ++ s0))) $$
      [$Hfmt $Hargs $Hown $HokB $Hbuf] as %n %err ⟨Hargs, -, %out, -, Hbuf⟩
  · iexists _
    isplitr
    · ipureintro; rfl
    · iapply hW
  try wp_auto
  -- `buf.Bytes()[buf.Len()-1]`: through `bytes.Buffer`'s `Bytes` and `Len` bodies, on the buffer's
  -- fields (as Perennial's proof of `Bytes`)
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
  have Hb : 0 ≤ sint.Z off ∧ sint.Z off ≤ sint.Z bb.len ∧ sint.Z bb.len ≤ sint.Z bb.cap :=
    ⟨Hoff.1, by word, Hwf.2⟩
  simp only [Hb, _root_.and_self, ↓reduceIte]
  icases (ownSlice_split_all off bb _ _ ⟨Hoff.1, by word⟩).1 $$ Hsl with ⟨Hsl1, Hsl2⟩
  try wp_auto
  wp_method_call
  try wp_auto
  wp_method_call
  try wp_auto
  -- the last byte, in bounds: the buffer holds the header, `bs ≠ []`
  have hvl : (List.drop (sint.nat off) all).length = (bs ++ out).length := by rw [← Hoff.2.2]
  have hbs1 : 1 ≤ (bs ++ out).length := by
    rw [List.length_append]; have := List.length_pos_iff.mpr hbs.1; omega
  have hvl2 : (List.drop (sint.nat off) all).length = sint.nat bb.len - sint.nat off := by
    rw [List.length_drop]; omega
  have hlen1 : 1 ≤ sint.nat bb.len - sint.nat off := by omega
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
  ihave Hbuf : bytes.ownBuffer
      (structFieldRef k8s_io.klog.v2.internal.buffer.Buffer go!"Buffer" b) (bs ++ out) $$
      [bufB offB lastReadB Hsl Hcap]
  · unfold bytes.ownBuffer
    iexists ⟨bb, off, lr⟩, all
    iframe Hsl Hcap
    isplitl
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ipureintro
    exact Hoff
  -- a newline appended unless the message ends in one, then `output`
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
