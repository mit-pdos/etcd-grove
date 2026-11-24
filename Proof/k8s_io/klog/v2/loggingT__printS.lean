/-
The proof of `klog.loggingT.printS.spec` (`Spec/k8s_io/klog/v2/loggingT__printS.lean`), over its
translated body (`klog.go:835-854`; klog-infos, 2026-11-23, etcd-grove#25): `make([]byte, 0, 1024)`,
`strconv.AppendQuote` of the message into it (Perennial's), a buffer from the pool (`GetBuffer`), the
quoted message written to it (`bytes.Buffer.Write`), no error so `errKV` stays `nil`, the keys and
values serialized (`serialize.FormatKVs`, over `[][]interface{}{nil, keysAndValues}`),
`printDepth` of the embedded `*bytes.Buffer`, and the buffer given back (`PutBuffer`). Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.loggingT__printS
public import Spec.k8s_io.klog.v2.loggingT__printDepth
public import Spec.k8s_io.klog.v2.internal.buffer.GetBuffer
public import Spec.k8s_io.klog.v2.internal.buffer.PutBuffer
public import Spec.k8s_io.klog.v2.internal.serialize.FormatKVs
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.strconv.Link

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

theorem klog.loggingT.printS.wp_proof
    (wp_GetBuffer : klog.buffer.GetBuffer.spec (GF := GF) (hG := hG))
    (wp_PutBuffer : klog.buffer.PutBuffer.spec (GF := GF) (hG := hG))
    (wp_FormatKVs : klog.serialize.FormatKVs.spec (GF := GF) (hG := hG))
    (wp_printDepth : klog.loggingT.printDepth.spec (GF := GF) (hG := hG)) :
    klog.loggingT.printS.spec (GF := GF) (hG := hG) := by
  intro err s depth msg args xs dq hok hmsg
  wp_start as ⟨%h, Hargs⟩
  obtain ⟨rfl, hs⟩ := h
  ihave #Hstrconv : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave #Hbufp : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2.internal.buffer $$ []
  · iPkgInit
  ihave #Hser : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2.internal.serialize $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_slice_make3 (V := w8) (W64 0) (W64 1024) (by word)) as %q0 ⟨Hq0, Hq0c, -⟩
  try wp_auto
  wp_apply (strconv.wp_AppendQuote _ _ _ hmsg) $$ [$Hstrconv $Hq0 $Hq0c] as %qm ⟨%qb, Hqm, Hqmc⟩
  try wp_auto
  wp_apply wp_GetBuffer $$ [$Hbufp] as %b Hb
  try wp_auto
  iunfold k8s_io.apiserver.pkg.storage.etcd3.klogOwnBuffer at Hb
  icases Hb with ⟨Hbb, Htmp⟩
  wp_method_call
  try wp_auto
  wp_apply bytes.Buffer.wp_Write $$ [$Hbb $Hqm] as ⟨Hbb, Hqm⟩
  try wp_auto
  -- `[][]interface{}{errKV, keysAndValues}`, `errKV` `nil`
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %kvs ⟨Hkvs, -⟩
  have hl : ([zero_val GoSlice, zero_val GoSlice].set (sint.nat (W64 (0 + 1))) args) =
      [zero_val GoSlice, args] := by
    rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]; rfl
  rw [hl]
  ihave Hnil := ownSlice_nil (V := GoInterface) (GF := GF) dq
  wp_apply (wp_FormatKVs _ _ _ [zero_val GoSlice, args] [[], xs] dq (DFrac.own 1) ?_) $$
      [$Hser $Hbb $Hkvs Hnil Hargs] as ⟨⟨%q, Hbb⟩, -, Hsls⟩
  · intro ys hys x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hys
    rcases hys with rfl | rfl
    · simp at hx
    · exact hok x hx
  · iapply (BigSepL2.bigSepL2_cons).2
    iframe Hnil
    iapply (BigSepL2.bigSepL2_cons).2
    iframe Hargs
    iapply (BigSepL2.bigSepL2_nil).2
    itrivial
  icases (BigSepL2.bigSepL2_cons).1 $$ Hsls with ⟨-, Hsls⟩
  icases (BigSepL2.bigSepL2_cons).1 $$ Hsls with ⟨Hargs, -⟩
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %a1 ⟨Ha1, -⟩
  try wp_auto
  wp_apply wp_printDepth $$ [$Hpkg $Ha1 $Hbb] as ⟨-, Hbb⟩
  · ipureintro; exact ⟨rfl, rfl, hs⟩
  try wp_auto
  wp_apply wp_PutBuffer $$ [$Hbufp Hbb Htmp]
  · iunfold k8s_io.apiserver.pkg.storage.etcd3.klogOwnBuffer
    iframe
  try wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
