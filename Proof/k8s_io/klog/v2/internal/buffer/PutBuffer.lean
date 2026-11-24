/-
The proof of `klog.buffer.PutBuffer.spec` (`Spec/k8s_io/klog/v2/internal/buffer/PutBuffer.lean`), over
its translated body (`buffer.go:59-72`; klog-infos, 2026-11-23, etcd-grove#25): the promoted `Len`
(Perennial's `bytes.Buffer.Len`); a buffer of 256 bytes or more is dropped, any other given to the
pool (Perennial's `sync.Pool.Put`, with klog's fact: an element is a `*Buffer` owned whole).
Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.internal.buffer.PutBuffer
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.sync.Link

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
variable [package_sem : k8s_io.klog.v2.internal.buffer.Assumptions]

theorem klog.buffer.PutBuffer.wp_proof : klog.buffer.PutBuffer.spec (GF := GF) (hG := hG) := by
  intro b bs
  wp_start as Hown
  ihave Hk : (k8s_io.apiserver.pkg.storage.etcd3.klogBufferInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold k8s_io.apiserver.pkg.storage.etcd3.klogBufferInit at Hk
  icases Hk with ⟨%f, %hf, #Hpool⟩
  wp_auto
  iunfold k8s_io.apiserver.pkg.storage.etcd3.klogOwnBuffer at Hown
  icases Hown with ⟨Hb, Htmp⟩
  iunfold bytes.ownBuffer at Hb
  icases Hb with ⟨%bb, %all, Hl, Hsl, Hcap, %Hoff⟩
  wp_method_call
  try wp_auto
  wp_apply bytes.Buffer.wp_Len $$ [$Hl] as Hl
  try wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ; itrivial
  · try wp_auto
    wp_apply sync.Pool.wp_Put $$ [$Hsync $Hpool Hl Hsl Hcap Htmp]
    · iunfold k8s_io.apiserver.pkg.storage.etcd3.klogPoolElem
      iexists b, bs
      isplitr
      · ipureintro; rfl
      iunfold k8s_io.apiserver.pkg.storage.etcd3.klogOwnBuffer
      iframe Htmp
      iunfold bytes.ownBuffer
      iexists bb, all
      iframe
      ipureintro; exact Hoff
    try wp_auto
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
