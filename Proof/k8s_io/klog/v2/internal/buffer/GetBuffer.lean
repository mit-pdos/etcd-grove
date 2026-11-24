/-
The proof of `klog.buffer.GetBuffer.spec` (`Spec/k8s_io/klog/v2/internal/buffer/GetBuffer.lean`), over
its translated body (`buffer.go:52-56`; klog-infos, 2026-11-23, etcd-grove#25): `buffers.Get()`
(Perennial's `sync.Pool`, with klog's fact: the pool's `New` is not `nil`, so `Get` returns one of
its elements, a `*Buffer` owned whole), the type assertion to `*Buffer`, and the promoted `Reset`
(Perennial's `bytes.Buffer.Reset`). Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.internal.buffer.GetBuffer
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

theorem klog.buffer.GetBuffer.wp_proof : klog.buffer.GetBuffer.spec (GF := GF) (hG := hG) := by
  wp_start as -
  ihave Hk : (k8s_io.apiserver.pkg.storage.etcd3.klogBufferInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold k8s_io.apiserver.pkg.storage.etcd3.klogBufferInit at Hk
  icases Hk with ⟨%f, %hf, #Hpool⟩
  wp_auto
  wp_apply (sync.Pool.wp_Get _ f iprop(True) k8s_io.apiserver.pkg.storage.etcd3.klogPoolElem) $$
      [$Hsync $Hpool] as %x ⟨Hx, -⟩
  icases Hx with (Hx | %h)
  · iunfold k8s_io.apiserver.pkg.storage.etcd3.klogPoolElem at Hx
    icases Hx with ⟨%l, %bs, %hx, Hown⟩
    subst hx
    wp_auto
    iunfold k8s_io.apiserver.pkg.storage.etcd3.klogOwnBuffer at Hown
    icases Hown with ⟨Hb, Htmp⟩
    wp_method_call
    try wp_auto
    wp_apply bytes.Buffer.wp_Reset $$ [$Hb] as Hb
    try wp_auto
    iapply HΦ
    iunfold k8s_io.apiserver.pkg.storage.etcd3.klogOwnBuffer
    iframe
  · exact absurd h.1 hf

end proof

end EtcdGrove
end Perennial
