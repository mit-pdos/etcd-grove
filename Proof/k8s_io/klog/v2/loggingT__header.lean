/-
The proof of `klog.loggingT.header.spec` (`Spec/k8s_io/klog/v2/loggingT__header.lean`), over the
trusted model `loggingT.header.impl` (`TrustedCode/k8s_io/klog/v2.lean`): a fresh `*buffer.Buffer`
(its embedded `bytes.Buffer` empty, `bytes.ownBuffer_new`), into which, `skipHeaders` being false
(klog's fact, `klogInit`), the model writes `"] "` with Perennial's `bytes.Buffer.WriteByte`.
klog-printf, 2026-11-23, etcd-grove#25. Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.loggingT__header
public import Perennial.Proof.bytes.Link

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

theorem klog.loggingT.header.wp_proof : klog.loggingT.header.spec (GF := GF) (hG := hG) := by
  intro s depth
  wp_start
  ihave Hk : (k8s_io.apiserver.pkg.storage.etcd3.klogInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold k8s_io.apiserver.pkg.storage.etcd3.klogInit at Hk
  icases Hk with ⟨-, -, -, -, #Hskip⟩
  have hty1 : (k8s_io.klog.v2.model.loggingT : go.GoType) = k8s_io.klog.v2.loggingT.ty := by
    with_unfolding_all rfl
  have hty2 : (k8s_io.klog.v2.model.settings : go.GoType) = k8s_io.klog.v2.settings.ty := by
    with_unfolding_all rfl
  simp only [hty1, hty2]
  wp_auto
  iStructNamed b
  ihave Hbuf := bytes.ownBuffer_new $$ Buffer
  wp_apply bytes.Buffer.wp_WriteByte $$ [$Hbuf] as Hbuf
  try wp_auto
  wp_apply bytes.Buffer.wp_WriteByte $$ [$Hbuf] as Hbuf
  try wp_auto
  iapply HΦ
  iexists _
  iframe Hbuf
  ipureintro
  simp

end proof

end EtcdGrove
end Perennial
