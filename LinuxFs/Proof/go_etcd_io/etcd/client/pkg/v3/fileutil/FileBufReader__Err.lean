/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/FileBufReader__Err.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader__Err


@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.Err.wp_proof : go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.Err.spec (GF := GF) (hG := hG) := by
  intro fbr b fi err dq
  wp_start as Hf
  ihave %Hn := typedPointsto_not_null fbr _ _ $$ Hf
  iStructNamed Hf
  wp_auto
  iapply HΦ
  iapply typedPointsto_combine fbr _ _ Hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end EtcdGrove
end Perennial
