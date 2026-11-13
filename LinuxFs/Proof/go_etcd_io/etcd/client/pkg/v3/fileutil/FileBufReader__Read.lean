/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/FileBufReader__Read.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader__Read
public import LinuxFs.Spec.bufio.Reader__Read

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

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.Read.wp_proof
    (HRead : bufio.Reader.Read.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.Read.spec (GF := GF) (hG := hG) := by
  intro fbr b fi err dq ri S E r p xs
  iintro #Hrs #HSb
  wp_start as ⟨%Hrx, Hf, Hb, Hp⟩
  ihave %Hn := typedPointsto_not_null fbr _ _ $$ Hf
  iStructNamed Hf
  wp_auto
  wp_apply HRead b ri S E r p xs $$ Hrs HSb [Hb Hp] as %n %e ⟨%ys, %Hys, Hp, Hb⟩
  · iframe; ipureintro; exact Hrx
  iapply HΦ
  iexists ys
  iframe
  isplitl []
  · ipureintro; exact Hys
  · iapply typedPointsto_combine fbr _ _ Hn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

end proof

end EtcdGrove
end Perennial
