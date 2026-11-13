/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/NewFileBufReader.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileBufReader
public import LinuxFs.Spec.bufio.NewReader

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

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileBufReader.wp_proof
    (HNew : bufio.NewReader.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileBufReader.spec (GF := GF) (hG := hG) := by
  intro ri S E r Q hty
  wp_start as ⟨HS, HFI⟩
  wp_auto
  wp_apply HNew ri S E r hty $$ [HS] as %b Hb
  · iframe
  ihave ⟨%q, HS, Hcl⟩ := bufio.ownReader_open b ri S E r $$ Hb
  wp_apply HFI $$ %(r ++ q) HS as %fi %err ⟨HS, HQ⟩
  ihave Hb := Hcl $$ HS
  iapply HΦ
  iexists b, fi, err
  iframe

end proof

end EtcdGrove
end Perennial
