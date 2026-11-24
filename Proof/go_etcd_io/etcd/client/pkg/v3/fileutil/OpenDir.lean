/-
The proof of `Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/OpenDir.lean`.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir
public import Proof.os.NsAbove
public import Proof.os.NsSOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.wp_proof :
    go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.spec (GF := GF) (hG := hG) := by
  intro p R j dq qc
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm⟩
  wp_auto
  wp_apply os.Open.wp_dirSOk p R j dq qc $$ [Hinv Hsi Hp Hperm] as %f %err Hr
  · iframe; (repeat' isplitl []) <;> (first | iassumption | iPkgInit)
  iapply HΦ
  iexact Hr

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.wp_proofAboveRoot :
    go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.specAboveRoot (GF := GF) (hG := hG) := by
  intro p R hp
  wp_start as ⟨#Hinv, #Hsi, #Hab⟩
  wp_auto
  wp_apply os.Open.wp_aboveS p R (os.aboveRoot_rootsAbove hp) $$ []
    as %f %err Hr
  · (repeat' isplitl []) <;> (first | iassumption | iPkgInit)
  iapply HΦ
  iexact Hr

end proof

end EtcdGrove
end Perennial
