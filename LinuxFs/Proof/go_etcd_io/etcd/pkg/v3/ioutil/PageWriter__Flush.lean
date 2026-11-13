/-
`(*PageWriter).Flush` (see `LinuxFs/Spec/go_etcd_io/etcd/pkg/v3/ioutil/PageWriter__Flush.lean`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.ioutil.PageWriter__Flush
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.ioutil.PageWriter__flush

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

theorem go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.Flush.wp_proof
    (wp_flush : go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.flush.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.Flush.spec (GF := GF) (hG := hG) := by
  intro pw wi W out pend
  iintro #Hw
  wp_start as ⟨Hpw, Hout⟩
  wp_auto
  wp_apply (wp_flush pw wi W out pend) $$ [Hw] [Hpw Hout] as %n %err ⟨%ys, %Hys, Hout, Hpw⟩
  · iexact Hw
  · iframe
  iapply HΦ
  iexists ys
  iframe
  ipureintro
  exact ⟨Hys.1, Hys.2.2⟩

end proof

end EtcdGrove
end Perennial
