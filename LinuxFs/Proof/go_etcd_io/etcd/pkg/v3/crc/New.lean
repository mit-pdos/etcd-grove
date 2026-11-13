/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/pkg/v3/crc/New.lean`: the translated body.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.New

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
variable [go_etcd_io.etcd.pkg.v3.crc.Assumptions]

theorem go_etcd_io.etcd.pkg.v3.crc.New.wp_proof :
    go_etcd_io.etcd.pkg.v3.crc.New.spec (GF := GF) (hG := hG) := by
  intro prev tab
  wp_start as -
  wp_auto
  wp_alloc l as Hl
  wp_pure
  wp_auto
  iapply HΦ
  iexact Hl

end proof

end EtcdGrove
end Perennial
