/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/pkg/v3/crc/digest__Sum32.lean`: the translated body.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.digest__Sum32

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

theorem go_etcd_io.etcd.pkg.v3.crc.digest.Sum32.wp_proof :
    go_etcd_io.etcd.pkg.v3.crc.digest.Sum32.spec (GF := GF) (hG := hG) := by
  intro l c tab dq
  wp_start as Hl
  ihave %Hn := typedPointsto_not_null l _ dq $$ Hl
  iStructNamed Hl
  wp_auto
  iapply HΦ
  iapply typedPointsto_combine l _ dq Hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end EtcdGrove
end Perennial
