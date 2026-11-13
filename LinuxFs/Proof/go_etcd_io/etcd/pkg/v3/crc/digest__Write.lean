/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/pkg/v3/crc/digest__Write.lean`: the translated body.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.digest__Write

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

theorem go_etcd_io.etcd.pkg.v3.crc.digest.Write.wp_proof
    (Hupd : hash.crc32.Update.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.pkg.v3.crc.digest.Write.spec (GF := GF) (hG := hG) := by
  intro l c tab s bs dq
  wp_start as ⟨Hl, #Ht, Hs⟩
  ihave %Hn := typedPointsto_not_null l _ _ $$ Hl
  iStructNamed Hl
  wp_auto
  wp_apply Hupd $$ [Hs] as Hs
  · iframe; iexact Ht
  wp_auto
  iapply HΦ
  iframe Hs
  iapply typedPointsto_combine l _ _ Hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end EtcdGrove
end Perennial
