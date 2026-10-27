module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.codec__Encode
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.encodeObj
public import Spec.bytes.Buffer__Write

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]
variable [_root_.Perennial.bytes.Assumptions]

theorem codec.Encode.wp_proof (wp_encodeObj : encodeObj.spec (GF := GF) (hG := hG))
    (wp_Write : bytes.Buffer.Write.spec (GF := GF) (hG := hG)) :
    codec.Encode.spec (GF := GF) (hG := hG) := by
  intro p dq name val rv b bs
  wp_start as ⟨Hp, Hb⟩
  ihave #Pby : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_encodeObj $$ [$Hp] as %sl ⟨Hsl, Hp⟩
  (try wp_auto)
  wp_apply wp_Write $$ [$Hb $Hsl] as ⟨Hb, -⟩
  (try wp_auto)
  iapply HΦ
  iframe Hp Hb

end proof

end k8setcd3
end EtcdGrove
end Perennial
