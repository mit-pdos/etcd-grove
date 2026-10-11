/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/NewStorage.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.NewStorage
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem NewStorage.wp_proof
    (wp_NewMemoryStorage : NewMemoryStorage.spec (GF := GF) (hG := hG)) :
    NewStorage.spec (GF := GF) (hG := hG) := by
  intro vsl voters
  wp_start as ⟨#Hreg, #Hv⟩
  wp_auto
  wp_apply wp_NewMemoryStorage as %ms %γs Hown
  wp_alloc s as Hs
  iStructNamed Hs
  imod regStor_register s ms γs ⊤ CoPset.subseteq_top $$ Hreg MemoryStorage with #Hrec
  ipersist voters
  wp_auto
  iapply HΦ
  iexists ms, γs
  iframe Hrec voters Hown

end proof

end register
end EtcdGrove
end Perennial
