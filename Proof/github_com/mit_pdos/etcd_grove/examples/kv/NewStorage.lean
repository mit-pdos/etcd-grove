/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/NewStorage.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.NewStorage
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

theorem NewStorage.wp_proof
    (wp_NewMemoryStorage : NewMemoryStorage.spec (GF := GF) (hG := hG)) :
    NewStorage.spec (GF := GF) (hG := hG) := by
  intro vsl voters
  wp_start as ⟨#Hreg, #Hv⟩
  iapply wp_fupd
  wp_auto
  wp_apply wp_NewMemoryStorage as %ms %γs ⟨Hl, Hlog, He, Hnone, Hmeta, Hfresh⟩
  irename «$r0» => Hs
  generalize «$r0_ptr» = s at *
  iStructNamed Hs
  imod kvStor_register s ms γs ⊤ CoPset.subseteq_top $$ Hreg MemoryStorage with #Hrec
  ipersist voters
  imodintro
  iapply HΦ
  iexists ms, γs
  iframe Hrec voters Hl Hlog He Hnone Hmeta Hfresh

end proof

end kv
end EtcdGrove
end Perennial
