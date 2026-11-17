/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__UnsafeForEach.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeForEach
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.unsafeForEach

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.batchTx.UnsafeForEach.wp_proof
    (hfe : backend.unsafeForEach.spec (GF := GF) (hG := hG)) :
    backend.batchTx.UnsafeForEach.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st bk bi fn I E
  wp_start as ⟨#Hb, #Ht, Hw, #Hbk, HI, #Hf⟩
  unfold btW
  icases Hw with ⟨Htx, Hpend, ⟨%G, Hwtx⟩⟩
  wp_auto
  wp_apply (hfe st.tx (.wr γ.db st.C st.S G) bk bi fn I E) $$ [Hwtx HI]
    as %err ⟨Hwtx, Hres⟩
  · simp only [feOwn, FeSide.data, FeSide.q]; iframe; iframe #
  iapply HΦ
  simp only [feOwn, FeSide.data]
  iframe
  iexists G
  iexact Hwtx

end proof

end EtcdGrove
end Perennial
