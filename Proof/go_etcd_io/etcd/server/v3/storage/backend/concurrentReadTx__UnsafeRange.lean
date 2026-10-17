/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/concurrentReadTx__UnsafeRange.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx__UnsafeRange
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.baseReadTx__UnsafeRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.concurrentReadTx.UnsafeRange.wp_proof
    (hbase : backend.baseReadTx.UnsafeRange.spec (GF := GF) (hG := hG)) :
    backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b crt rtx rv bk bi key endKey kb eb dk de limit Hnil Hsafe Hhas
  wp_start as ⟨Hs, #Hbk, Hk, He⟩
  unfold crtSnap
  icases Hs with ⟨%m, %Pb, %cm, %tm, %wg, %γw, %γo, %γt, %k, %q, %rt, %cst, #Hrt, #Htm, Hrb,
    #Hcst, #Hrtx, #Hcm, #Htm', #Hwg, Hown, #Hg, Hsh, #Hsnap, #Hintv, #Hwgi, %Hwf⟩
  unfold rdShare
  icases Hsh with ⟨Hlive, Hrc⟩
  wp_apply hbase γ P W Pk b (cbaseOf crt) DFrac.discard rtx rv q bk bi key endKey kb eb dk de limit
      Hnil Hsafe Hhas $$ [Hrb Hown Hlive $Hk $He]
    as %keys %vals ⟨Hbr, Hk, He, Hout⟩
  · isplitl [Hrb Hown Hlive]
    · unfold baseRd
      iexists m, Pb, cst
      iframe; iframe #
      isplitl
      · unfold stRd
        iexists cm, tm
        iframe; iframe #
        ipureintro; exact Hwf.2.2
      ipureintro; exact ⟨Hwf.1, Hwf.2.1, Or.inl rfl⟩
    unfold isBucket; iexact Hbk
  unfold baseRd
  icases Hbr with ⟨%m', %Pb', %cst', Hrb, #Hcst', Hsr, %Hwf'⟩
  ihave %Hsteq := stIf_agree (cbaseOf crt) cst cst' $$ [Hcst Hcst']
  · iframe #
  subst Hsteq
  unfold stRd
  icases Hsr with ⟨%cm', %tm', #Hrtx', #Hcm', #Htm'', Hown, -, Hlive, -, #Hintv', -⟩
  icombine Htm' Htm'' gives %Heq
  subst Heq
  iapply HΦ
  iframe
  iexists cm', wg, γw, γt, rt, cst
  iframe #
  ipureintro; exact ⟨Hwf.1, Hwf.2.1, Hwf.2.2⟩


end proof

end EtcdGrove
end Perennial
