/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/readTx__UnsafeRange.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__UnsafeRange
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

theorem backend.readTx.UnsafeRange.wp_proof
    (hbase : backend.baseReadTx.UnsafeRange.spec (GF := GF) (hG := hG)) :
    backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b rt rtx rv qo bk bi key endKey kb eb dk de limit Hnil Hsafe Hhas
  wp_start as ⟨#Hb, #Hrt, Hh, Hopen, #Hbk, Hk, He⟩
  unfold rtHeld
  icases Hh with ⟨%rt', %rd, %H, #Hrt', Hrl, HR, %Hrtx, Hcr⟩
  icombine Hrt Hrt' gives %Heq
  subst Heq
  subst Hrtx
  unfold isBackend
  icases Hb with ⟨%t, %rt2, %tm, %db, %lg, %h, -, #Hrt2, -, -, -, -, -, #Htm, -, -, -, #Hg, -, -, -,
    -, -, %HPwf⟩
  icombine Hrt Hrt2 gives %Heq
  subst Heq
  unfold crTok
  icases Hcr with ⟨%rt3, %tm3, #Hrt3, #Htm3, Hown, Hrdt⟩
  icombine Hrt Hrt3 gives %Heq
  subst Heq
  ihave %Heq := rtmuAt_agree rt tm tm3 $$ []
  · iframe #
  subst Heq
  unfold rtResAt rtRest rtCore rtIntv
  icases HR with ⟨%m, %Pb, %cm, Hrb, %Hok, Hcm, Hview, Hrd, Hrvs, Hcur, Hhist, ⟨#Hst, Hrtxf⟩, Hwg,
    %Hfacts, #Hha, #Hcv, Hpo, #Hauth, Hiv⟩
  ihave #Htm0 := Htm
  iunfold rtmuAt at Htm0
  icases Htm0 with ⟨%st0, #Hst0, #Htmo⟩
  ihave %Hsteq := stIf_agree (baseOf rt) st0 rd.st $$ []
  · iframe #
  subst Hsteq
  cases hl : rd.live
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hiv with ⟨-, #Hst⟩
    iexfalso
    iapply bOpen_stopped γ qo $$ [$Hopen $Hst]
  simp only [↓reduceIte]
  icases Hiv with ⟨Hlive, #Hsnap, #Hintv, #Hwgi, Hwo⟩
  wp_apply hbase γ P W Pk b (baseOf rt) (DFrac.own sync.rfrac) rd.rtx rv sync.rfrac.half bk bi key
      endKey kb eb dk de limit Hnil Hsafe Hhas $$ [Hrb Hrtxf Hcm Hown Hlive $Hk $He]
    as %keys %vals ⟨Hbr, Hk, He, Hout⟩
  · isplitl [Hrb Hrtxf Hcm Hown Hlive]
    · unfold baseRd
      iexists m, Pb, rd.st
      iframe; iframe #
      isplitl
      · unfold stRd
        iexists cm, tm
        iframe; iframe #
        ipureintro; exact HPwf
      ipureintro; exact ⟨Hfacts.1, Hfacts.2.1, Or.inr Hok⟩
    unfold isBucket; iexact Hbk
  unfold baseRd
  icases Hbr with ⟨%m', %Pb', %st', Hrb, #Hst', Hsr, %Hwf'⟩
  ihave %Hsteq := stIf_agree (baseOf rt) rd.st st' $$ [Hst0 Hst']
  · iframe #
  rw [← Hsteq]
  unfold stRd
  icases Hsr with ⟨%cm', %tm', Hrtxf, Hcm, #Htm', Hown, -, Hlive, -, #Hintv', -⟩
  icombine Htmo Htm' gives %Heq
  subst Heq
  have Hok' : bksOk Pb' rv.2.bks := by
    rcases Hwf'.2.2 with h | h
    · cases h
    · exact h
  iapply HΦ
  iframe
  rw [hl]
  simp only [↓reduceIte]
  iframe; iframe #
  ipureintro; exact ⟨Hok', Hfacts⟩


end proof

end EtcdGrove
end Perennial
