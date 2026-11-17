/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/readTx__UnsafeForEach.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__UnsafeForEach
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.baseReadTx__UnsafeForEach

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

theorem backend.readTx.UnsafeForEach.wp_proof
    (hbase : backend.baseReadTx.UnsafeForEach.spec (GF := GF) (hG := hG)) :
    backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b rt rtx rv p bk bi fn I E
  wp_start as ⟨#Hb, #Hrt, Hh, #Hbk, HI, #Hvis⟩
  unfold rtHeldF
  icases Hh with ⟨%rt', %rd, %H, %L, #Hrt', Hrl, HR, %Hrtx, Hcr⟩
  icombine Hrt Hrt' gives %Heq
  subst Heq
  obtain ⟨Hrtx, Hnn⟩ := Hrtx
  subst Hrtx
  unfold isBackend
  icases Hb with ⟨%t, %rt2, %tm, %db, %lg, %h, -, #Hrt2, -, -, -, -, -, #Htm, -, -, -, #Hg, -, -, -,
    -, -, %HPwf, -⟩
  icombine Hrt Hrt2 gives %Heq
  subst Heq
  unfold crTok
  icases Hcr with ⟨%rt3, %tm3, #Hrt3, #Htm3, Hown, Hrdt⟩
  icombine Hrt Hrt3 gives %Heq
  subst Heq
  icombine Htm Htm3 gives %Heq
  subst Heq
  unfold rtResAt rtRest rtCore rtIntv
  icases HR with ⟨%m, %Pb, %cm, Hrb, %Hok, Hcm, Hview, Hrd, Hrvs, Hcur, Hcln, Hhist, Hrtxf, Hwg, %Hfacts,
    #Hha, #Hcv, Hpo, #Hauth, Hiv, #Hfk⟩
  cases hl : rd.live
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hiv with ⟨%Hnull, -⟩
    exact absurd Hnull Hnn
  simp only [↓reduceIte]
  icases Hiv with ⟨Hlive, #Hsnap, #Hintv, #Hwgi, Hwo⟩
  wp_apply hbase γ P (baseOf rt) (DFrac.own sync.rfrac) rd.rtx rv p bk bi fn I E
      $$ [Hrb Hrtxf Hcm Hown Hlive $HI]
    as %err ⟨Hbr, Hres⟩
  · isplitl [Hrb Hrtxf Hcm Hown Hlive]
    · unfold baseRd
      iexists m, Pb, cm, tm
      iframe; iframe #
      ipureintro; exact ⟨Hfacts.1, Hfacts.2.1, HPwf, Or.inr Hok⟩
    isplitr
    · unfold isBucket; iexact Hbk
    iexact Hvis
  unfold baseRd
  icases Hbr with ⟨%m', %Pb', %cm', %tm', Hrb, Hrtxf, Hcm, #Htm', Hown, -, Hlive, -, #Hintv', %Hwf'⟩
  icombine Htm Htm' gives %Heq
  subst Heq
  have Hok' : bksOk Pb' rv.2.bks := by
    rcases Hwf'.2.2.2 with h | h
    · cases h
    · exact h
  iapply HΦ
  iframe
  rw [hl]
  simp only [↓reduceIte]
  iframe; iframe #
  ipureintro; exact ⟨⟨Hok', Hfacts⟩, trivial, Hnn⟩


end proof

end EtcdGrove
end Perennial
