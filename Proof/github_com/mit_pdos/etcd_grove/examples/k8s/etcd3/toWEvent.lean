module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.toWEvent

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input WEvent)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem toWEvent.wp_proof : toWEvent.spec (GF := GF) (hG := hG) := by
  intro v e
  obtain ⟨vt, vo⟩ := v
  wp_start as Hw
  iunfold wevAt at Hw
  by_cases h4 : e.t = 4
  · simp only [h4, ↓reduceIte]
    icases Hw with ⟨%Ht, Hs⟩
    iunfold statusFailureAt at Hs
    icases Hs with ⟨%p, %st, %Hx, #Hp⟩
    obtain ⟨Hx, Hst⟩ := Hx
    subst Ht Hx
    iStructNamed Hp
    wp_auto
    wp_if_destruct
    · iapply HΦ
      iexists ⟨k8s_correctness.evError, .status go!"Failure"⟩
      isplitr
      · ipureintro
        refine ⟨⟨?_, fun h => absurd h4 h, fun _ => rfl⟩, ?_⟩
        · simp [wevOf, h4]
        · simp [wevOf, k8s_correctness.toWEvL, k8s_correctness.evError, k8s_correctness.evAdded,
            k8s_correctness.evModified, k8s_correctness.evDeleted, k8s_correctness.evBookmark, zObj]
          rfl
      unfold k8s_correctness.evRep k8s_correctness.evObjRep
      isplitr
      · ipureintro; rfl
      iexists p, st
      iframe Hp
      ipureintro; exact ⟨rfl, Hst⟩
    · exact absurd Hst Hif
  · simp only [h4, ↓reduceIte]
    icases Hw with ⟨%Ht, Ho⟩
    obtain ⟨ht4, Ht⟩ := Ht
    ihave Ho' : (∃ (p : Loc) (n : w64),
        ⌜vo = interface.mkOk (go.GoType.PointerType objTyD) #p ∧
          rvStr (W64 (e.rv : Int)) = rvStr n⌝ ∗
        p ↦ { e.o.toObj n with Annotated' := e.ann } : IProp GF) $$ [Ho]
    · cases ha : e.ann
      · simp only [Bool.false_eq_true, ↓reduceIte, driverSpec, objAtD]
        icases Ho with ⟨%p, %n, %Hx, Hp⟩
        iexists p, n
        iframe
        ipureintro; exact ⟨Hx.1, by rw [← Hx.2.2]; rfl⟩
      · simp only [ite_true, driverW]
        icases Ho with ⟨%p, %n, %Hx, Hp⟩
        iexists p, n
        iframe
        ipureintro; exact ⟨Hx.1, by rw [← Hx.2.2]; rfl⟩
    icases Ho' with ⟨%p, %n, %Hx, Hp⟩
    obtain ⟨Hx, Hn⟩ := Hx
    have Hn' := rvStr_inj Hn
    subst Ht Hx Hn'
    have hts : e.t = 0 ∨ e.t = 1 ∨ e.t = 2 ∨ e.t = 3 := by omega
    ipersist Hp
    rcases hts with ht | ht | ht | ht <;>
    · simp only [kEvTypeStr, ht]
      wp_auto
      iapply HΦ
      iexists ⟨kEvTypeStr e.t, .obj { e.o.toObj (W64 (e.rv : Int)) with Annotated' := e.ann }⟩
      isplitr
      · ipureintro
        refine ⟨⟨by simp [wevOf, ht], fun _ => ?_, fun h => by omega⟩, ?_⟩
        · simp [wevOf, kToWEv, ht]
        · simp [wevOf, k8s_correctness.toWEvL, kEvTypeStr, ht, k8s_correctness.evError,
            k8s_correctness.evAdded, k8s_correctness.evModified, k8s_correctness.evDeleted,
            k8s_correctness.evBookmark]
      unfold k8s_correctness.evRep k8s_correctness.evObjRep
      isplitr
      · ipureintro; simp [kEvTypeStr, ht]
      iapply k8s_correctness.deepRO_obj $$ Hp

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
