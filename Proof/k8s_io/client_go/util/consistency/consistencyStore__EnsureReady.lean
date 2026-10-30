/-
Proof of `Spec/k8s_io/client_go/util/consistency/consistencyStore__EnsureReady.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.consistency.consistencyStore__EnsureReady
public import Spec.k8s_io.client_go.util.consistency.consistencyStore__getWrittenRecord
public import Spec.k8s_io.client_go.util.consistency.consistencyStore__Clear
public import Spec.k8s_io.client_go.util.consistency.ownerRecord__EnsureReady
public import Proof.k8s_io.client_go.util.consistency.InvLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.consistency

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

/-- What `getWrittenRecord`'s view shift leaves at `EnsureReady`'s read of the map `W`: with no
record, `EnsureReady` took effect (`K true`); else its permission is in the record's slot. -/
def readQ (γ : ConsNames) (T : Owner → Qp → IProp GF) (S : GMap GR LastSyncRVGetter)
    (G : GR → GoString → IProp GF) (o : Owner) (K : Bool → IProp GF) (W : GMap Owner Loc) :
    IProp GF :=
  match W !! o with
  | none => iprop(K true ∗ T o 1)
  | some r => iprop(∃ s V, isRec γ r s ∗ ⌜s.owner = o⌝ ∗ ensTok γ o ⟨r, V, false⟩ ∗
      auEns γ S G o K)

theorem consistencyStore.EnsureReady.wp_proof
    (wp_getWrittenRecord : consistencyStore.getWrittenRecord.spec (GF := GF) (hG := hG))
    (wp_Clear : consistencyStore.Clear.spec (GF := GF) (hG := hG))
    (wp_recEnsureReady : ownerRecord.EnsureReady.spec (GF := GF) (hG := hG)) :
    consistencyStore.EnsureReady.spec (GF := GF) (hG := hG) := by
  intro c γ T S G o
  iintro %Φ ⟨#Hpkg, #Hc, HT, Hrd⟩ HAU
  ihave #Hc' := Hc
  iNamed Hc'
  let K : Bool → IProp GF := fun ok => iprop(∀ err : GoInterface,
    (⌜ok = true ↔ err = interface.nil⌝ ∗ T o 1 ∗ consReader c γ) -∗ Φ #err)
  ihave HAU : auEns γ S G o K $$ [HAU]
  · iunfold auEns; iexact HAU
  wp_method_call
  wp_call_lc Hlc0
  wp_auto_lc 2
  wp_apply (wp_getWrittenRecord c γ T S G o (readQ γ T S G o K))
    $$ [$Hpkg $Hc $Hrd HAU HT Hlc0 Hlc1 Hlc2] as %r0 ⟨Hrd, %W, %Hr0, HQ⟩
  · iintro %W HWg
    unfold readQ
    cases hw : W !! o with
    | none =>
      imod ens_none_commit γ T S G _ K hw $$ [$Hinv $Hlc1 $Hlc2 $HWg $HAU] with ⟨HWg, HK⟩
      imodintro; iframe HWg; dsimp only; iframe
    | some r =>
      imod ens_deposit γ T _ hw $$ [$Hinv $Hexcl $Hlc0 $HWg $HT] with ⟨HWg, %s, %V, #Hrec, %ho, Htok⟩
      imodintro; iframe
      iexists s, V; iframe #; iframe
      ipureintro; exact ho
  unfold readQ at *
  cases hw : W !! o with
  | none =>
    simp only [hw, Option.getD_none] at Hr0
    subst Hr0
    simp only [hw]
    icases HQ with ⟨HK, HT⟩
    wp_auto
    iapply HK
    iframe
    ipureintro; simp
  | some r =>
    simp only [hw, Option.getD_some] at Hr0
    subst Hr0
    simp only [hw]
    icases HQ with ⟨%s, %V, #Hrec, %ho, Htok, HAU⟩
    subst ho
    ihave #Hrec' := Hrec
    iunfold isRec at Hrec'
    icases Hrec' with ⟨-, Hp⟩
    iunfold recPhys at Hp
    icases Hp with ⟨%Hnn, #Huid, -, -⟩
    simp only [decide_eq_false Hnn]
    wp_auto
    wp_bind
    iapply (wp_recEnsureReady c γ T S G r0 s V) $$ [$Hpkg $Hc $Hrec $Htok]
    inext
    imod HAU with ⟨%M, HM, Hcl⟩
    imodintro
    iexists M
    iframe HM
    iintro %ok ⟨HM, Hready⟩
    imod Hcl $$ %ok [$HM $Hready] with HK
    imodintro
    iintro %err ⟨%Herr, Hres⟩
    cases ok with
    | true =>
      have he : err = interface.nil := Herr.1 rfl
      subst he
      simp only [↓reduceIte]
      wp_auto
      wp_bind
      iapply (wp_Clear c γ T S G s.owner s.uid (some (r0, s, V))) $$ [$Hpkg $Hc Hres]
      · dsimp only [clearPre]; iframe; iframe #; ipureintro; exact ⟨rfl, rfl⟩
      inext
      iapply fupd_mask_intro
      · simp
      iintro Hclose
      iexists ∅
      dsimp only [clearState]
      isplitr
      · itrivial
      iintro -
      imod Hclose
      imodintro
      dsimp only [clearPost]
      iintro HT
      wp_auto
      iapply HK
      iframe
      ipureintro; simp
    | false =>
      cases err with
      | nil => exact absurd (Herr.2 rfl) (by simp)
      | ok i =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        wp_auto
        iapply HK
        iframe
        ipureintro; simp

end proof

end consistency
end EtcdGrove
end Perennial
