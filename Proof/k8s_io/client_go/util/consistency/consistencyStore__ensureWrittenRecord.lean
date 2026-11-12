/-
Proof of `Spec/k8s_io/client_go/util/consistency/consistencyStore__ensureWrittenRecord.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.consistency.consistencyStore__ensureWrittenRecord
public import Spec.k8s_io.client_go.util.consistency.consistencyStore__getWrittenRecord
public import Spec.k8s_io.client_go.util.consistency.newOwnerRecord
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

/-- What `getWrittenRecord`'s view shift leaves, at the fast path's read of the map `W`: if the
owner's record `r` is for `uid`, `WroteAt` took effect (the atomic update's continuation `K` and
the pending write's receipt); else the update and the permission are untouched. -/
def fastQ (γ : ConsNames) (o : Owner) (uid : GoString) (gr : GR) (rv : GoString) (q : Qp)
    (T : Owner → Qp → IProp GF) (K : IProp GF) (W : GMap Owner Loc) : IProp GF :=
  match W !! o with
  | none => iprop(auWrote γ o uid gr rv K ∗ T o q)
  | some r => iprop(∃ s, isRec γ r s ∗ ⌜s.owner = o⌝ ∗
      (if s.uid = uid then iprop(K ∗ ∃ id, pendTok γ id ⟨r, gr, rv, q⟩)
       else iprop(auWrote γ o uid gr rv K ∗ T o q)))

theorem consistencyStore.ensureWrittenRecord.wp_proof
    (wp_getWrittenRecord : consistencyStore.getWrittenRecord.spec (GF := GF) (hG := hG))
    (wp_newOwnerRecord : newOwnerRecord.spec (GF := GF) (hG := hG)) :
    consistencyStore.ensureWrittenRecord.spec (GF := GF) (hG := hG) := by
  intro c γ T S G o uid gr rv q
  iintro %Φ ⟨#Hpkg, #Hc, HT, Hrd⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  ihave #Hc' := Hc
  iNamed Hc'
  let K : IProp GF := iprop(∀ r, (consReader c γ ∗ ∃ s id, isRec γ r s ∗ ⌜s.owner = o⌝ ∗
    pendTok γ id ⟨r, gr, rv, q⟩) -∗ Φ #r)
  ihave HAU : auWrote γ o uid gr rv K $$ [HAU]
  · iunfold auWrote; inext; iexact HAU
  wp_auto
  wp_apply (lc := 3) wp_with_defer as %defer defer
  wp_apply (wp_getWrittenRecord c γ T S G o (fastQ γ o uid gr rv q T K))
    $$ [$Hpkg $Hc $Hrd HAU HT Hlc1 Hlc2 Hlc3] as %r0 ⟨Hrd, %W, %Hr0, HQ⟩
  · iintro %W HWg
    unfold fastQ
    cases hw : W !! o with
    | none => imodintro; iframe HWg; dsimp only; iframe
    | some r =>
      imod lookup_rec γ T _ hw $$ [$Hinv $Hlc1 $HWg] with ⟨HWg, %s, #Hrec, %ho⟩
      by_cases hu : s.uid = uid
      · imod wrote_found_commit γ T gr rv q _ K hw hu ho $$ [$Hinv $Hexcl $Hlc2 $Hlc3 $HWg $Hrec $HT $HAU]
          with ⟨HWg, HK, Htok⟩
        imodintro
        iframe HWg
        iexists s
        iframe #
        simp only [hu, ↓reduceIte]
        isplitr
        · ipureintro; exact ho
        · iframe
      · imodintro
        iframe HWg
        iexists s
        iframe #
        simp only [hu, ↓reduceIte]
        isplitr
        · ipureintro; exact ho
        · iframe
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ auWrote γ o uid gr rv K ∗ T o q ∗
      consReader c γ ∗ ownerUID_ptr ↦ uid ∗ «$res0_ptr» ↦ zero_val Loc) ∨
      (∃ r : Loc, ⌜v = returnVal #()⌝ ∗ «$res0_ptr» ↦ r ∗ Φ #r))) at next
    with [HQ Hrd record ownerUID «$res0»]
  · unfold fastQ
    cases hw : W !! o with
    | none =>
      simp only [hw, Option.getD_none] at Hr0
      subst Hr0
      wp_auto
      dsimp only
      icases HQ with ⟨HAU, HT⟩
      ileft; iframe; ipureintro; rfl
    | some r =>
      simp only [hw, Option.getD_some] at Hr0
      subst Hr0
      icases HQ with ⟨%s, #Hrec, %ho, HQ⟩
      ihave #Hrec' := Hrec
      iunfold isRec at Hrec'
      icases Hrec' with ⟨-, Hp⟩
      iunfold recPhys at Hp
      icases Hp with ⟨%Hnn, #Huid, -, -⟩
      simp only [decide_eq_false Hnn, Bool.not_false]
      wp_auto
      by_cases hu : s.uid = uid
      · simp only [hu, ↓reduceIte]
        icases HQ with ⟨HK, %id, Htok⟩
        wp_auto
        iright
        iexists r0
        isplitr
        · ipureintro; rfl
        iframe «$res0»
        iapply HK
        iframe
        iframe #
        ipureintro; exact ho
      · simp only [hu, ↓reduceIte]
        icases HQ with ⟨HAU, HT⟩
        wp_auto
        ileft; iframe; ipureintro; rfl
  iintro (⟨%Hv, HAU, HT, Hrd, ownerUID, «$res0»⟩ | ⟨%r, %Hv, «$res0», HΦ⟩)
  · subst Hv
    wp_auto
    wp_apply (lc := 3) sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
    iunfold writesP at HP
    icases HP with ⟨%W1, Hm, Hg⟩
    wp_apply wp_map_lookup1 $$ [$Hm] as Hm
    ihave HAU : auWrote γ o uid gr rv K $$ [HAU]
    · iunfold auWrote; inext; iexact HAU
    wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ auWrote γ o uid gr rv K ∗ T o q ∗
        consReader c γ ∗ £ 1 ∗ £ 1 ∗ γ.wm ↦$ W1 ∗ ghostVar γ.W (1 : Qp).half W1 ∗
        ownerUID_ptr ↦ uid ∗ «$res0_ptr» ↦ zero_val Loc ∗
        □ (∀ r1, ⌜W1 !! o = some r1⌝ -∗ ∃ s1, isRec γ r1 s1 ∗ ⌜s1.uid ≠ uid⌝)) ∨
        (∃ r : Loc, ⌜v = returnVal #()⌝ ∗ «$res0_ptr» ↦ r ∗ Φ #r ∗ γ.wm ↦$ W1 ∗
          ghostVar γ.W (1 : Qp).half W1)))
      at next with [HAU HT Hrd Hlc1 Hlc2 Hlc3 Hm Hg record ownerUID «$res0»]
    · cases hw1 : W1 !! o with
      | none =>
        simp only [Option.getD_none]
        wp_auto
        ileft; iframe
        isplitr
        · ipureintro; rfl
        iintro !> %r1 %h; cases h
      | some r1 =>
        simp only [Option.getD_some]
        imod lookup_rec γ T _ hw1 $$ [$Hinv $Hlc1 $Hg] with ⟨Hg, %s1, #Hrec, %ho⟩
        ihave #Hrec' := Hrec
        iunfold isRec at Hrec'
        icases Hrec' with ⟨-, Hp⟩
        iunfold recPhys at Hp
        icases Hp with ⟨%Hnn, #Huid, -, -⟩
        simp only [decide_eq_false Hnn, Bool.not_false]
        wp_auto
        by_cases hu : s1.uid = uid
        · simp only [hu]
          imod wrote_found_commit γ T gr rv q _ K hw1 hu ho
            $$ [$Hinv $Hexcl $Hlc2 $Hlc3 $Hg $Hrec $HT $HAU] with ⟨Hg, HK, %id, Htok⟩
          wp_auto
          iright
          iexists r1
          isplitr
          · ipureintro; rfl
          iframe Hm Hg «$res0»
          iapply HK
          iframe
          iframe #
          ipureintro; exact ho
        · simp only [hu]
          wp_auto
          ileft; iframe
          isplitr
          · ipureintro; rfl
          iintro !> %r2 %h
          cases h
          iexists s1; iframe #; ipureintro; exact hu
    iintro (⟨%Hv, HAU, HT, Hrd, Hlc2, Hlc3, Hm, Hg, ownerUID, «$res0», #Hold⟩ |
      ⟨%r, %Hv, «$res0», HΦ, Hm, Hg⟩)
    · subst Hv
      wp_auto
      wp_apply wp_newOwnerRecord as %r' ⟨%vm, %Hnn', Huid', Hlk', Hvf', Hvm'⟩
      imod ghostVar_alloc (∅ : Vs) with ⟨%γv, Hγv⟩
      ihave ⟨Hγv1, Hγv2⟩ := (ghostVar_split_half γv 1 (∅ : Vs)).1 $$ Hγv
      imod sync.init_Mutex (recLockInv ⟨o, uid, vm, γv⟩) ⊤ _ $$ Hlk' [Hvm' Hγv1] with #Hmu'
      · inext; iunfold recLockInv; iexists ∅; iframe
      ipersist Hvf'
      wp_apply wp_mapInsert $$ [$Hm] as Hm
      imod wrote_new_commit γ T r' vm γv gr rv q K Hnn'
        $$ [$Hinv $Hexcl $Hlc2 $Hlc3 $Hg $Hold $Huid' $Hvf' $Hmu' $Hγv2 $HT $HAU]
        with ⟨Hg, HK, #Hrec', %id, Htok⟩
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hm Hg]
      · iunfold writesP; iexists _; iframe
      iapply HK
      iframe
      iframe #
      ipureintro; rfl
    · subst Hv
      wp_auto
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hm Hg]
      · iunfold writesP; iexists W1; iframe
      iexact HΦ
  · subst Hv
    wp_auto
    iexact HΦ

end proof

end consistency
end EtcdGrove
end Perennial
