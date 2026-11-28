/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/snapstore/Store__Open.lean (241f27e).
-/
/-
The proof of `snapstore.Store.Open`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Store__Open
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.NewReader

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.snapstore

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.snapstore.Store.Open.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_NewReader : github_com.hashicorp.raft.examples.snapstore.NewReader.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.snapstore.Store.Open.spec (GF := GF) (hG := hG) :=
  fun st γ eof id Φ => by
  iintro ⟨#Hpkg, #Hstore, HAU⟩
  iNamed Hstore
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply (lc := 1) wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iNamed HR
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod HAU $$ Hnc with ⟨Hnc, HAU⟩
  imod lc_fupd_elim_later (E := ∅) $$ Hlc1 HAU with ⟨%old, Hown, Hclose⟩
  unfold ownLatest
  ihave %Heq := ghostVar_agree _ _ _ _ _ $$ Hown Hg
  subst Heq
  imod Hclose $$ Hown with HΦ
  imodintro
  iframe Hnc
  ihave ⟨%e, #He, %Hene⟩ := errNoSnapshot_ok $$ Hpkg
  wp_auto
  cases old with
  | none =>
    simp only [latestCell]
    icases Hcell with %Hhas
    subst Hhas
    wp_auto
    wp_apply wp_Unlock $$ [$Hmu $Hlocked Hg Hhas Hmt Hdat Hnid]
    · inext; unfold storeLocked ownLatest; iexists none, false, mt, dsl, nid; iframe
      simp only [latestCell]; ipureintro; trivial
    iapply HΦ
    simp only [openPost]
    iexists e
    ipureintro; exact ⟨rfl, Hene⟩
  | some p =>
    obtain ⟨m, b⟩ := p
    simp only [latestCell]
    icases Hcell with ⟨⟨%Hhas, %Hmt⟩, #Hb⟩
    subst Hhas Hmt
    wp_auto
    wp_if_destruct
    · wp_apply wp_NewReader dsl DFrac.discard b eof $$ [$Heof $Hb] as %rd ⟨-, %R, #Hrc, HR, %Hwt⟩
      wp_apply wp_Unlock $$ [$Hmu $Hlocked Hg Hhas Hmt Hdat Hnid]
      · inext; unfold storeLocked ownLatest; iexists some (mt, b), true, mt, dsl, nid; iframe
        simp only [latestCell]; isplitr; · ipureintro; simp
        iexact Hb
      iapply HΦ
      simp only [openPost, if_pos]
      iexists m_ptr, ⟨go.GoType.PointerType snapstore.Reader.ty, #rd⟩, R
      iframe
      iframe #
      ipureintro; exact ⟨rfl, Hwt⟩
    · wp_apply wp_Unlock $$ [$Hmu $Hlocked Hg Hhas Hmt Hdat Hnid]
      · inext; unfold storeLocked ownLatest; iexists some (mt, b), true, mt, dsl, nid; iframe
        simp only [latestCell]; isplitr; · ipureintro; simp
        iexact Hb
      iapply HΦ
      simp only [openPost, if_neg Hif]
      iexists e
      ipureintro; exact ⟨rfl, Hene⟩

end proof

end Perennial
