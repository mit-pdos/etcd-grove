/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/snapstore/New.lean (241f27e).
-/
/-
The proof of `snapstore.New`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.New
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Store__Create
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Store__List
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Store__Open
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Sink__Write
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Sink__Close
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Sink__Cancel
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Sink__ID

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

/-- (SNAP-2) An open sink's bytes are a Go slice's: shorter than `2^63`. -/
theorem sinkSt_len (k : Loc) (bs : List w8) :
    sinkSt (GF := GF) k (some bs) ⊢ ⌜bs.length < 2 ^ 63⌝ ∗ sinkSt k (some bs) := by
  simp only [sinkSt]
  iintro ⟨%dsl, Hd, Hsl, Hcap, Hc, Hsz⟩
  ihave %Hl := ownSlice_len $$ Hsl
  isplitr
  · ipureintro
    obtain ⟨h1, h2⟩ := Hl
    rw [h1]; word
  · iexists dsl; iframe

/-- The sink of `Create` meets `isSink`, with the commit `Cm` the client fixed. -/
theorem sink_isSink
    (wp_Write : github_com.hashicorp.raft.examples.snapstore.Sink.Write.spec (GF := GF) (hG := hG))
    (wp_Close : github_com.hashicorp.raft.examples.snapstore.Sink.Close.spec (GF := GF) (hG := hG))
    (wp_Cancel : github_com.hashicorp.raft.examples.snapstore.Sink.Cancel.spec (GF := GF) (hG := hG))
    (wp_ID : github_com.hashicorp.raft.examples.snapstore.Sink.ID.spec (GF := GF) (hG := hG))
    (k st : Loc) (γ : GName) (eof : GoInterface) (id : GoString) (ver idx term cfgIdx : w64)
    (cfg : Configuration) (Q R : List w8 → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗ sinkCore k st γ eof id ver idx term cfgIdx cfg ⊢
      isSink ⟨go.GoType.PointerType Sink.ty, #k⟩ id
        (sinkOwn k iprop(∀ bs : List w8, ⌜bs.length < 2 ^ 63⌝ -∗ Q bs -∗
          sinkCommit γ (sinkMeta ver idx term cfgIdx cfg id bs) bs (R bs))) Q R := by
  iintro ⟨#Hpkg, #Hcore⟩
  unfold isSink
  simp only [sinkOwn]
  isplitr
  · ipureintro; go_type_set
  isplitr
  · imodintro
    iintro %p %dq %bs %c %Φ ⟨Hst, Hcm⟩ Hp HΦ
    iapply wp_Write k p dq bs c $$ [$Hpkg $Hst $Hp]
    inext; iintro ⟨Hst, Hp⟩
    iapply HΦ $$ [Hst Hcm] Hp
    iframe
  isplitr
  · imodintro
    iintro %bs %Φ ⟨Hst, Hcm⟩ HQ HΦ
    icases sinkSt_len k bs $$ Hst with ⟨%Hlen, Hst⟩
    iapply wp_Close k st γ eof id ver idx term cfgIdx cfg (some bs) (R bs) $$ [$Hpkg $Hcore $Hst Hcm HQ]
    · iapply Hcm $$ %bs %Hlen HQ
    inext; iintro ⟨Hst, HR⟩
    iapply HΦ $$ Hst HR
  isplitr
  · imodintro
    iintro %Φ Hst HΦ
    iapply wp_Close k st γ eof id ver idx term cfgIdx cfg none iprop(True) $$ [$Hpkg $Hcore $Hst]
    inext; iintro ⟨Hst, -⟩
    iapply HΦ $$ Hst
  isplitr
  · imodintro
    iintro %o %Φ Hst HΦ
    ihave Hst' : sinkSt k o $$ [Hst]
    · cases o with
      | none => iexact Hst
      | some bs => icases Hst with ⟨Hst, -⟩; iexact Hst
    iapply wp_Cancel k o $$ [$Hpkg $Hst']
    inext; iintro Hst
    iapply HΦ $$ Hst
  · imodintro
    iintro %Φ HΦ
    iapply wp_ID k st γ eof id ver idx term cfgIdx cfg $$ [$Hpkg $Hcore]
    inext; iintro -
    iexact HΦ

theorem github_com.hashicorp.raft.examples.snapstore.New.wp_proof
    (wp_Create : github_com.hashicorp.raft.examples.snapstore.Store.Create.spec (GF := GF) (hG := hG))
    (wp_List : github_com.hashicorp.raft.examples.snapstore.Store.List.spec (GF := GF) (hG := hG))
    (wp_Open : github_com.hashicorp.raft.examples.snapstore.Store.Open.spec (GF := GF) (hG := hG))
    (wp_Write : github_com.hashicorp.raft.examples.snapstore.Sink.Write.spec (GF := GF) (hG := hG))
    (wp_Close : github_com.hashicorp.raft.examples.snapstore.Sink.Close.spec (GF := GF) (hG := hG))
    (wp_Cancel : github_com.hashicorp.raft.examples.snapstore.Sink.Cancel.spec (GF := GF) (hG := hG))
    (wp_ID : github_com.hashicorp.raft.examples.snapstore.Sink.ID.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.snapstore.New.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)


end proof

end Perennial
