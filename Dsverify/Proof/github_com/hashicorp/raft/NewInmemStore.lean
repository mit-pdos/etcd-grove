/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/NewInmemStore.lean (241f27e).
-/
/-
The proof of `raft.NewInmemStore`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.NewInmemStore

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.NewInmemStore.wp_proof :
    github_com.hashicorp.raft.NewInmemStore.spec (GF := GF) (hG := hG) := by
  intro hb
  wp_start as #Herr
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc) go.uint64 (go.GoType.PointerType Log.ty))
    as %ml Hml
  wp_apply (wp_map_make1 (K := GoString) (V := GoSlice) go.string (go.GoType.SliceType go.byte))
    as %mk Hmk
  wp_apply (wp_map_make1 (K := GoString) (V := w64) go.string go.uint64) as %mki Hmki
  irename «$r0» => Hs
  generalize «$r0_ptr» = s at *
  iStructNamed Hs
  let c0 : Conc := { L := LogAbs.empty, lo := W64 0, st := ⟨∅, ∅⟩, mlog := ml, mkv := mk, mint := mki, lm := ∅, kvm := ∅ }
  imod ghostVar_alloc c0 with ⟨%γc, Hgc⟩
  imod ghostVar_alloc (LogAbs.empty) with ⟨%γl, Hgl⟩
  imod ghostVar_alloc (⟨∅, ∅⟩ : StableAbs) with ⟨%γk, Hgk⟩
  icases (ghostVar_split_half γl 1 LogAbs.empty).mp $$ Hgl with ⟨Hgl, Hgl'⟩
  icases (ghostVar_split_half γk 1 (⟨∅, ∅⟩ : StableAbs)).mp $$ Hgk with ⟨Hgk, Hgk'⟩
  let γs : InmemNames := ⟨γc, γl, γk⟩
  ihave HP1 : (▷ storeInv γs s 1 : IProp GF) $$ [lowIndex highIndex logs kv kvInt Hml Hmk Hmki Hgc Hgl Hgk]
  · inext
    iapply (storeInv_unfold γs s 1).mpr
    iexists c0
    iframe
    isplit
    · ipureintro
      refine ⟨?_, ?_, ?_⟩
      · intro k; simp [c0, LogAbs.empty]
      · intro k; simp [c0, LogAbs.empty]
      · intro k; simp [c0]
    · unfold concPers
      isplitl
      · imodintro; iintro %k %p %Hp; simp [c0] at Hp
      · imodintro; iintro %k %p %Hp; simp [c0] at Hp
  imod sync.init_RWMutex_qpool (storeInv γs s) (E := ⊤) inmemPoolN (s.[InmemStore, go!"l"])
    (ThreadBoundLe.le _) $$ HP1 l with ⟨%γp, #Hguard, #Hpool⟩
  imodintro
  iapply HΦ
  iexists γs
  unfold isInmemStore inmemPool inmemLogs kvView
  iframe
  iframe #
  iexists γp
  iframe #

end proof

end Perennial
