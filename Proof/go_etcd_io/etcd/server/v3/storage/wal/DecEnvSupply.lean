/- Lean-first (no Rocq counterpart).

**`WalDecEnvSupply` proved** (2026-11-22): the decoder's environment from the WAL package's initialization, with
`IoE` the `*PathError`s. `io.EOF`, `io.ErrUnexpectedEOF` and `walpb.ErrCRCMismatch` are three `errors.New` errors
(`errors.newVar`, the `walpb` fact's cell), different by their messages (`errors.errorString_ne`);
`errors.Is(_, io.EOF)` on `nil`, `io.EOF` and `io.ErrUnexpectedEOF` answers `==` (`errors.wp_Is_ptr` on `nil`,
`errors.wp_Is_leaf` on a leaf); `ErrCRCMismatch` is a leaf `*errorString` (`errTreeNot_errorString`,
`errTreeTerm_errorString`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.openAtIndexLemmas
public import Proof.errors.ErrTree
public import Perennial.Proof.errors.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

section pure
variable [GooseExts] [GoGlobalContext]

/-- An `*errorString` at `x` as an `error`. -/
private abbrev es (x : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x

private theorem es_ne_pathError (x pe : Loc) :
    es x ≠ interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe := by
  unfold es interface.mkOk
  intro h
  injection h with h
  injection h with h
  injection h with h
  rw [io.fs.PathError.ty.eq_1, _root_.Perennial.errors.errorString.ty.eq_1] at h
  injection h with h
  revert h; decide

private theorem es_ne {x y : Loc} (h : x ≠ y) : es x ≠ es y := by
  unfold es interface.mkOk
  intro he
  injection he with he
  injection he with _ he
  exact h (GoGlobalContext.intoVal_inj_loc he)

end pure

section eof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [_root_.Perennial.errors.Assumptions]

/-- `errors.Is(e, io.EOF)` on a leaf `*errorString` or `nil`: `e == io.EOF`. -/
private theorem wp_Is_eof (xE : Loc) (e : GoInterface) (he : e = GoInterface.nil ∨ ∃ y : Loc, e = es y) :
    isPkgInit (PROP := IProp GF) pkg_id.errors ⊢
    {{ (True : IProp GF) }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #e)) (Val #(es xE)))
    {{ (b : Bool), RET #b; ⌜b = decide (e = es xE)⌝ }} := by
  iintro #Herr !> %Φ - HΦ
  obtain ⟨hp, -, -⟩ := EtcdGrove.errorString_leaf xE
  rcases he with rfl | ⟨y, rfl⟩
  · wp_apply +noauto (_root_.Perennial.errors.wp_Is_ptr (· = GoInterface.nil) (fun _ _ => True) (fun _ _ => True)
      GoInterface.nil (es xE) (fun tii h => by cases h; exact hp)
      (fun ii _ h _ _ => by cases h)) $$ [$Herr] as %b ⟨%Hnil, -⟩
    · isplitl
      · iintro !> %ii %h; cases h
      · ipureintro; rfl
    iapply HΦ
    ipureintro; exact Hnil (Or.inl rfl)
  · obtain ⟨hpy, hleaf, hIs⟩ := EtcdGrove.errorString_leaf y
    wp_apply +noauto (_root_.Perennial.errors.wp_Is_leaf _ (es xE) hleaf hIs (fun tii h => by cases h; exact hp)
      (_root_.Perennial.errors.treeTyped_pointer _ _ hpy)) $$ [$Herr]
    iapply HΦ
    ipureintro; rfl

end eof

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions] [_root_.Perennial.errors.Assumptions]

/-- **`WalDecEnvSupply` holds** (see the file header). -/
theorem wal_decEnvSupply : WalDecEnvSupply (GF := GF) := by
  iintro #Hpkg
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Herr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Hpbi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal.walpb $$ []
  · iPkgInit
  ihave #Hw : (wal.walInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave #Hcrc := wal.walInit_crcTable $$ Hw
  ihave #Hi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, #HE, #HU, -⟩
  iunfold _root_.Perennial.errors.newVar at HE HU
  icases HE with ⟨%xE, #GE, #SE, -⟩
  icases HU with ⟨%xU, #GU, #SU, -⟩
  ihave #Hpb : (walpb.walpbInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpbi
  icases Hpb with ⟨%eC, #GC, #OkC, -, %xC, %hxC, #SC⟩
  ihave %hEU := _root_.Perennial.errors.errorString_ne xE xU _ _ (by decide) $$ SE SU
  ihave %hCE := _root_.Perennial.errors.errorString_ne xC xE _ _ (by decide) $$ SC SE
  subst hxC
  iexists (fun x => ∃ pe : Loc, x = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe), es xE, es xU
  isplitl
  · iunfold decEnv
    iPkgInit
    iframe GE GU Hcrc
    isplitl
    · iunfold isEofOk
      isplitl
      · ipureintro
        refine ⟨es_ne hEU, fun ⟨pe, h⟩ => es_ne_pathError _ _ h, fun ⟨pe, h⟩ => es_ne_pathError _ _ h⟩
      iintro !> %e %he
      iapply (wp_Is_eof xE e ?_) $$ Herr
      rcases he with h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨xE, h⟩
      · exact Or.inr ⟨xU, h⟩
    isplitl
    · iexists _
      iframe GC OkC
      isplitl
      · iapply (errTreeNot_errorString xC (es xE) (es_ne hCE))
      · iapply (errTreeTerm_errorString xC)
    · iPkgInit
  · ipureintro
    exact ⟨fun pe => ⟨pe, rfl⟩, fun ⟨pe, h⟩ => by cases h⟩

end proof

end EtcdGrove
end Perennial
