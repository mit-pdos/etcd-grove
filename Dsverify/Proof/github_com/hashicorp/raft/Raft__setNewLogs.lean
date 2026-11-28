/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__setNewLogs.lean (241f27e).
-/
/-
The proof of `Raft__setNewLogs` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setNewLogs
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Dsverify.Spec.github_com.hashicorp.raft.min

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot proto

theorem github_com.hashicorp.raft.Raft.setNewLogs.wp_proof
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_min : github_com.hashicorp.raft.min.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.setNewLogs.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T req rq nextIndex lastIndex prev tid => by
  wp_start as ⟨#Hr, #Hl, #Hlb, Hreq, Htok, %Hprev⟩
  iapply wp_fupd
  wp_auto
  wp_apply wp_config $$ [$Hr] as %c %Hc
  have hmax : 1 ≤ uint.nat c.MaxAppendEntries' ∧ uint.nat c.MaxAppendEntries' ≤ 64 := by
    unfold cfgOk at Hc; exact ⟨Hc.2.2.2.2.2.2.2.2.2.1, Hc.2.2.2.2.2.2.2.2.2.2.1⟩
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) c.MaxAppendEntries' (by word)) as %sl0 ⟨Hsl, Hcap, %Hslcap⟩
  wp_apply wp_min
  ihave #Hinv := (isRaft_proto r γ rc i).trans sep_elim_left $$ Hr
  ihave ⟨%x, #Hlogs, #Hls, -⟩ := isRaft_logStore r γ rc i $$ Hr
  ihave #Hcell := isRaft_durInv r γ rc i $$ Hr
  ihave HI : iprop(∃ (iv : w64) (sl : GoSlice) (ptrs : List Loc) (ents : List Entry),
      "i" ∷ i_ptr ↦ iv ∗ "Hreq" ∷ req ↦ { rq with Entries' := sl } ∗ "Hsl" ∷ sl ↦* ptrs ∗
      "Hcap" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗
      "%Hlen" ∷ ⌜uint.nat iv = uint.nat nextIndex + ents.length ∧ ptrs.length = ents.length⌝ ∗
      "#Hptrs" ∷ ([∗list] j ↦ p ∈ ptrs, ∃ e, ⌜ents[j]? = some e⌝ ∗ logPtr p (prev + 1 + j) e) ∗
      "#Hok" ∷ orStale γ i T (entsOk γ T prev ents)) $$ [i Hreq Hsl Hcap]
  · iexists nextIndex, sl0, [], []
    iframe
    isplitr
    · ipureintro; simp
    isplitr
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
    ileft; unfold entsOk; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  wp_for HI
  wp_if_destruct
  · irename «$r0» => Hlp
    wp_apply (wp_getLog_repl γ rc i T x iv «$r0_ptr» _) $$ [$Htok $Hlp] as %err ⟨Htok, Hres⟩
    · iframe #
    unfold getLogRepl
    icases Hres with (⟨%Herr, #Hce, %lv, Hlv⟩ | ⟨%Herr, %lv, %e, Hlv, #His, %Hk, #Hrd⟩)
    · cases err with
      | nil => exact absurd rfl Herr
      | ok erri =>
      wp_auto
      wp_for_post
      imodintro
      iapply HΦ
      iframe Htok
      iexists sl
      iframe Hreq
      ileft; iframe #; ipureintro; exact Herr
    subst Herr
    wp_auto
    ipersist Hlv
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.PointerType Log.ty))))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType Log.ty) [«$r0_ptr»]
    wp_auto
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hs1, Hs1cap⟩
    wp_auto
    wp_apply (wp_slice_append (V := Loc) (t := go.GoType.PointerType Log.ty) sl ptrs _ [«$r0_ptr»] (DFrac.own 1))
      $$ [Hsl Hcap Hs1] as %sl' ⟨Hsl', Hcap', -⟩
    · iframe
    wp_for_post
    iframe
    iexists (iv + W64 1), sl', ptrs ++ [«$r0_ptr»], ents ++ [e]
    iframe
    have hidx : uint.nat iv = prev + 1 + ents.length := by omega
    isplitr
    · ipureintro
      constructor
      · simp only [List.length_append, List.length_singleton]; word
      · simp only [List.length_append, List.length_singleton]; omega
    isplitr
    · iapply ptrs_snoc ptrs ents prev «$r0_ptr» e Hlen.2
      iframe #
      unfold logPtr
      iexists lv
      iframe #
      rw [← hidx]
      iframe #
    iapply entsOk_snoc γ i T prev ents e
    iframe #
    rw [← hidx]
    iframe #
  imod (ownSlice_persist sl _ ptrs) $$ Hsl with #Hsl
  imodintro
  iapply HΦ
  iframe Htok
  iexists sl
  iframe Hreq
  iright
  isplitr; · ipureintro; rfl
  iexists ents
  iframe #
  unfold entPtrs
  iexists ptrs
  iframe #
  ipureintro; exact Hlen.2

end proof

end Perennial
