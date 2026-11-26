/-
Package `proxy`'s internal definitions: the main loop's state (the replicated log, the state
machine), the proxy's channels' elements.
-/
module

public import Dsverify.Proof.raxos.Proxy.Exec
public import Perennial.Proof.time.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- `time.Now()`: some time, given `time`'s initialization (Perennial's `time.wp_Now`, a theorem
since Perennial 3afd77e35; it needs `isPkgInit pkg_id.time`, which callers get from their
package's initialization). -/
theorem wp_time_Now [time.Assumptions] : time.Now.spec (GF := GF) (hG := hG) :=
  time.wp_Now

theorem bigSepL_bupd_mono {A : Type} (l : List A) :
    ∀ (Φ Ψ : Nat → A → IProp GF), (∀ k x, Φ k x ⊢ |==> Ψ k x) →
      ([∗list] k ↦ x ∈ l, Φ k x) ⊢ |==> [∗list] k ↦ x ∈ l, Ψ k x := by
  induction l with
  | nil =>
    intro Φ Ψ _
    iintro _
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons y ys ih =>
    intro Φ Ψ h
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
    imod (h 0 y) $$ H1 with H1
    imod (ih (fun k x => Φ (k + 1) x) (fun k x => Ψ (k + 1) x) (fun k x => h (k + 1) x)) $$ H2 with H2
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe H1 H2

theorem bigSepL_fupd_mono {A : Type} (E : CoPset) (l : List A) :
    ∀ (Φ Ψ : Nat → A → IProp GF), (∀ k x, Φ k x ⊢ |={E}=> Ψ k x) →
      ([∗list] k ↦ x ∈ l, Φ k x) ⊢ |={E}=> [∗list] k ↦ x ∈ l, Ψ k x := by
  induction l with
  | nil =>
    intro Φ Ψ _
    iintro _
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons y ys ih =>
    intro Φ Ψ h
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
    imod (h 0 y) $$ H1 with H1
    imod (ih (fun k x => Φ (k + 1) x) (fun k x => Ψ (k + 1) x) (fun k x => h (k + 1) x)) $$ H2 with H2
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe H1 H2

/-- `bigSepL_fupd_mono` for the elements of the list only. -/
theorem bigSepL_fupd_mono_mem {A : Type} (E : CoPset) (l : List A) :
    ∀ (Φ Ψ : Nat → A → IProp GF), (∀ k x, x ∈ l → Φ k x ⊢ |={E}=> Ψ k x) →
      ([∗list] k ↦ x ∈ l, Φ k x) ⊢ |={E}=> [∗list] k ↦ x ∈ l, Ψ k x := by
  induction l with
  | nil =>
    intro Φ Ψ _
    iintro _
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons y ys ih =>
    intro Φ Ψ h
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
    imod (h 0 y List.mem_cons_self) $$ H1 with H1
    imod (ih (fun k x => Φ (k + 1) x) (fun k x => Ψ (k + 1) x)
      (fun k x hx => h (k + 1) x (List.mem_cons_of_mem _ hx))) $$ H2 with H2
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe H1 H2

/-- A slice's elements, one points-to each. -/
theorem ownSlice_elems {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice) (dq : DFrac)
    (vs : List V) :
    (s ↦*{dq} vs : IProp GF) ⊢ [∗list] k ↦ v ∈ vs, typedPointsto (sliceIndexRef V (k : Int) s) v dq := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨Hsl, %_⟩)
  · rw [H.2]; iapply BigSepL.bigSepL_nil.2; iempintro
  · icases typedPointsto_split _ _ _ $$ Hsl with Hsl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hsl with ⟨%_, Hsl⟩
    unfold arrayElems
    simp only [sliceIndexRef]
    iexact Hsl

theorem repCBVal_persist (E : CoPset) (o : raxos.proto.client.ClientBatch) (b : Batch) :
    repCBVal (GF := GF) o (DFrac.own 1) b ⊢ |={E}=> repCBVal o .discard b := by
  iintro H
  iunfold repCBVal at H
  icases H with ⟨%ps, %Hp, Hps, Hl⟩
  iunfold repList at Hl
  icases Hl with ⟨%Hlen, Hl⟩
  imod (ownSlice_persist _ _ _) $$ Hps with Hps
  imod (bigSepL_fupd_mono E ps (fun i p => iprop(∃ x, ⌜b.cmds[i]? = some x⌝ ∗ repCSingle (GF := GF) p (DFrac.own 1) x))
    (fun i p => iprop(∃ x, ⌜b.cmds[i]? = some x⌝ ∗ repCSingle (GF := GF) p DFrac.discard x))
    (fun i p => by
      iintro ⟨%x, %Hx, Hr⟩
      iunfold repCSingle at Hr
      icases Hr with ⟨%v, Hv, %Hv'⟩
      imod ptCSingle_persist E _ _ _ $$ Hv with #Hv
      imodintro
      iexists x
      isplitr
      · ipureintro; exact Hx
      iunfold repCSingle
      iexists v
      iframe Hv
      ipureintro; exact Hv')) $$ Hl with Hl
  imodintro
  iunfold repCBVal
  iexists ps
  iframe Hps
  isplitr
  · ipureintro; exact Hp
  iunfold repList
  iframe Hl
  ipureintro; exact Hlen

end defs

end Perennial.raxos
