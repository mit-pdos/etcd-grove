/-
The specs and proofs of the lab's `encoding/json` model's codec registry and its calls of the
codec (`json.go`): `SetCodec(c)` registers `c` (the first registration stays; `codecSet` after
it), `getCodec()` returns the registered codec; `Marshal` is the kit's `jsonMarshal`;
`Valid(data)` is `jsonValid F`; `Unmarshal(data, ptr)` is a syntax error unless
`jsonValid F`, else the kit's `jsonUnmarshal`. `RawMessage`'s `MarshalJSON` and `UnmarshalJSON`.
-/
module

public import Harness.Proof.encoding.json.Defs
public import Perennial.Proof.sync.Mutex__Lock
public import Perennial.Proof.sync.Mutex__Unlock

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

section spec
variable [JsonKit]
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [encoding.json.Assumptions] [JsonCodec GF]

/-- The packages `encoding/json` imports are initialized. -/
theorem deps_of_pkg :
    isPkgInit (PROP := IProp GF) pkg_id.encoding.json ⊢
      isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPkgInit (PROP := IProp GF) pkg_id.io := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.encoding.json).trans ?_
  show iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ True) ⊢ _
  iintro ⟨H1, H2, -⟩
  iframe

/-- `SetCodec(c)`: with `c` a non-nil codec holding the kit's functions, a codec with them is
registered for good. -/
abbrev SetCodec.spec : Prop :=
  ∀ c : Loc,
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ codecFns c ∗ ⌜c ≠ null⌝ }}
    (App (Val (@! encoding.json.SetCodec)) (Val #c))
  {{ RET #(); codecSet (GF := GF) }}

/-- `getCodec()`: with a codec registered, it returns it. -/
abbrev getCodec.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ codecSet (GF := GF) }}
    (App (Val (@! encoding.json.getCodec)) (Val #()))
  {{ (c : Loc), RET #c; codecFns c }}

set_option goose.wp.extras true

theorem SetCodec.wp_proof : SetCodec.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as ⟨#Hfns, %Hc⟩
  ihave ⟨#Hsync, -⟩ := deps_of_pkg $$ Hpkg
  ihave #Hi := isInit_access $$ Hpkg
  iNamed Hi
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $HcodecMu] as ⟨Hlocked, Hinv⟩
  ihave Hinv : (globalAddr codec ↦ (null : Loc) ∨
    ∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr codec ↦□ c ∗ codecFns c : IProp GF) $$ [Hinv]
  · unfold codecInv; iexact Hinv
  icases Hinv with (Hnull | ⟨%c', %Hc', #Hcp, #Hfns'⟩)
  · wp_auto
    ipersist Hnull
    wp_apply sync.Mutex.Unlock.wp_proof (globalAddr codecMu) codecInv $$ [$Hsync $HcodecMu $Hlocked]
    · unfold codecInv; iright; iexists c; iframe Hnull Hfns; ipureintro; exact Hc
    iapply HΦ
    unfold codecSet
    iexists c; iframe Hnull Hfns; ipureintro; exact Hc
  · wp_auto
    rw [decide_eq_false Hc']
    wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof (globalAddr codecMu) codecInv $$ [$Hsync $HcodecMu $Hlocked]
    · unfold codecInv; iright; iexists c'; iframe Hcp Hfns'; ipureintro; exact Hc'
    iapply HΦ
    unfold codecSet
    iexists c'; iframe Hcp Hfns'; ipureintro; exact Hc'

theorem getCodec.wp_proof : getCodec.spec (GF := GF) (hG := hG) := by
  wp_start as #Hset
  unfold codecSet
  icases Hset with ⟨%c, %Hc, #Hcp, #Hfns⟩
  ihave ⟨#Hsync, -⟩ := deps_of_pkg $$ Hpkg
  ihave #Hi := isInit_access $$ Hpkg
  iNamed Hi
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $HcodecMu] as ⟨Hlocked, Hinv⟩
  ihave Hinv : (globalAddr codec ↦ (null : Loc) ∨
    ∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr codec ↦□ c ∗ codecFns c : IProp GF) $$ [Hinv]
  · unfold codecInv; iexact Hinv
  icases Hinv with (Hnull | ⟨%c', %Hc', #Hcp', -⟩)
  · icombine Hnull Hcp gives %Heq
    exact absurd Heq.symm Hc
  icombine Hcp' Hcp gives %Heq
  subst Heq
  wp_apply sync.Mutex.Unlock.wp_proof (globalAddr codecMu) codecInv $$ [$Hsync $HcodecMu $Hlocked]
  · unfold codecInv; iright; iexists c'; iframe Hcp' Hfns; ipureintro; exact Hc
  rw [decide_eq_false Hc]
  wp_auto
  iapply HΦ
  iexact Hfns

/-- `Marshal(v)`: the kit's `jsonMarshal` (`JsonCodec.enc`). -/
abbrev Marshal.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (v : GoInterface) (Ψ : Option (List w8) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ codecSet (GF := GF) ∗
      kitCodecOk F ∗ JsonCodec.enc v Ψ }}
    (App (Val (@! encoding.json.Marshal)) (Val #v))
  {{ (s : GoSlice) (err : GoInterface), RET (PairV #s #err);
      (⌜err = interface.nil⌝ ∗ ∃ bs, s ↦* bs ∗ ownSliceCap w8 s (DFrac.own 1) ∗ Ψ (some bs)) ∨
      (⌜err ≠ interface.nil⌝ ∗ Ψ none) }}

theorem Marshal.wp_proof : Marshal.spec (GF := GF) (hG := hG) := by
  intro F v Ψ
  wp_start as ⟨#Hset, #Hok, Henc⟩
  wp_auto
  wp_apply getCodec.wp_proof $$ [$Hset] as %c #Hfns
  unfold codecFns
  icases Hfns with ⟨#Hm, #Hu, #Hs⟩
  wp_auto
  unfold kitCodecOk marshalOk
  icases Hok with ⟨#Hmok, -, -⟩
  wp_apply Hmok $$ Henc
  isplit
  · iintro %s %bs Hs Hcap HΨ
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists bs
    iframe
  · iintro %s %err %Herr HΨ
    wp_auto
    iapply HΦ
    iright
    iframe
    ipureintro; exact Herr

end spec

end encoding.json

end Perennial
