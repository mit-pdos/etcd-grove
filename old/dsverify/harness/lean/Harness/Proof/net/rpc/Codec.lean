/-
The specs and proofs of the codec registry of the lab's `net/rpc` model (`codec.go`):
`SetCodec(c)` registers `c` (the first registration stays; `codecSet` after it), `getCodec()`
returns the registered codec (with `codecSet`, the kit's).
-/
module

public import Harness.Proof.net.rpc.Defs
public import Perennial.Proof.sync.Mutex__Lock
public import Perennial.Proof.sync.Mutex__Unlock

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions] [RpcKit] [RpcCodec GF]

/-- The packages `net/rpc` imports are initialized. -/
theorem deps_of_pkg :
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ⊢
      isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
      isPkgInit (PROP := IProp GF) pkg_id.net ∗ isPkgInit (PROP := IProp GF) pkg_id.errors := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.net.rpc).trans ?_
  show iprop(isPkgInit (PROP := IProp GF) pkg_id.errors ∗
    isPkgInit (PROP := IProp GF) pkg_id.net ∗ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ True) ⊢ _
  iintro ⟨H4, H3, H2, H1, -⟩
  iframe

/-- `SetCodec(c)`: with `c` a non-nil codec holding the kit's functions, a codec with them is
registered for good. -/
abbrev SetCodec.spec : Prop :=
  ∀ c : Loc,
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecFns c ∗ ⌜c ≠ null⌝ }}
    (App (Val (@! net.rpc.SetCodec)) (Val #c))
  {{ RET #(); codecSet (GF := GF) }}

/-- `getCodec()`: with a codec registered, it returns it. -/
abbrev getCodec.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) }}
    (App (Val (@! net.rpc.getCodec)) (Val #()))
  {{ (c : Loc), RET #c; codecFns c }}

set_option goose.wp.extras true

theorem SetCodec.wp_proof : SetCodec.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as ⟨#Hfns, %Hc⟩
  ihave ⟨-, #Hsync, -, -⟩ := deps_of_pkg $$ Hpkg
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
  ihave ⟨-, #Hsync, -, -⟩ := deps_of_pkg $$ Hpkg
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

end spec

end net.rpc

end Perennial
