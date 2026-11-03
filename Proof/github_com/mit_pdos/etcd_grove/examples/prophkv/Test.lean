/- Lean-first (no Rocq counterpart).

The proof of `Test`: after the first `Put`, an invariant holds the client's half of the abstract
state, in which `"k"` is `"a"` or `"b"`; the goroutine's `Put` and `GetAny`'s atomic update
(`au_of_inv`) both go through it.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.prophkv.Test
public import Spec.github_com.mit_pdos.etcd_grove.examples.prophkv.NewKV
public import Spec.github_com.mit_pdos.etcd_grove.examples.prophkv.KV__Put
public import Spec.github_com.mit_pdos.etcd_grove.examples.prophkv.GetAny

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prophkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.prophkv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.prophkv.Assumptions]

/-- `Test`'s invariant: the client's half of the abstract state, in which `"k"` is `"a"` or
`"b"`. -/
abbrev testInv (γ : GName) : IProp GF :=
  iprop(∃ m : GMap GoString GoString, kvState γ m ∗ ⌜∃ v, m !! go!"k" = some v ∧ goodVal v⌝)

def testN : Namespace := nroot.@"prophkv"

/-- The atomic update `GetAny` takes, from the invariant: a read of `"k"` answers a good value. -/
theorem au_of_inv (γ : GName) :
    inv testN (testInv (GF := GF) γ) ⊢
      AU <{ ∃∃ (m : GMap GoString GoString), kvState γ m }> @ ⊤, ∅
        <{ kvState γ m, COMM ⌜goodVal ((m !! go!"k").getD go!"")⌝ }> := by
  refine (and_intro .rfl true_intro).trans (aupd_intro ?_)
  iintro ⟨#Hinv, -⟩
  unfold atomic_acc
  iinv Hinv with ⟨%m, >Hst, >%Hgood⟩ Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists ⟨m, ⟨⟩⟩
  simp only [Tele.app]
  iframe Hst
  isplit
  · iintro Hst
    imod Hmask with -
    imod Hclose $$ [Hst] with -
    · inext; iexists m; iframe Hst; ipureintro; exact Hgood
    imodintro; itrivial
  · iintro %y Hst
    imod Hmask with -
    imod Hclose $$ [Hst] with -
    · inext; iexists m; iframe Hst; ipureintro; exact Hgood
    imodintro
    ipureintro
    obtain ⟨v, hv, hg⟩ := Hgood
    simp [hv, hg]

theorem Test.wp_proof (wp_NewKV : NewKV.spec (GF := GF)) (wp_Put : KV__Put.spec (GF := GF))
    (wp_GetAny : GetAny.spec (GF := GF)) : Test.spec (GF := GF) := by
  wp_start as #Hpkg
  wp_auto
  wp_apply wp_NewKV as %kv %γ ⟨#Hkv, Hst⟩
  -- `Put("k", "a")`, on the client's own half of the abstract state
  wp_apply (wp_Put kv γ go!"k" go!"a" (kvState γ (<[go!"k" := go!"a"]> ∅))) $$ [$Hkv Hst]
    as Hst
  · iintro %m Hlk
    iunfold kvState at Hlk Hst
    icombine Hlk Hst gives %Hagree
    obtain ⟨_, rfl⟩ := Hagree
    imod ghostVar_update_halves (<[go!"k" := go!"a"]> ∅) γ ∅ ∅ $$ Hlk Hst with ⟨Hlk, Hst⟩
    imodintro
    unfold kvState
    iframe
  -- the invariant: `"k"` is `"a"` or `"b"`
  imod inv_alloc testN ⊤ (testInv γ) $$ [Hst] with #Hinv
  · inext; iexists _; iframe Hst; ipureintro; exact ⟨go!"a", by simp, Or.inl rfl⟩
  -- the goroutine: `Put("k", "b")`, through the invariant
  ipersist kv
  wp_apply wp_fork $$ []
  · wp_auto
    wp_apply (wp_Put kv γ go!"k" go!"b" iprop(True)) $$ [$Hkv]
    · iintro %m Hlk
      iinv Hinv with ⟨%m', >Hst, >%Hgood⟩ Hclose
      iunfold kvState at Hlk Hst
      icombine Hlk Hst gives %Hagree
      obtain ⟨_, rfl⟩ := Hagree
      imod ghostVar_update_halves (<[go!"k" := go!"b"]> m) γ m m $$ Hlk Hst with ⟨Hlk, Hst⟩
      imod Hclose $$ [Hst] with -
      · inext; iexists _; unfold kvState; iframe Hst
        ipureintro; exact ⟨go!"b", by simp, Or.inr rfl⟩
      imodintro
      unfold kvState
      iframe
    itrivial
  -- `GetAny`, with the update from the invariant
  ihave HAU := au_of_inv γ $$ Hinv
  wp_apply (wp_GetAny kv γ go!"k" (fun x => iprop(⌜goodVal x⌝))) $$ [$Hkv $HAU] as %r Hr
  iapply HΦ $$ Hr

end proof

end prophkv
end EtcdGrove
end Perennial
