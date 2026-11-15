/-
`o.Do(f)` on a freshly owned, zero `sync.Once` (U11d; for `loadFreelist`'s `db.freelistLoad.Do`,
`notes/bbolt-proof-plan.md`): Perennial's `isOnce` and its `Once.Do` spec are stated for
`HasLC.hasLC` only, and bbolt's predicates are over any `hlc`; `Open` owns the zero `Once` when it
calls `loadFreelist` and nothing later calls `Do` on it (`Tx.Check`'s `loadFreelist` is
unreachable with `StrictMode = false`), so `Do` is stepped directly: `done` is false, `doSlow`
locks the (fresh) mutex, sees `done` false, runs `f`, stores `done`, unlocks. A local stand-in for
an `hlc`-generic `Once` spec (a Perennial proposal, `notes/perennial-changes.md`).
-/
module

public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode

section once
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- **`o.Do(f)` on an owned zero `Once`**: `f` runs once, from `P` to `Q`; `o` is lost (no later
`Do` is covered). -/
theorem Once.wp_Do_own (o : Loc) (P Q : IProp GF) (f : GoFunc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ typedPointsto (GF := GF) o (zero_val sync.Once)
        (DFrac.own 1) ∗ P ∗ iprop({{ P }} (App (Val #f) (Val #())) {{ RET #(); Q }}) }}
      (App (Val (o @!! go.GoType.PointerType sync.Once.ty @!! go!"Do")) (Val #f))
    {{ RET #(); Q }} := by
  iintro %Φ ⟨#Hsync, Ho, HP, Hf⟩ HΦ
  iStructNamed Ho
  have hz : (zero_val sync.atomic.Bool') =
      ({ «_#0'» := zero_val _, v' := sync.atomic.b32w false } : sync.atomic.Bool') := rfl
  ihave Hd : sync.atomic.ownBool (GF := GF) (structFieldRef sync.Once go!"done" o) (DFrac.own 1) false $$ [done]
  · simp only [sync.atomic.ownBool_unseal, sync.atomic.ownBoolDef]
    rw [← hz]; iexact done
  imod sync.init_Mutex iprop(True) ⊤ (structFieldRef sync.Once go!"m" o) $$ m [] with #Hm
  · inext; itrivial
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_method_call
  wp_auto
  wp_apply_core sync.atomic.Bool.wp_Load _ (DFrac.own 1) $$ [] [-]
  · iexact Hat
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists false
  iframe Hd
  iintro Hd
  imod Hmask with _
  imodintro
  wp_auto
  wp_method_call
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hsync $Hm] as ⟨Hlk, -⟩
  try wp_auto
  wp_apply_core sync.atomic.Bool.wp_Load _ (DFrac.own 1) $$ [] [-]
  · iexact Hat
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists false
  iframe Hd
  iintro Hd
  imod Hmask with _
  imodintro
  wp_auto
  try simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  try wp_auto
  wp_apply Hf $$ HP as HQ
  try wp_auto
  wp_apply_core sync.atomic.Bool.wp_Store _ _ $$ [] [-]
  · iexact Hat
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists false
  iframe Hd
  iintro Hd
  imod Hmask with _
  imodintro
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ iprop(True) $$ [$Hsync $Hm $Hlk]
  iapply HΦ $$ HQ

end once

end bbolt
end EtcdGrove
end Perennial
