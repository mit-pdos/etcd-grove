/-
`once.Do(f)` on a `sync.Once` nobody else uses, never run before (its zero value, owned): it runs
`f` (`Q`, not necessarily persistent, unlike Perennial's `Once.wp_Do`, which shares a `Once`).
bbolt's `loadFreelist` runs once this way in `Open`: the freelist it makes is the database's.
-/
module

public import Perennial.Proof.sync_proof.once

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem Once.wp_Do_fresh (o : Loc) (P Q : IProp GF) (f : GoFunc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ typedPointsto o (zero_val sync.Once) (DFrac.own 1) ∗
        P ∗ iprop({{ P }} (App (Val #f) (Val #())) {{ RET #(); Q }}) }}
      (App (Val (o @!! go.GoType.PointerType sync.Once.ty @!! go!"Do")) (Val #f))
    {{ RET #(); Q }} := by
  wp_start as ⟨Ho, HP, Hf⟩
  iStructNamed Ho
  have hz : (zero_val sync.atomic.Bool') =
      ({ _0' := zero_val _, v' := sync.atomic.b32w false } : sync.atomic.Bool') := rfl
  ihave Hd : sync.atomic.ownBool (GF := GF) (structFieldRef sync.Once go!"done" o) (DFrac.own 1) false $$ [done]
  · simp only [sync.atomic.ownBool_unseal, sync.atomic.ownBoolDef]
    rw [← hz]; iexact done
  imod sync.init_Mutex iprop(True) ⊤ (structFieldRef sync.Once go!"m" o) $$ m [] with #Hm
  · inext; itrivial
  wp_auto
  wp_apply_core sync.atomic.Bool.wp_Load $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists false
  iframe Hd
  iintro Hd
  imod Hmask with _
  imodintro
  wp_auto
  rw [method_unfold]
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hm] with ⟨Hlocked, -⟩
  wp_apply_core sync.atomic.Bool.wp_Load $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists false
  iframe Hd
  iintro Hd
  imod Hmask with _
  imodintro
  try wp_auto
  wp_apply Hf $$ HP with HQ
  try wp_auto
  wp_apply_core sync.atomic.Bool.wp_Store $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists false
  iframe Hd
  iintro Hd
  imod Hmask with _
  imodintro
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hlocked]
  · iframe #; inext; itrivial
  try wp_auto
  iapply HΦ $$ HQ

end wps

end EtcdGrove
end Perennial
