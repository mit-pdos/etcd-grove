/-
`sync/atomic`'s `LoadInt64`/`AddInt64` on a counter the caller owns (bbolt's statistics):
Perennial's specs are logically atomic; these are their non-atomic instances.
-/
module

public import Proof.go_etcd_io.bbolt.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode

section atomics
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

include package_sem in
theorem wp_LoadInt64_own (addr : Loc) (dq : DFrac) (v : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ addr ↦{dq} v }}
      (App (Val (@! sync.atomic.LoadInt64)) (Val #addr))
    {{ RET #v; addr ↦{dq} v }} := by
  iintro %Φ ⟨#Hpkg, Ha⟩ HΦ
  wp_apply_core sync.atomic.wp_LoadInt64 $$ [] [Ha HΦ]
  · iexact Hpkg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v
  iframe Ha
  iintro Ha
  imod Hmask with -
  imodintro
  iapply HΦ $$ Ha

include package_sem in
theorem wp_AddInt64_own (addr : Loc) (v d : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ addr ↦ v }}
      (App (App (Val (@! sync.atomic.AddInt64)) (Val #addr)) (Val #d))
    {{ RET #(v + d); addr ↦ (v + d) }} := by
  iintro %Φ ⟨#Hpkg, Ha⟩ HΦ
  wp_apply_core sync.atomic.wp_AddInt64 $$ [] [Ha HΦ]
  · iexact Hpkg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v
  iframe Ha
  iintro Ha
  imod Hmask with -
  imodintro
  iapply HΦ $$ Ha

end atomics

end bbolt
end EtcdGrove
end Perennial
