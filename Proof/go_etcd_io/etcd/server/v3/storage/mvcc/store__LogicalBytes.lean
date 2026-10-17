/-
Proof of `Spec/.../mvcc/store__LogicalBytes.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__LogicalBytes
public import Perennial.Proof.sync.atomic

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.LogicalBytes.wp_proof : mvcc.store.LogicalBytes.spec (GF := GF) (hG := hG) := by
  intro s γ o
  wp_start as ⟨#Hs, Ho⟩
  iunfold mvcc.isStore at Hs
  iNamedSuffix Hs "S"
  wp_auto
  -- `atomic.LoadInt64(&s.logicalBytes)`, in the counter's invariant
  wp_apply_core sync.atomic.wp_LoadInt64 $$ [] [-]
  · iPkgInit
  iinv HlbinvS with ⟨%w, >Hf, >Hg⟩ Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w
  iframe Hf
  iintro Hf
  imod Hmask with -
  cases o with
  | none =>
    imod Hclose $$ [Hf Hg] with -
    · inext; iexists w; iframe Hf Hg
    imodintro
    wp_auto
    iapply HΦ
    ipureintro; exact ⟨trivial, fun _ h => by cases h⟩
  | some w0 =>
    ihave %Hw := ghostVar_agree γ.lb _ _ _ _ $$ Hg Ho
    imod Hclose $$ [Hf Hg] with -
    · inext; iexists w; iframe Hf Hg
    imodintro
    wp_auto
    iapply HΦ
    iframe Ho
    ipureintro; intro w' h; cases h; exact Hw

end proof

end EtcdGrove
end Perennial
