/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/stm__reset.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__reset

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem stm.reset.wp_proof : stm.reset.spec (GF := GF) (hG := hG) := by
  intro b pfx
  wp_start as ⟨⟨%m1, Hr⟩, ⟨%m2, Hw⟩⟩
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string
    (go.GoType.PointerType go_etcd_io.etcd.client.v3.GetResponse.ty)) as %rm Hrm
  wp_apply (wp_map_make1 (K := GoString) (V := stmPut) go.string stmPut.ty) as %wm Hwm
  iapply HΦ
  isplitl [Hr Hrm]
  · unfold stmRsetOwn
    iexists rm, ∅
    iframe Hr Hrm
    unfold readsAt
    isplitr
    · ipureintro; intro k; rfl
    imodintro
    iintro %k %p %e %Hp %He
    simp at Hp
  · unfold stmWsetOwn
    iexists wm, ∅
    iframe Hw Hwm
    unfold writesAt
    isplitr
    · ipureintro; intro k; rfl
    imodintro
    iintro %k %sp %w %Hsp %Hw
    simp at Hsp

end proof

end concurrency
end EtcdGrove
end Perennial
