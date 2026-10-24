/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/ioutil/NewLimitedBufferReader.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.ioutil.NewLimitedBufferReader

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

theorem ioutil.NewLimitedBufferReader.wp_proof :
    ioutil.NewLimitedBufferReader.spec (GF := GF) (hG := hG) := by
  intro rd Src B e n hn
  wp_start as #Hrd
  wp_auto
  wp_alloc l as Hl
  ipersist Hl
  wp_auto
  iapply HΦ
  unfold http.prefixReaderOk
  iexists ⟨go.GoType.PointerType ioutil.limitedBufferReader.ty, #l⟩
  isplitr
  · ipureintro; rfl
  iintro !> %r %p %xs %Φ' !> ⟨Hsrc, Hp, #He⟩ HΦ'
  icases Hrd with ⟨%ri, %Hri, #HR⟩
  subst Hri
  simp only
  iStructNamed Hl
  rw [method_unfold (t := go.GoType.PointerType ioutil.limitedBufferReader.ty) (m := go!"Read")]
  wp_pures
  wp_auto
  wp_if_destruct
  · -- `len(p) > r.n`: the read capped at `n` bytes, into `p[:n]`
    ihave %Hwf := ownSlice_wf p _ xs $$ Hp
    ihave %Hlen := ownSlice_len p _ xs $$ Hp
    rw [if_pos (by refine ⟨by decide, by word, by word⟩)]
    wp_auto
    icases (ownSlice_split_all n p (DFrac.own 1) xs ⟨by word, by word⟩).1 $$ Hp with ⟨Hp1, Hp2⟩
    wp_apply HR $$ [$Hsrc $Hp1 $He]
      as %k %err ⟨%ys, %Hys, Hp1, Hsrc⟩
    iapply HΦ'
    iexists ys
    ihave %Hl1 := ownSlice_len _ _ _ $$ Hp1
    simp only [slice.slice, List.length_append, List.length_drop, List.length_take] at Hl1
    have hn : sint.nat n < xs.length := by word
    have hys : ys.length ≤ sint.nat n := by
      have := Hl1.1
      rw [show sint.nat (n - W64 0) = sint.nat n by word] at this
      omega
    iframe Hsrc
    isplitr
    · ipureintro; exact Hys
    iapply (ownSlice_split_all n p (DFrac.own 1) (ys ++ xs.drop ys.length) ⟨by word, by word⟩).2
    have e1 : (ys ++ xs.drop ys.length).take (sint.nat n) =
        ys ++ (xs.take (sint.nat n)).drop ys.length := by
      rw [List.take_append, List.take_of_length_le hys, List.drop_take]
    have e2 : (ys ++ xs.drop ys.length).drop (sint.nat n) = xs.drop (sint.nat n) := by
      rw [List.drop_append, List.drop_of_length_le hys, List.nil_append, List.drop_drop]
      congr 1; omega
    rw [e1, e2]
    iframe Hp1 Hp2
  -- `len(p) ≤ r.n`: the read into `p`
  wp_apply HR $$ [$Hsrc $Hp $He] as %k %err Hres
  iapply HΦ'
  iexact Hres

end proof

end EtcdGrove
end Perennial
