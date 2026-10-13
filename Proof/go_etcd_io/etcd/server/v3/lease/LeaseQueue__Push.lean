/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/LeaseQueue__Push.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseQueue__Push
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.LeaseQueue.Push.wp_proof : lease.LeaseQueue.Push.spec (GF := GF) (hG := hG) := by
  intro qf s xs p id k
  wp_start as ⟨Hqf, Hq, Hit⟩
  iunfold queueAt at Hq
  icases Hq with ⟨Hs, Hcap, Hits⟩
  ihave %Hlen := ownSlice_len s _ _ $$ Hs
  simp only [List.length_map] at Hlen
  iunfold lwtAt at Hit
  icases Hit with ⟨#Hid, Ht, Hix⟩
  wp_auto
  wp_apply wp_slice_literal (V := Loc) [p]
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_auto
  wp_apply wp_slice_append s (xs.map Prod.fst) _ [p] (DFrac.own 1) $$ [$Hs $Hcap $Hsl] as %s' ⟨Hs', Hcap', -⟩
  iapply HΦ
  iexists s'
  iframe
  iunfold queueAt
  simp only [List.map_append, List.map_cons, List.map_nil]
  iframe Hs' Hcap'
  iapply BigSepL.bigSepL_snoc.2
  iframe Hits
  iunfold lwtAt
  have hk : (W64 ((xs.length : Nat) : Int) : w64) = s.len := by rw [Hlen.1]; word
  rw [hk]
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
