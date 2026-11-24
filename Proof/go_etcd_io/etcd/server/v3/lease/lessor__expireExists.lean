/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__expireExists.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__expireExists
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__Len
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__Peek
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__Unregister
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__RegisterOrUpdate
public import Proof.go_etcd_io.etcd.server.v3.lease.NotifCell

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.expireExists.wp_proof
    (hLen : lease.LeaseExpiredNotifier.Len.spec (GF := GF) (hG := hG))
    (hPeek : lease.LeaseExpiredNotifier.Peek.spec (GF := GF) (hG := hG))
    (hUnreg : lease.LeaseExpiredNotifier.Unregister.spec (GF := GF) (hG := hG))
    (hReg : lease.LeaseExpiredNotifier.RegisterOrUpdate.spec (GF := GF) (hG := hG)) :
    lease.lessor.expireExists.spec (GF := GF) (hG := hG) := by
  intro lp lm np dm dn M ri
  wp_start as ⟨Hlm, HM, Hnp, Hn, #Hri⟩
  ihave #Htpkg : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  iunfold notifierAt at Hn
  icases Hn with ⟨%N, Hn⟩
  wp_auto
  wp_apply (hLen np 1 N) $$ [$Hpkg $Hn] as ⟨Hn, %Hlt⟩
  (try wp_auto)
  by_cases h0 : N = ∅
  · have hs : GMap.size N = 0 := by rw [h0]; exact GMap.map_size_empty
    rw [hs]
    (try wp_auto)
    iapply HΦ
    iframe Hlm HM Hnp
    isplitl [Hn]
    · iunfold notifierAt; iexists N; iexact Hn
    ileft; ipureintro; rfl
  have hs : W64 (GMap.size N : Int) ≠ W64 0 := by
    intro h
    apply h0
    have : GMap.size N = 0 := by word
    exact (GMap.map_size_empty_iff N).1 this
  rw [decide_eq_false hs]
  (try wp_auto)
  wp_apply (hPeek np 1 N) $$ [$Hpkg $Hn] as %p ⟨Hn, Hp⟩
  icases Hp with (%Hp | ⟨%id, %Hid, #HidF⟩)
  · exact absurd Hp.2 h0
  (try wp_auto)
  wp_apply (wp_map_lookup1 LeaseID.ty (go.GoType.PointerType Lease.ty) lm M id dm) $$ HM as HM
  (try wp_auto)
  by_cases hl : (M !! id).getD (zero_val Loc) = null
  · rw [hl]
    simp only [decide_true]
    (try wp_auto)
    wp_apply (hUnreg np N h0) $$ [$Hpkg $Hn] as %p' ⟨%id', %k', %Hid', Hn, -⟩
    (try wp_auto)
    iapply HΦ
    iframe Hlm HM Hnp
    isplitl [Hn]
    · iunfold notifierAt; iexists _; iexact Hn
    ileft; ipureintro; rfl
  rw [decide_eq_false hl]
  (try wp_auto)
  wp_apply time.wp_Now as %now -
  (try wp_auto)
  icases notifierAtM_time np N id p Hid $$ Hn with ⟨⟨%t, Ht⟩, Hback⟩
  (try wp_auto)
  wp_apply _root_.Perennial.time.Time.wp_ptr_Before $$ [now] as %b now
  · iexact now
  by_cases hb : b = true
  · subst hb
    (try wp_auto)
    ihave Hn := Hback $$ %t Ht
    iapply HΦ
    iframe Hlm HM Hnp
    isplitl [Hn]
    · iunfold notifierAt; iexists N; iexact Hn
    ileft; ipureintro; rfl
  have hb' : b = false := by cases b <;> simp_all
  subst hb'
  (try wp_auto)
  wp_apply _root_.Perennial.time.Time.wp_ptr_Add $$ [now] as %t' now
  · iexact now
  (try wp_auto)
  ihave Hn := Hback $$ %t' Ht
  wp_apply (hReg np p id (W64 0) N) $$ [$Hpkg $Hn] as Hn
  · iright; ipureintro; exact Hid
  (try wp_auto)
  iapply HΦ
  iframe Hlm HM Hnp Hn
  iright; ipureintro
  refine ⟨id, ?_⟩
  cases hM : M !! id with
  | none => rw [hM] at hl; exact absurd rfl hl
  | some v => rfl

end proof

end EtcdGrove
end Perennial
