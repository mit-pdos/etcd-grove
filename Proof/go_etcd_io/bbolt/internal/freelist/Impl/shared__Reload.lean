/-
`shared.Reload(p)` (U2 internal): `Read(p)`, then `NoSyncReload(freePageIds())`: the free ids
become the freelist page's ids but the pending ones.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__Read
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__NoSyncReload

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

theorem sortPgids_perm_eq {l l' : List w64} (hp : l.Perm l') : sortPgids l = sortPgids l' :=
  sortPgids_eq_of_sorted (sortPgids_sorted l') ((sortPgids_perm l').trans hp.symm)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem ownShW_wfw (s : Loc) (fli : GoInterface) (fl : FLPg) :
    ownShW (GF := GF) s fli fl ⊢ ownShW s fli fl ∗ ⌜fl.WFw⌝ := by
  iintro H
  iunfold ownShW at H
  icases H with ⟨%c, H, %Hok⟩
  isplitl
  · iunfold ownShW; iexists c; iframe; ipureintro; exact Hok
  · ipureintro; exact Hok.2

/-- `t.Reload(p)` on the freelist page `pg` at `p`: the free ids become the page's ids but the
pending ones (`FLPg.reload`). The page's ids are distinct pages, not too many with the pending
ones (the result is well-formed); an empty page needs the old free ids all pending
(`hashMap.Init` of no ids keeps the old cache). The state before need only be weakly
well-formed. -/
abbrev shared.Reload.spec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (fl : FLPg) (p : Loc) (pg : List w8) (dq : DFrac),
  pageFlags pg = freelistPageFlag →
  16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length →
  (flCountIdx pg).1 < 2 ^ 63 → 0 < p.addr → p.addr + pg.length ≤ maxAddr →
  (flIds pg).Nodup → (∀ x ∈ flIds pg, 2 ≤ x.toNat) →
  (flIds pg).length + fl.pendingIds.length < 2 ^ 63 →
  (flIds pg ≠ [] ∨ ∀ x ∈ fl.free, x ∈ fl.pendingIds) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ I.hdl s ∗
      ownShW s I.iface fl ∗ I.own fl.free ∗ bytesPointsto p dq pg }}
    (App (Val #(methods (go.GoType.PointerType shared.ty) go!"Reload" #s)) (Val #p))
  {{ RET #(); ownSh s I.iface (fl.reload (flIds pg)) ∗ I.own (fl.reload (flIds pg)).free ∗
      bytesPointsto p dq pg }}

theorem shared.Reload.wp_proof (I : FLImpl (GF := GF)) (hInit : I.InitSpec)
    (hFPI : I.FreePageIdsSpec)
    (hIs : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.IsFreelistPage.spec
      (GF := GF) (hG := hG))
    (hIds : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.FreelistPageIds.spec
      (GF := GF) (hG := hG)) :
    shared.Reload.spec I := by
  intro s fl p pg dq Hfl Hsz Hcnt Hp Hmax Hnd Hge Hlen Hemp
  wp_start as ⟨#Hhdl, Hsh, Hown, Hpg⟩
  icases ownShW_wfw _ _ _ $$ Hsh with ⟨Hsh, %Hwf0⟩
  have Hinc : PgidsIncr (sortPgids (flIds pg)) := sortPgids_incr Hnd
  have Hperm := sortPgids_perm (flIds pg)
  have Hwf1 : ({ fl with free := sortPgids (flIds pg) } : FLPg).WFw := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := Hwf0
    refine ⟨h1, fun id hid => ?_, Hinc, ?_, h5⟩
    · rcases List.mem_append.1 hid with hx | hx
      · exact Hge id (Hperm.mem_iff.1 hx)
      · exact h2 id (List.mem_append_right _ hx)
    · show (sortPgids (flIds pg) ++ fl.pendingIds).length < _
      rw [List.length_append, Hperm.length_eq]; exact Hlen
  wp_auto
  wp_apply (shared.Read.wp_proof I hInit hIs hIds s fl p pg dq Hfl Hsz Hcnt Hp Hmax Hwf1 Hemp)
    $$ [Hsh Hown Hpg] as ⟨Hsh, Hown, Hpg⟩
  · iframe
    iexact Hhdl
  generalize hfl1 : ({ fl with free := sortPgids (flIds pg) } : FLPg) = fl1 at Hwf1
  iunfold ownShW at Hsh
  icases Hsh with ⟨%c1, Hsh, %Hok1⟩
  iunfold ownShC at Hsh
  iNamed Hsh
  wp_method_call
  wp_call
  try wp_auto
  have hfree1 : fl1.free = sortPgids (flIds pg) := by rw [← hfl1]
  have hpend1 : fl1.pendingIds = fl.pendingIds := by rw [← hfl1]; rfl
  rw [← hfree1]
  wp_apply (hFPI fl1.free) $$ [Hown] as %r ⟨Hr, Hback⟩
  · iframe
  ihave Hsh : ownShW s I.iface fl1 $$ [Hif Hal Hallocs Hca Hcache Hpe Hpending Hpds]
  · iunfold ownShW; iexists c1
    isplitl
    · iunfold ownShC; iexists al, ca, pe, pp; iframe
    · ipureintro; exact Hok1
  have Hge1 : ∀ x ∈ fl1.free, 2 ≤ x.toNat := by
    rw [hfree1]; intro x hx; exact Hge x (Hperm.mem_iff.1 hx)
  have Hlen1 : fl1.free.length + fl1.pendingIds.length < 2 ^ 63 := by
    rw [hfree1, hpend1, Hperm.length_eq]; exact Hlen
  have Hemp1 : fl1.free.filter (fun x => decide (x ∉ fl1.pendingIds)) ≠ [] ∨
      ∀ x ∈ fl1.free, x ∈ fl1.pendingIds := by
    by_cases h : fl1.free.filter (fun x => decide (x ∉ fl1.pendingIds)) = []
    · right; intro x hx
      have := List.filter_eq_nil_iff.1 h x hx
      simpa using this
    · left; exact h
  wp_apply (shared.NoSyncReload.wp_proof I hInit s fl1 r fl1.free (DFrac.own 1) iprop(True)
    (by rw [hfree1]; exact Hinc) Hge1 Hlen1 Hemp1) $$ [Hsh Hr Hback] as ⟨Hsh, Hown, -⟩
  · iframe
    isplitl []
    · iexact Hhdl
    iintro Hr
    isplitl
    · iapply Hback $$ Hr
    · itrivial
  have hre : fl1.reload fl1.free = fl.reload (flIds pg) := by
    rw [← hfl1]
    unfold FLPg.reload
    simp only
    congr 1
    apply sortPgids_perm_eq
    exact (List.Perm.filter _ Hperm)
  rw [hre]
  iapply HΦ
  iframe
  iExactEq Hown
  rw [← hre]
  simp [FLPg.reload]

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
