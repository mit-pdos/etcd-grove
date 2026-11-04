/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__Reload.lean` (U2, `notes/bbolt-proof-plan.md`): `wp_proof'`, of `spec'`, the spec over the call a caller reaches (`ifaceCall`, `Lemmas/IfaceCall.lean`: the frozen spec's expression is unreachable); `wp_proof` stays `sorry` until the frozen spec is restated.
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Reload
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.IfaceCall
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__Reload

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The spec over the call a caller reaches, with four more premises than the frozen spec,
which is false without them: the page's ids are distinct pages (at least 2) and not too many with
the pending ones (else `fl.reload (flIds pg)` is not `FLPg.WF`, which `flPgOwn` requires; a page
written by bbolt meets them), and the page has ids or no id was free (an empty page makes
`hashMap.Init` of no ids return before `reindex`, keeping the old cache: the old free ids would
stay cached). -/
abbrev Interface.Reload.spec' : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (p : Loc) (pg : List w8) (dq : DFrac),
  pageFlags pg = freelistPageFlag →
  16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length →
  (flCountIdx pg).1 < 2 ^ 63 → 0 < p.addr → p.addr + pg.length ≤ maxAddr →
  (flIds pg).Nodup → (∀ x ∈ flIds pg, 2 ≤ x.toNat) →
  (flIds pg).length + fl.pendingIds.length < 2 ^ 63 → (flIds pg ≠ [] ∨ fl.free = []) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl ∗
      bytesPointsto p dq pg }}
    (App (ifaceCall fli go!"Reload") (Val #p))
  {{ RET #(); flPgOwn fli (fl.reload (flIds pg)) ∗ bytesPointsto p dq pg }}

theorem Interface.Reload.wp_proof'
    (hI : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.InitSpec)
    (hIs : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.IsFreelistPage.spec
      (GF := GF) (hG := hG))
    (hIds : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.FreelistPageIds.spec
      (GF := GF) (hG := hG))
    (hF : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.FreePageIdsSpec) :
    Interface.Reload.spec' (GF := GF) (hG := hG) := by
  intro fli fl p pg dq Hfl Hsz Hcnt Hp Hmax Hnd Hge Hlen Hemp
  wp_start_folded as ⟨Hfl', Hpg⟩
  icases flPgOwn_open _ _ $$ Hfl' with ⟨%I, %a, %s, %HIf, #Hhdl, Hown, Hsh⟩
  obtain ⟨HI, Hfli⟩ := HIf
  subst Hfli
  have hInit := hI I a HI
  have hFPI := hF I a HI
  have Hemp' : flIds pg ≠ [] ∨ ∀ x ∈ fl.free, x ∈ fl.pendingIds := by
    rcases Hemp with h | h
    · exact Or.inl h
    · right; simp [h]
  have hI' := HI
  rcases HI with rfl | rfl <;> (
    isimp only [arrayImpl, hashImpl] at Hhdl
    iface_dispatch
    wp_apply (shared.Reload.wp_proof _ hInit hFPI hIs hIds s fl p pg dq Hfl Hsz Hcnt Hp Hmax
      Hnd Hge Hlen Hemp') $$ [Hsh Hown Hpg] as ⟨Hsh, Hown, Hpg⟩
    · iframe
      isplitl []
      · isimp only [arrayImpl, hashImpl]; iexact Hhdl
      iapply ownSh_w $$ Hsh
    iapply HΦ
    iframe Hpg
    iapply flPgOwn_close _ a s _ _ hI' rfl
    isplitl []
    · isimp only [arrayImpl, hashImpl]; iexact Hhdl
    isplitl [Hown]
    · iExactEq Hown; simp [FLPg.reload] <;> rfl
    iexact Hsh)

theorem Interface.Reload.wp_proof : Interface.Reload.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
