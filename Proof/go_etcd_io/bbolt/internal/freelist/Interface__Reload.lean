/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__Reload.lean` (U2, `notes/bbolt-proof-plan.md`),
over `ifaceCall` (`Inv/Freelist.lean`; dispatch: `Lemmas/IfaceCall.lean`).
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

open Fs
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem Interface.Reload.wp_proof
    (hI : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.InitSpec)
    (hIs : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.IsFreelistPage.spec
      (GF := GF) (hG := hG))
    (hIds : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.FreelistPageIds.spec
      (GF := GF) (hG := hG))
    (hF : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.FreePageIdsSpec) :
    Interface.Reload.spec (GF := GF) (hG := hG) := by
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

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
