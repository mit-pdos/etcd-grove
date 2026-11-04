/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__Rollback.lean` (U2, `notes/bbolt-proof-plan.md`): `wp_proof'`, of `spec'` (the call a caller reaches; the code's model `FLPg.rollbackGo`); `wp_proof` stays `sorry` until the frozen spec is restated.
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Rollback
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.IfaceCall
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__Rollback

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

/-- The spec over the call a caller reaches (`ifaceCall`), and over the code's model
`FLPg.rollbackGo` (`Lemmas/Rollback.lean`: the frozen spec's `FLPg.rollback` also drops `txid`'s
allocations when `txid` has no pending entry, which the code does not). -/
abbrev Interface.Rollback.spec' : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (txid : w64),
  (∀ pd, fl.pending !! txid = some pd → txid ∉ pd.alloctx) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl }}
    (App (ifaceCall fli go!"Rollback") (Val #txid))
  {{ RET #(); flPgOwn fli (fl.rollbackGo txid) }}

theorem Interface.Rollback.wp_proof' : Interface.Rollback.spec' (GF := GF) (hG := hG) := by
  intro fli fl txid Hcan
  wp_start_folded as Hfl
  icases flPgOwn_open _ _ $$ Hfl with ⟨%I, %a, %s, %HIf, #Hhdl, Hown, Hsh⟩
  obtain ⟨HI, Hfli⟩ := HIf
  subst Hfli
  have hI' := HI
  rcases HI with rfl | rfl <;> (
    isimp only [arrayImpl, hashImpl] at Hhdl
    iface_dispatch
    wp_apply (shared.Rollback.wp_proof s _ fl txid Hcan) $$ [Hsh] as Hsh
    · iframe
    iapply HΦ
    iapply flPgOwn_close _ a s _ _ hI' rfl
    isplitl []
    · isimp only [arrayImpl, hashImpl]; iexact Hhdl
    iframe
    have hfree : (fl.rollbackGo txid).free = fl.free := by
      unfold FLPg.rollbackGo FLPg.rollback; split <;> rfl
    rw [hfree]
    iframe)

theorem Interface.Rollback.wp_proof : Interface.Rollback.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
