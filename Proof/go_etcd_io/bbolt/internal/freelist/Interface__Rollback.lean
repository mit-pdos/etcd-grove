/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__Rollback.lean` (U2, `notes/bbolt-proof-plan.md`),
over `ifaceCall` (`Inv/Freelist.lean`; dispatch: `Lemmas/IfaceCall.lean`).
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

theorem Interface.Rollback.wp_proof : Interface.Rollback.spec (GF := GF) (hG := hG) := by
  intro fli fl txid Hcan
  rw [← FLPg.rollbackGo_eq]
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
      unfold FLPg.rollbackGo FLPg.rollbackEntry; split <;> rfl
    rw [hfree]
    iframe)

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
