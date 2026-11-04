/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__Free.lean` (U2, `notes/bbolt-proof-plan.md`): `wp_proof'`, of `spec'`, the spec over the call a caller reaches (`ifaceCall`, `Lemmas/IfaceCall.lean`: the frozen spec's expression is unreachable); `wp_proof` stays `sorry` until the frozen spec is restated.
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Free
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.IfaceCall
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__Free

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

abbrev Interface.Free.spec' : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (txid : w64) (p : Loc) (hdr : Page) (dq : DFrac),
  fl.canFree txid hdr.id' (1 + hdr.overflow'.toNat) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      flPgOwn fli fl ∗ p ↦{dq} hdr }}
    (App (App (ifaceCall fli go!"Free") (Val #txid)) (Val #p))
  {{ RET #(); flPgOwn fli (fl.freePages txid hdr.id' (1 + hdr.overflow'.toNat)) ∗ p ↦{dq} hdr }}

theorem Interface.Free.wp_proof'
    (hId : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hOv : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.Overflow.spec (GF := GF) (hG := hG))
    (hVerify : bbolt.common.Verify.spec (GF := GF) (hG := hG)) :
    Interface.Free.spec' (GF := GF) (hG := hG) := by
  intro fli fl txid p pv dq Hcan
  wp_start_folded as ⟨Hfl, Hp⟩
  icases flPgOwn_open _ _ $$ Hfl with ⟨%I, %a, %s, %HIf, #Hhdl, Hown, Hsh⟩
  obtain ⟨HI, Hfli⟩ := HIf
  subst Hfli
  have hI' := HI
  rcases HI with rfl | rfl <;> (
    isimp only [arrayImpl, hashImpl] at Hhdl
    iface_dispatch
    wp_apply (shared.Free.wp_proof hId hOv hVerify s _ fl txid p pv dq Hcan) $$ [Hsh Hp]
      as ⟨Hsh, Hp⟩
    · iframe
    iapply HΦ
    iframe Hp
    iapply flPgOwn_close _ a s _ _ hI' rfl
    isplitl []
    · isimp only [arrayImpl, hashImpl]; iexact Hhdl
    iframe)

theorem Interface.Free.wp_proof : Interface.Free.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
