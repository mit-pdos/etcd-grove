/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__Free.lean` (U2, `notes/bbolt-proof-plan.md`),
over `ifaceCall` (`Inv/Freelist.lean`; dispatch: `Lemmas/IfaceCall.lean`).
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

theorem Interface.Free.wp_proof
    (hId : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hOv : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.Overflow.spec (GF := GF) (hG := hG))
    (hVerify : _root_.Perennial.EtcdGrove.bbolt.internal.common.Verify.spec (GF := GF) (hG := hG)) :
    Interface.Free.spec (GF := GF) (hG := hG) := by
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

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
