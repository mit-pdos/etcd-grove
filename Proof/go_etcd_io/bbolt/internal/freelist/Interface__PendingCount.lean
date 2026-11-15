/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__PendingCount.lean` (U2, `notes/bbolt-proof-plan.md`),
over `ifaceCall` (`Inv/Freelist.lean`; dispatch: `Lemmas/IfaceCall.lean`).
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__PendingCount
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.IfaceCall
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__PendingCount

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

theorem Interface.PendingCount.wp_proof : Interface.PendingCount.spec (GF := GF) (hG := hG) := by
  intro fli fl
  wp_start_folded as Hfl
  icases flPgOwn_open _ _ $$ Hfl with ⟨%I, %a, %s, %HIf, #Hhdl, Hown, Hsh⟩
  obtain ⟨HI, Hfli⟩ := HIf
  subst Hfli
  have hI' := HI
  iunfold ownSh at Hsh
  icases Hsh with ⟨%c, Hsh, %Hok⟩
  rcases HI with rfl | rfl <;> (
    isimp only [arrayImpl, hashImpl] at Hhdl
    iface_dispatch
    wp_apply (shared.PendingCount.wp_proof s _ fl c) $$ [Hsh] as Hsh
    · iframe
    iapply HΦ
    iapply flPgOwn_close _ a s _ fl hI' rfl
    isplitl []
    · isimp only [arrayImpl, hashImpl]; iexact Hhdl
    iframe
    iunfold ownSh
    iexists c
    iframe
    ipureintro; exact Hok)

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
