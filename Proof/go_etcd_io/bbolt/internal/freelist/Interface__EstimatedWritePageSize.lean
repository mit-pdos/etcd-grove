/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__EstimatedWritePageSize.lean` (U2, `notes/bbolt-proof-plan.md`),
over `ifaceCall` (`Inv/Freelist.lean`; dispatch: `Lemmas/IfaceCall.lean`).
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__EstimatedWritePageSize
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.IfaceCall
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__EstimatedWritePageSize

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

theorem Interface.EstimatedWritePageSize.wp_proof
    (hFC : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.FreeCountSpec) :
    Interface.EstimatedWritePageSize.spec (GF := GF) (hG := hG) := by
  intro fli fl
  wp_start_folded as Hfl
  icases flPgOwn_open _ _ $$ Hfl with ⟨%I, %a, %s, %HIf, #Hhdl, Hown, Hsh⟩
  obtain ⟨HI, Hfli⟩ := HIf
  subst Hfli
  have hFC' := hFC I a HI
  rcases HI with rfl | rfl <;> (
    isimp only [arrayImpl, hashImpl] at Hhdl
    iface_dispatch
    wp_apply (shared.EstimatedWritePageSize.wp_proof _ hFC' s fl) $$ [Hsh Hown] as ⟨Hsh, Hown⟩
    · iframe
    iapply HΦ
    iapply flPgOwn_close _ a s _ fl (by first | exact Or.inl rfl | exact Or.inr rfl) rfl
    isplitl []
    · isimp only [arrayImpl, hashImpl]; iexact Hhdl
    isplitl [Hown]
    · isimp only [arrayImpl, hashImpl]; iexact Hown
    iexact Hsh)

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
