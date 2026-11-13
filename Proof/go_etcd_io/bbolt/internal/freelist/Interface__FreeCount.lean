/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__FreeCount.lean` (U2, `notes/bbolt-proof-plan.md`),
over `ifaceCall` (`Inv/Freelist.lean`; dispatch: `Lemmas/IfaceCall.lean`).
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__FreeCount
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.IfaceCall

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

theorem Interface.FreeCount.wp_proof
    (hFC : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.FreeCountSpec) :
    Interface.FreeCount.spec (GF := GF) (hG := hG) := by
  intro fli fl
  wp_start_folded as Hfl
  icases flPgOwn_open _ _ $$ Hfl with ⟨%I, %a, %s, %HIf, #Hhdl, Hown, Hsh⟩
  obtain ⟨HI, Hfli⟩ := HIf
  subst Hfli
  have hFC' := hFC I a HI
  rw [ifaceCall_impl]
  iapply (hFC' fl.free) $$ [Hown]
  · iframe; iPkgInit
  inext
  iintro Hown
  iapply HΦ
  iapply flPgOwn_close _ a s _ fl HI rfl
  iframe
  iexact Hhdl

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
