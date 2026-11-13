/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__Allocate.lean` (U2, `notes/bbolt-proof-plan.md`),
over `ifaceCall` (`Inv/Freelist.lean`; dispatch: `Lemmas/IfaceCall.lean`).
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Allocate
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

theorem Interface.Allocate.wp_proof
    (hA : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.AllocateSpec) :
    Interface.Allocate.spec (GF := GF) (hG := hG) := by
  intro fli fl txid n Hn
  wp_start_folded as Hfl
  icases flPgOwn_open _ _ $$ Hfl with ⟨%I, %a, %s, %HIf, #Hhdl, Hown, Hsh⟩
  obtain ⟨HI, Hfli⟩ := HIf
  subst Hfli
  rw [ifaceCall_impl]
  iapply (hA I a HI s fl txid n Hn) $$ [Hown Hsh]
  · iframe; isplitl []
    · iPkgInit
    iexact Hhdl
  inext
  iintro %r Hr
  iapply HΦ
  icases Hr with (⟨%H0, Hsh, Hown⟩ | ⟨%H1, Hsh, Hown⟩)
  · ileft
    isplitr
    · ipureintro; exact H0
    iapply flPgOwn_close _ a s _ fl HI rfl
    iframe
    iexact Hhdl
  · iright
    isplitr
    · ipureintro; exact H1
    iapply flPgOwn_close _ a s _ _ HI rfl
    iframe
    iexact Hhdl

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
