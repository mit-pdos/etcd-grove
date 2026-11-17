/-
The proof of `Spec/go_etcd_io/bbolt/DB__Close_ownNoErr.lean` (session bbolt-inv): `DB.Close_own.spec`,
whose `¬ FsNoErr` case the premises refute (`FsNoErr` is the premises).
-/
module

public import Spec.go_etcd_io.bbolt.DB__Close_ownNoErr
public import Spec.go_etcd_io.bbolt.DB__Close_own

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.Close_ownNoErr.wp_proof (hOwn : DB.Close_own.spec (GF := GF) (hG := hG)) :
    DB.Close_ownNoErr.spec (GF := GF) (hG := hG) := by
  intro _ _ _ Sio h1 h2 hS db γ i D
  have hne : FsNoErr := ⟨Sio, hS, h1, h2⟩
  iintro %Φ Hpre HΦ
  iapply hOwn db γ i D $$ Hpre
  inext
  iintro %err Hpost
  iapply HΦ
  icases Hpost with (⟨%he, Hf⟩ | ⟨Hst, (%hn | ⟨%he, #Hnf⟩)⟩)
  · isplitr
    · ipureintro; exact he
    · ileft; iexact Hf
  · exact absurd hne hn
  · isplitr
    · ipureintro; exact he
    · iright; iframe Hst; iexact Hnf

end proof

end bbolt
end EtcdGrove
end Perennial
