/-
The proof of `Spec/go_etcd_io/bbolt/DB__Close_noErr.lean`: `DB.Close`'s proof, generic in its
`close`'s error (`DB.Close.wp_proofQ`), at `(· = nil)`, over `DB.close.spec_ownedNoErr`
(`Open/CloseNoErr.lean`).
-/
module

public import Spec.go_etcd_io.bbolt.DB__Close_noErr
public import Proof.go_etcd_io.bbolt.DB__Close
import all Proof.go_etcd_io.bbolt.DB__Close
public import Proof.go_etcd_io.bbolt.Open.CloseNoErr

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

theorem DB.Close_noErr.wp_proof
    (hOwned : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
      DB.close.spec_ownedNoErr (GF := GF) (hG := hG)) :
    DB.Close_noErr.spec (GF := GF) (hG := hG) := by
  intro _ _ _ Sio _ _ hS db γ
  refine DB.Close.wp_proofQ (· = GoInterface.nil) rfl ?_ db γ
  intro db lg dqr fli wa s ms p f hdb
  iintro %Φ Hpre HΦ
  iapply hOwned Sio hS db lg dqr fli wa s ms p f hdb $$ Hpre
  inext
  iintro Hpost
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iexact Hpost

end proof

end bbolt
end EtcdGrove
end Perennial
