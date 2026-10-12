/-
Accessors of the database predicate (`DBPred.lean`): a field of the database taken out of
`ownDB`, and given back.
-/
module

public import Proof.go_etcd_io.bbolt.DBPred
public import Spec.go_etcd_io.bbolt.getDiscardLogger

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section acc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The database's logger (nil or the default one): persistent facts of `ownDB`. -/
theorem ownDB_logger (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState) :
    ownDB I dbl γ σ ⊢ ∃ (lg : GoInterface) (dl : Loc),
      structFieldRef DB go!"logger" dbl ↦□ lg ∗ (globalAddr discardLogger ↦□ dl : IProp GF) ∗
      defaultLoggerOK dl ∗
      ⌜(lg = interface.nil ∨ lg = discardIface dl) ∧ dbl ≠ null⌝ ∗ ownDB I dbl γ σ := by
  iintro Hdb
  isimp only [ownDB] at Hdb
  iNamed Hdb
  iexists dv.logger', dl
  iframe #
  isplitr
  · ipureintro; exact ⟨Hlog, Hdv.2.2.2.2.2.2.2.2.2⟩
  simp only [ownDB]
  iexists dv, fls, v0, v1, dl
  isplitr
  · ipureintro; exact Hdv
  isplitr
  · ipureintro; exact Hok
  iframe
  iframe #
  try (ipureintro; exact Hlog)

end acc

end bbolt
end EtcdGrove
end Perennial
