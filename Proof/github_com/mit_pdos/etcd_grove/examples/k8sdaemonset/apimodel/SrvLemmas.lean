/-
**The server's predicates: lemmas** (a resource's table among the fixed facts). Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A resource's table's fixed facts, from the server's. -/
theorem srvFixed_tbl (s : Loc) (γ : ApiNames) (L : SrvLocs) (cfg : _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (r : Res) :
    srvFixed (GF := GF) s γ L cfg ⊢ tableFixed r (L.tbl r) ∗ tableOf s r (L.tbl r).t := by
  iintro #Hs
  iNamed Hs
  cases r <;> simp only [SrvLocs.tbl] <;> iframe #

/-- The table a `tableOf` names is the server's. -/
theorem srvFixed_tableOf (s : Loc) (γ : ApiNames) (L : SrvLocs) (cfg : _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (r : Res) (t : Loc) :
    srvFixed (GF := GF) s γ L cfg ∗ tableOf s r t ⊢ ⌜t = (L.tbl r).t⌝ := by
  iintro ⟨#Hs, #Ht⟩
  ihave ⟨-, #Ht'⟩ := srvFixed_tbl s γ L cfg r $$ Hs
  unfold tableOf
  icombine Ht Ht' gives %Heq
  ipureintro
  exact Heq

end lemmas

end apimodel
end EtcdGrove
end Perennial
