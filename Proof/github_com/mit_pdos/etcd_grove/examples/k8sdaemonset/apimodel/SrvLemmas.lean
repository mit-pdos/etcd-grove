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

/-- **A resource's table among the four**, and putting a new one back. -/
theorem tablesLocked_acc (L : SrvLocs) (σ : St) (r : Res) :
    tablesLocked (GF := GF) L σ ⊢ tableLocked (L.tbl r) (σ.tbl r) ∗
      (∀ σ' : St, ⌜∀ r', r' ≠ r → σ'.tbl r' = σ.tbl r'⌝ -∗ tableLocked (L.tbl r) (σ'.tbl r) -∗
        tablesLocked L σ') := by
  unfold tablesLocked
  iintro ⟨Hp, Hn, Hd, Hc⟩
  cases r
  · simp only [SrvLocs.tbl, St.tbl]
    iframe Hp
    iintro %σ' %Heq Hp'
    have h1 := Heq .nodes (by decide)
    have h2 := Heq .daemonSets (by decide)
    have h3 := Heq .revisions (by decide)
    simp only [St.tbl] at h1 h2 h3
    rw [h1, h2, h3]
    iframe
  · simp only [SrvLocs.tbl, St.tbl]
    iframe Hn
    iintro %σ' %Heq Hn'
    have h1 := Heq .pods (by decide)
    have h2 := Heq .daemonSets (by decide)
    have h3 := Heq .revisions (by decide)
    simp only [St.tbl] at h1 h2 h3
    rw [h1, h2, h3]
    iframe
  · simp only [SrvLocs.tbl, St.tbl]
    iframe Hd
    iintro %σ' %Heq Hd'
    have h1 := Heq .pods (by decide)
    have h2 := Heq .nodes (by decide)
    have h3 := Heq .revisions (by decide)
    simp only [St.tbl] at h1 h2 h3
    rw [h1, h2, h3]
    iframe
  · simp only [SrvLocs.tbl, St.tbl]
    iframe Hc
    iintro %σ' %Heq Hc'
    have h1 := Heq .pods (by decide)
    have h2 := Heq .nodes (by decide)
    have h3 := Heq .daemonSets (by decide)
    simp only [St.tbl] at h1 h2 h3
    rw [h1, h2, h3]
    iframe

end lemmas

end apimodel
end EtcdGrove
end Perennial
