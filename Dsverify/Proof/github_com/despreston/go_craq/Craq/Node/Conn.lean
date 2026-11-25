module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Common
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Store
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Log
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.CommitM

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

section conn
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions] [LogSpecs GF]
variable [net.rpc.Assumptions] [π : NetProtoGS]

/-- The neighbors map's facts. -/
abbrev nbrsOk (cfg : Cfg GF) (nbrs : GMap w64 node.neighbor) : IProp GF :=
  iprop([∗map] _p ↦ nb ∈ nbrs, nbrOk cfg nb)

theorem nbrAt_ok (cfg : Cfg GF) (nbrs : GMap w64 node.neighbor) (p : w64) :
    nbrsOk cfg nbrs ⊢ nbrOk cfg (nbrAt nbrs p) := by
  unfold nbrAt
  cases h : nbrs !! p with
  | none =>
    iintro -
    unfold nbrOk; ileft; ipureintro; exact ⟨rfl, rfl⟩
  | some nb =>
    iintro #H
    iapply (BI.BigSepM.bigSepM_lookup (Φ := fun _ nb => nbrOk (hG := hG) cfg nb) h) $$ H

theorem nbrAt_zero (nbrs : GMap w64 node.neighbor) (p : w64) :
    (nbrs !! p).getD (zero_val node.neighbor) = nbrAt nbrs p := rfl

theorem nbrsOk_insert (cfg : Cfg GF) (nbrs : GMap w64 node.neighbor) (p : w64)
    (nb : node.neighbor) :
    nbrOk cfg nb ∗ nbrsOk cfg nbrs ⊢ nbrsOk cfg (<[p := nb]> nbrs) := by
  iintro ⟨#H1, #H2⟩
  iapply (BI.BigSepM.bigSepM_insert_elim (Φ := fun _ nb => nbrOk (hG := hG) cfg nb)) $$ H1 H2

/-- A neighbor's client is not nil iff it is a client of its address, which is not empty. -/
theorem nbrOk_cases (cfg : Cfg GF) (nb : node.neighbor) :
    nbrOk cfg nb ⊢ (⌜nb.rpc' = interface.nil ∧ nb.address' = go!""⌝ ∨
      ⌜nb.rpc' ≠ interface.nil ∧ nb.address' ∈ cfg.chain⌝ ∗ isNodeClient cfg nb.rpc' nb.address') := by
  iintro #H
  unfold nbrOk
  icases H with (%h | #Hc)
  · ileft; ipureintro; exact h
  · iright
    ihave #Hc' := Hc
    unfold isNodeClient
    icases Hc' with ⟨%e, ⟨%he, %ha⟩, -⟩
    iframe Hc
    ipureintro
    refine ⟨?_, ha⟩
    rw [he]; simp

/-- `n.connectToNode(addr, pos)`: a new client of `addr` at `pos` (the old one closed). -/
theorem wp_connectToNode (cfg : Cfg GF) (n : Loc) (a : GoString) (st : GoInterface) (γs : GName)
    (nbM latM : Loc) (nbrs : GMap w64 node.neighbor) (addr : GoString) (pos : w64)
    (hpos : pos = W64 0 ∨ pos = W64 1 ∨ pos = W64 2) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗
        nodeFields cfg n a st γs nbM latM ∗ nbM ↦$ nbrs ∗ nbrsOk cfg nbrs ∗ ⌜addr ∈ cfg.chain⌝) -∗
      (∀ err : GoInterface,
        ((⌜err = interface.nil⌝ ∗ ∃ c : GoInterface,
            nbM ↦$ (<[pos := node.neighbor.mk c addr]> nbrs) ∗
            nbrsOk cfg (<[pos := node.neighbor.mk c addr]> nbrs) ∗ isNodeClient cfg c addr) ∨
          (models_lab.errPlain err ∗ nbM ↦$ nbrs ∗ nbrsOk cfg nbrs)) -∗ Φ #err) -∗
      WP (App (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"connectToNode" #n))
        (Val #addr)) (Val #pos)) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hf, Hnbm, #Hnbrs, %Haddr⟩ HΦ
  unfold nodeFields
  icases Hf with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  wp_method_call
  wp_call
  wp_auto
  unfold isFactory
  wp_apply Hfac as %c Hc
  unfold freshNodeClient
  icases Hc with ⟨%e, %he, Hconn⟩
  subst he
  wp_auto
  ihave Hconn' := Hconn $$ %addr
  wp_apply Hconn' $$ []
  · ipureintro; exact Haddr
  iintro %err Herr
  icases Herr with (⟨%Herr, #Hcl⟩ | #Herr)
  · subst Herr
    wp_auto
    wp_log [interface.mkOk go.string #addr]
    · iapply argOks1; iapply argOk_string
    wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
    rw [nbrAt_zero]
    ihave #Hold := nbrAt_ok cfg nbrs pos $$ Hnbrs
    generalize nbrAt nbrs pos = nb at *
    obtain ⟨rpc, naddr⟩ := nb
    unfold nbrOk
    icases Hold with (%Hnil | #Hc)
    · obtain ⟨h1, -⟩ := Hnil
      simp only at h1
      subst h1
      wp_auto
      wp_apply wp_mapInsert $$ Hnbm with Hnbm
      iapply HΦ
      ileft
      iframe
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply nbrsOk_insert; iframe Hnbrs; unfold nbrOk; iright; iexact Hcl
      iexact Hcl
    · iunfold isNodeClient at Hc
      icases Hc with ⟨%e', ⟨%He', -⟩, #Hcs⟩
      simp only at He'
      subst He'
      icases Hcs with ⟨-, -, -, -, -, -, -, -, Hclose⟩
      wp_auto
      wp_apply Hclose as %err2
      wp_apply wp_mapInsert $$ Hnbm with Hnbm
      iapply HΦ
      ileft
      iframe
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply nbrsOk_insert; iframe Hnbrs; unfold nbrOk; iright; iexact Hcl
      iexact Hcl
  · ihave %Hok := errPlain_ok err $$ Herr
    obtain ⟨ei, rfl⟩ := Hok
    wp_auto
    iapply HΦ
    iright
    iframe; iframe #

/-- `n.resetNeighbor(pos)`: no neighbor at `pos` (the old one closed). -/
theorem wp_resetNeighbor (cfg : Cfg GF) (n : Loc) (a : GoString) (st : GoInterface) (γs : GName)
    (nbM latM : Loc) (nbrs : GMap w64 node.neighbor) (pos : w64) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗
        nodeFields cfg n a st γs nbM latM ∗ nbM ↦$ nbrs ∗ nbrsOk cfg nbrs) -∗
      (nbM ↦$ (<[pos := node.neighbor.mk interface.nil go!""]> nbrs) ∗
          nbrsOk cfg (<[pos := node.neighbor.mk interface.nil go!""]> nbrs) -∗ Φ #()) -∗
      WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"resetNeighbor" #n))
        (Val #pos)) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hf, Hnbm, #Hnbrs⟩ HΦ
  iunfold nodeFields at Hf
  icases Hf with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
  rw [nbrAt_zero]
  ihave #Hold := nbrAt_ok cfg nbrs pos $$ Hnbrs
  generalize nbrAt nbrs pos = nb at *
  obtain ⟨rpc, naddr⟩ := nb
  unfold nbrOk
  ihave #Hz : nbrOk cfg (node.neighbor.mk interface.nil go!"") $$ []
  · unfold nbrOk; ileft; ipureintro; exact ⟨rfl, rfl⟩
  icases Hold with (%Hnil | #Hc)
  · obtain ⟨h1, -⟩ := Hnil
    simp only at h1
    subst h1
    wp_auto
    wp_apply wp_mapInsert $$ Hnbm with Hnbm
    iapply HΦ
    iframe
    iapply nbrsOk_insert; iframe Hnbrs Hz
  · iunfold isNodeClient at Hc
    icases Hc with ⟨%e', ⟨%He', -⟩, #Hcs⟩
    simp only at He'
    subst He'
    icases Hcs with ⟨-, -, -, -, -, -, -, -, Hclose⟩
    wp_auto
    wp_apply Hclose as %err2
    wp_apply wp_mapInsert $$ Hnbm with Hnbm
    iapply HΦ
    iframe
    iapply nbrsOk_insert; iframe Hnbrs Hz

end conn

end NodeP

end github_com.despreston.go_craq

end Perennial
