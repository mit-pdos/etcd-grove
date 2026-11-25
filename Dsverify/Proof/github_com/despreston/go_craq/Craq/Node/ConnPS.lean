module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Common
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Store
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Log
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.CommitM
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.UpdSpecs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Conn

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

section connps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [π : NetProtoGS]

theorem nbrAt_insert_eq [GooseExts] (nbrs : GMap w64 node.neighbor) (p : w64) (nb : node.neighbor) :
    nbrAt (<[p := nb]> nbrs) p = nb := by
  unfold nbrAt; rw [GMap.lookup_insert_eq]; rfl

theorem nbrAt_insert_ne [GooseExts] (nbrs : GMap w64 node.neighbor) (p q : w64) (nb : node.neighbor)
    (h : q ≠ p) : nbrAt (<[q := nb]> nbrs) p = nbrAt nbrs p := by
  unfold nbrAt; rw [GMap.lookup_insert_ne _ _ h]

/-- `n.connectToPredecessor(addr)` under the lock. -/
theorem wp_connectToPredecessor (Hfwd : requestFwdPropagation.spec (GF := GF) (hG := hG))
    (cfg : Cfg GF) (n : Loc) (a : GoString) (st : GoInterface) (γs : GName) (nbM latM : Loc)
    (h t : Bool) (nbrs : GMap w64 node.neighbor) (lat : GMap GoString w64) (S : StoreS)
    (addr : GoString) (haddr : addr ∈ go!"" :: cfg.chain) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ craqCtx cfg ∗
        nodeFields cfg n a st γs nbM latM ∗ lockedState cfg γs n nbM latM h t nbrs lat S) -∗
      (∀ err : GoInterface, (∃ (nbrs' : GMap w64 node.neighbor) (S' : StoreS),
          lockedState cfg γs n nbM latM h t nbrs' lat S' ∗
          ⌜nbrAt nbrs' (W64 1) = nbrAt nbrs (W64 1)⌝ ∗
          ⌜err = interface.nil → (nbrAt nbrs' (W64 0)).address' = addr⌝) -∗
        (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"connectToPredecessor" #n))
        (Val #addr)) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hctx, #Hf, Hls⟩ HΦ
  ihave #Hf' := Hf
  iunfold nodeFields at Hf'
  icases Hf' with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  iunfold lockedState at Hls
  icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs, HS, %HlatS, Htail⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
  rw [nbrAt_zero]
  ihave #Hz : nbrOk cfg (node.neighbor.mk interface.nil go!"") $$ []
  · unfold nbrOk; ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_if_destruct
  · -- the same predecessor
    wp_logln [interface.mkOk go.string #(go!"New predecessor same address as last one, keeping conn.")]
    · iapply argOks1; iapply argOk_string
    iapply HΦ $$ [Hh Ht Hnbm Hlatm HS Htail] []
    · iexists nbrs, S
      isplitl [Hh Ht Hnbm Hlatm HS Htail]
      · unfold lockedState; iframe; iframe #; ipureintro; exact HlatS
      ipureintro
      exact ⟨rfl, fun _ => rfl⟩
    ileft; ipureintro; rfl
  · wp_if_destruct
    · -- no predecessor
      wp_logln [interface.mkOk go.string #(go!"Resetting predecessor")]
      · iapply argOks1; iapply argOk_string
      wp_apply wp_resetNeighbor cfg n a st γs nbM latM nbrs (W64 0) $$ [$Hpkg $Hf $Hnbm $Hnbrs]
        as ⟨Hnbm, #Hnbrs'⟩
      iapply HΦ $$ [Hh Ht Hnbm Hlatm HS Htail] []
      · iexists _, S
        isplitl [Hh Ht Hnbm Hlatm HS Htail]
        · unfold lockedState; iframe; iframe #; ipureintro; exact HlatS
        ipureintro
        refine ⟨nbrAt_insert_ne _ _ _ _ (by decide), fun _ => ?_⟩
        rw [nbrAt_insert_eq]
      ileft; ipureintro; rfl
    · -- a new predecessor
      wp_log [interface.mkOk go.string #addr]
      · iapply argOks1; iapply argOk_string
      have haddr' : addr ∈ cfg.chain := by
        rcases List.mem_cons.1 haddr with h' | h'
        · exact absurd h' Hif
        · exact h'
      wp_apply wp_connectToNode cfg n a st γs nbM latM nbrs addr (W64 0) (by simp)
        $$ [$Hpkg $Hf $Hnbm $Hnbrs] as %err Hres
      · ipureintro; exact haddr'
      icases Hres with (⟨%Herr, %c, Hnbm, #Hnbrs', #Hc⟩ | ⟨#Herr, Hnbm, -⟩)
      · subst Herr
        wp_auto
        wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
        wp_apply (Hfwd cfg n a st γs nbM latM h t _ lat S c addr)
          $$ [Hh Ht Hnbm Hlatm HS Htail] as %err ⟨%S', Hls⟩ Hres
        · iframe; iframe #
          unfold lockedState; iframe; iframe #; ipureintro; exact HlatS
        iapply HΦ $$ [Hls] [Hres]
        · iexists _, S'
          iframe
          ipureintro
          refine ⟨nbrAt_insert_ne _ _ _ _ (by decide), fun _ => ?_⟩
          rw [nbrAt_insert_eq]
        iexact Hres
      · ihave %Hok := errAny_ok err $$ Herr
        obtain ⟨ei, rfl⟩ := Hok
        wp_auto
        iapply HΦ $$ [Hh Ht Hnbm Hlatm HS Htail] []
        · iexists nbrs, S
          isplitl [Hh Ht Hnbm Hlatm HS Htail]
          · unfold lockedState; iframe; iframe #; ipureintro; exact HlatS
          ipureintro
          refine ⟨rfl, fun h => ?_⟩
          cases h
        iright; iexact Herr

/-- `n.connectToSuccessor(addr)` under the lock. -/
theorem wp_connectToSuccessor (HL : Laws (GF := GF))
    (Hback : requestBackPropagation.spec (GF := GF) (hG := hG))
    (cfg : Cfg GF) (n : Loc) (a : GoString) (st : GoInterface) (γs : GName) (nbM latM : Loc)
    (h t : Bool) (nbrs : GMap w64 node.neighbor) (lat : GMap GoString w64) (S : StoreS)
    (addr : GoString) (haddr : addr ∈ go!"" :: cfg.chain) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ craqCtx cfg ∗
        nodeFields cfg n a st γs nbM latM ∗ lockedState cfg γs n nbM latM h t nbrs lat S) -∗
      (∀ err : GoInterface, (∃ (nbrs' : GMap w64 node.neighbor) (lat' : GMap GoString w64)
          (S' : StoreS), lockedState cfg γs n nbM latM h t nbrs' lat' S' ∗
          ⌜err = interface.nil → nextAddr nbrs' = addr⌝) -∗
        (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"connectToSuccessor" #n))
        (Val #addr)) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hctx, #Hf, Hls⟩ HΦ
  ihave #Hf' := Hf
  iunfold nodeFields at Hf'
  icases Hf' with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  iunfold lockedState at Hls
  icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs, HS, %HlatS, Htail⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
  rw [nbrAt_zero]
  wp_if_destruct
  · -- the same successor
    wp_logln [interface.mkOk go.string #(go!"New successor same address as last one, keeping conn.")]
    · iapply argOks1; iapply argOk_string
    iapply HΦ $$ [Hh Ht Hnbm Hlatm HS Htail] []
    · iexists nbrs, lat, S
      isplitl [Hh Ht Hnbm Hlatm HS Htail]
      · unfold lockedState; iframe; iframe #; ipureintro; exact HlatS
      ipureintro
      exact fun _ => rfl
    ileft; ipureintro; rfl
  · wp_if_destruct
    · -- no successor
      wp_logln [interface.mkOk go.string #(go!"Resetting successor")]
      · iapply argOks1; iapply argOk_string
      wp_apply wp_resetNeighbor cfg n a st γs nbM latM nbrs (W64 1) $$ [$Hpkg $Hf $Hnbm $Hnbrs]
        as ⟨Hnbm, #Hnbrs'⟩
      iapply HΦ $$ [Hh Ht Hnbm Hlatm HS Htail] []
      · iexists _, lat, S
        isplitl [Hh Ht Hnbm Hlatm HS Htail]
        · unfold lockedState; iframe; iframe #; ipureintro; exact HlatS
        ipureintro
        intro _
        unfold nextAddr
        rw [nbrAt_insert_eq]
      ileft; ipureintro; rfl
    · -- a new successor
      wp_log [interface.mkOk go.string #addr]
      · iapply argOks1; iapply argOk_string
      have haddr' : addr ∈ cfg.chain := by
        rcases List.mem_cons.1 haddr with h' | h'
        · exact absurd h' Hif
        · exact h'
      wp_apply wp_connectToNode cfg n a st γs nbM latM nbrs addr (W64 1) (by simp)
        $$ [$Hpkg $Hf $Hnbm $Hnbrs] as %err Hres
      · ipureintro; exact haddr'
      icases Hres with (⟨%Herr, %c, Hnbm, #Hnbrs', #Hc⟩ | ⟨#Herr, Hnbm, -⟩)
      · subst Herr
        wp_auto
        wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
        iapply fupd_wp
        imod (HL.covers_nil cfg.γ addr) with #Hcov
        imodintro
        wp_apply (Hback cfg n a st γs nbM latM h t _ lat S c addr [])
          $$ [Hh Ht Hnbm Hlatm HS Htail] as %err ⟨%lat', %S', Hls, -, %Hcv⟩ Hres
        · iframe; iframe #
          unfold lockedState; iframe; iframe #; ipureintro; exact HlatS
        iapply HΦ $$ [Hls] [Hres]
        · iexists _, lat', S'
          iframe
          ipureintro
          intro _
          unfold nextAddr
          rw [nbrAt_insert_eq]
        iexact Hres
      · ihave %Hok := errAny_ok err $$ Herr
        obtain ⟨ei, rfl⟩ := Hok
        wp_auto
        iapply HΦ $$ [Hh Ht Hnbm Hlatm HS Htail] []
        · iexists nbrs, lat, S
          isplitl [Hh Ht Hnbm Hlatm HS Htail]
          · unfold lockedState; iframe; iframe #; ipureintro; exact HlatS
          ipureintro
          intro h; cases h
        iright; iexact Herr

end connps

end NodeP

end github_com.despreston.go_craq

end Perennial
