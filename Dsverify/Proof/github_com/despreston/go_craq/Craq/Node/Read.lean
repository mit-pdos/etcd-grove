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

section read
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogSpecs GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- An `errors.New(msg)` error has its message. -/
theorem newErr_errMsg' (x : Loc) (msg : GoString) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
        WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x))
          (Val #())) {{ Φ }}) ⊢
      net.rpc.errMsg (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) msg := by
  iintro #H
  unfold net.rpc.errMsg
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact errorString_isError
  iexact H

/-- A neighbors map entry (the zero neighbor if absent) is `nbrOk`. -/
theorem nbrOk_lookup_rd (cfg : Cfg GF) (nbrs : GMap w64 node.neighbor) (p : w64) :
    ([∗map] _p ↦ nb ∈ nbrs, nbrOk cfg nb) ⊢ nbrOk cfg ((nbrs !! p).getD (zero_val node.neighbor)) := by
  cases h : nbrs !! p with
  | none =>
    iintro -
    unfold nbrOk
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  | some nb =>
    iintro #H
    iapply (BI.BigSepM.bigSepM_lookup (Φ := fun _ nb => nbrOk (hG := hG) cfg nb) h) $$ H

theorem wp_Read (HL : Laws (GF := GF)) (cfg : Cfg GF) (n : Loc) (a : GoString)
    (k : GoString) (Q : KvM.Output → IProp GF) (Φ : val → IProp GF) (hk : keyOk k) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node -∗
      isNode cfg n a -∗ opAU cfg.γ (.get k) Q -∗
      ▷ (∀ (k' : GoString) (sl : GoSlice) (err : GoInterface),
          ((⌜err = interface.nil ∧ k' = k⌝ ∗ ∃ (x : GoString) (σ : KvM.State), sl ↦*□ x ∗
              Q (.got (σ k)) ∗ ⌜σ k = some x⌝) ∨
            (net.rpc.errMsg err notFoundMsg ∗ ∃ σ : KvM.State, Q (.got (σ k)) ∗
              ⌜σ k = none⌝) ∨
            (∃ msg, ⌜msg ≠ [] ∧ msg ≠ notFoundMsg⌝ ∗ net.rpc.errMsg err msg)) -∗
          Φ (PairV (PairV #k' #sl) #err)) -∗
      WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"Read" #n)) (Val #k)) {{ Φ }} := by
  iintro #Hpkg #Hn Hau HΦ
  unfold isNode isNodeDef nodeFields
  icases Hn with ⟨#Hctx, %Ha, -, %st, %γs, %nbM, %latM, %f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac,
    #Haddr, #Hpub, #Hcdra, #Hlog, #Hch, %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  ihave #Hstore' := Hstore
  iunfold isStore at Hstore'
  icases Hstore' with ⟨%e, %he, -⟩
  subst he
  ihave #Hcraq : isCraq cfg.γ $$ [Hctx]
  · unfold craqCtx; icases Hctx with ⟨#H, -⟩; iexact H
  wp_method_call
  wp_call
  wp_auto_lc 1
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] with ⟨Hlocked, Hlk⟩
  unfold lockInv
  icases Hlk with ⟨%h, %t, %nbrs, %lat, %S, Hls, Hrole⟩
  unfold lockedState
  icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs, HS, %HlatS, Htail⟩
  cases t
  · wp_auto
    wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
    ihave #Hnt := nbrOk_lookup_rd cfg nbrs (W64 2) $$ Hnbrs
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hh Ht Hnbm Hlatm HS Htail Hrole]
    · inext
      iexists h, false, nbrs, lat, S
      iframe; iframe #
      ipureintro; exact HlatS
    generalize (nbrs !! W64 2).getD (zero_val node.neighbor) = tl at *
    unfold nbrOk
    icases Hnt with (%Hnil | #Hcl)
    · obtain ⟨Hr, -⟩ := Hnil
      cases tl
      simp only at Hr
      subst Hr
      ihave ⟨-, #HnoTail, -, -⟩ := node_vars $$ Hpkg
      ihave ⟨%e2, #He2, #He2Msg, -⟩ := newVar_errMsg' $$ HnoTail
      wp_auto
      iapply HΦ
      iright; iright
      iexists _
      iframe He2Msg
      ipureintro
      unfold notFoundMsg
      decide
    · obtain ⟨rpc, addr⟩ := tl
      simp only
      ihave #Hcl' := Hcl
      unfold isNodeClient
      icases Hcl' with ⟨%ec, ⟨%Hec, %Haddr⟩, #Hcs⟩
      subst Hec
      icases Hcs with ⟨-, -, -, HLV, -⟩
      wp_auto
      wp_apply HLV $$ %_ %_ %_ %hk Hau
      iintro %k' %v %err Hres
      icases Hres with (⟨%Herr, %σ, HQ, #Hrf⟩ | #Hea)
      · subst Herr
        wp_auto
        unfold readFacts
        icases Hrf with ⟨%Hz, #Hx⟩
        wp_if_destruct
        · wp_apply errors.wp_New_errorString as %x ⟨-, #Herr⟩
          iapply HΦ
          iright; ileft
          iframe
          isplitl []
          · unfold notFoundMsg; iapply newErr_errMsg' $$ Herr
          ipureintro
          exact Hz.1 rfl
        · wp_apply (wp_store_ReadVersion cfg a γs e k v) $$ [$Hstore $Hinv] as %p %err Hres
          icases Hres with (⟨%x, %Herr, Hp, #Hve⟩ | #Hnf)
          · subst Herr
            unfold itemPtr
            icases Hp with ⟨-, -, %vsl, #Hvsl, #Hxs⟩
            wp_auto
            have hsome : ∃ x', σ k = some x' := by
              cases hσ : σ k with
              | none => exact absurd (Hz.2 hσ) Hif
              | some x' => exact ⟨x', rfl⟩
            obtain ⟨x', hx'⟩ := hsome
            ihave #Hve' := Hx $$ %x' %hx'
            ihave %Hag := HL.valsElem_agree cfg.γ v k x k x' $$ [Hve Hve']
            · iframe Hve Hve'
            obtain ⟨-, rfl⟩ := Hag
            iapply HΦ
            ileft
            isplitr
            · ipureintro; exact ⟨rfl, rfl⟩
            iexists x, σ
            iframe; iframe #
            ipureintro; exact hx'
          · ihave #Hem := errNotFound_errMsg err $$ Hnf
            ihave %Hok := errMsg_ok err _ $$ Hem
            obtain ⟨ei, rfl⟩ := Hok
            wp_auto
            iapply HΦ
            iright; iright
            iexists _
            iframe Hem
            ipureintro
            unfold notFoundMsg
            decide
      · ihave %Hok := errAny_ok err $$ Hea
        obtain ⟨ei, rfl⟩ := Hok
        wp_auto
        wp_log [interface.mkOk go.string #k, GoInterface.ok ei]
        · iapply argOks2
          isplitr
          · iapply argOk_string
          iapply argOk_err $$ Hea
        ihave ⟨-, -, -, #Htv⟩ := node_vars $$ Hpkg
        ihave ⟨%e3, #He3, #He3Msg, -⟩ := newVar_errMsg' $$ Htv
        wp_auto
        iapply HΦ
        iright; iright
        iexists _
        iframe He3Msg
        ipureintro
        unfold notFoundMsg
        decide
  · unfold tailRes
    simp only [↓reduceIte]
    icases Htail with ⟨%L, HL', %HLL⟩
    iapply fupd_wp
    imod (HL.read cfg.γ ⊤ (by simp) L k Q) $$ [Hcraq HL' Hau Hlc1] with ⟨HL', %σ, HQ, #Hrf⟩
    · iframe; iframe #
    imodintro
    wp_auto
    wp_apply wp_map_lookup1 $$ Hlatm with Hlatm
    have hv : (lat !! k).getD (zero_val w64) = cvOf L k := HLL k
    rw [hv]
    unfold readFacts
    icases Hrf with ⟨%Hz, #Hx⟩
    wp_if_destruct
    · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hh Ht Hnbm Hlatm HS HL' Hrole]
      · inext
        iexists h, true, nbrs, lat, S
        iframe; iframe #
        isplitr
        · ipureintro; exact HlatS
        simp only [↓reduceIte]
        iexists L; iframe
        ipureintro; exact HLL
      wp_apply errors.wp_New_errorString as %x ⟨-, #Herr⟩
      iapply HΦ
      iright; ileft
      iframe
      isplitl []
      · unfold notFoundMsg; iapply newErr_errMsg' $$ Herr
      ipureintro
      exact Hz.1 Hif
    · wp_apply (wp_store_ReadVersion cfg a γs e k (cvOf L k)) $$ [$Hstore $Hinv] as %p %err Hres
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hh Ht Hnbm Hlatm HS HL' Hrole]
      · inext
        iexists h, true, nbrs, lat, S
        iframe; iframe #
        isplitr
        · ipureintro; exact HlatS
        simp only [↓reduceIte]
        iexists L; iframe
        ipureintro; exact HLL
      icases Hres with (⟨%x, %Herr, Hp, #Hve⟩ | #Hnf)
      · subst Herr
        unfold itemPtr
        icases Hp with ⟨-, -, %vsl, #Hvsl, #Hxs⟩
        wp_auto
        have hsome : ∃ x', σ k = some x' := by
          cases hσ : σ k with
          | none => exact absurd (Hz.2 hσ) Hif
          | some x' => exact ⟨x', rfl⟩
        obtain ⟨x', hx'⟩ := hsome
        ihave #Hve' := Hx $$ %x' %hx'
        ihave %Hag := HL.valsElem_agree cfg.γ (cvOf L k) k x k x' $$ [Hve Hve']
        · iframe Hve Hve'
        obtain ⟨-, rfl⟩ := Hag
        iapply HΦ
        ileft
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        iexists x, σ
        iframe; iframe #
        ipureintro; exact hx'
      · ihave #Hem := errNotFound_errMsg err $$ Hnf
        ihave %Hok := errMsg_ok err _ $$ Hem
        obtain ⟨ei, rfl⟩ := Hok
        wp_auto
        iapply HΦ
        iright; iright
        iexists _
        iframe Hem
        ipureintro
        unfold notFoundMsg
        decide

end read

end NodeP

end github_com.despreston.go_craq

end Perennial
