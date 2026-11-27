module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Common

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions] [LogSpecs GF]
variable [net.rpc.Assumptions] [π : NetProtoGS]

theorem wp_LatestVersion (Hread : read.spec (GF := GF)) (cfg : Cfg GF) (n : Loc) (a : GoString)
    (k : GoString) (Q : KvM.Output → IProp GF) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node -∗
      isNode cfg n a -∗ opAU cfg.γ (.get k) Q -∗
      ▷ (∀ (k' : GoString) (v : w64) (err : GoInterface),
          ((⌜err = interface.nil ∧ k' = k⌝ ∗ ∃ σ : KvM.State, Q (.got (σ k)) ∗
              readFacts cfg.γ k v (σ k)) ∨ errNE err) -∗
          Φ (PairV (PairV #k' #v) #err)) -∗
      WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"LatestVersion" #n)) (Val #k))
        {{ Φ }} := by
  iintro #Hpkg #Hn Hau HΦ
  unfold isNode isNodeDef nodeFields
  icases Hn with ⟨#Hctx, %Ha, -, %st, %γs, %nbM, %latM, %f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac,
    #Haddr, #Hpub, #Hcdra, #Hlog, #Hch, %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply (lc := 1) wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] with ⟨Hlocked, Hlk⟩
  unfold lockInv
  icases Hlk with ⟨%h, %t, %nbrs, %lat, %S, Hls, Hrole⟩
  unfold lockedState
  icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs, HS, %HlatS, Htail⟩
  wp_auto
  cases t
  · -- not the tail
    ihave ⟨-, -, #HnotTail, -⟩ := node_vars $$ Hpkg
    ihave ⟨%e, #He, #HeMsg, -⟩ := newVar_errMsg' $$ HnotTail
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hh Ht Hnbm Hlatm HS Htail Hrole]
    · inext
      iexists h, false, nbrs, lat, S
      iframe; iframe #
      ipureintro; exact HlatS
    iapply HΦ
    iright
    iapply errNE_of_errMsg $$ HeMsg
    decide
  · -- the tail: the read law
    unfold tailRes
    simp only [↓reduceIte]
    icases Htail with ⟨%L, HL, %HL⟩
    ihave #Hcraq : isCraq cfg.γ $$ [Hctx]
    · unfold craqCtx; icases Hctx with ⟨#H, -⟩; iexact H
    iapply fupd_wp
    imod (Hread cfg.γ ⊤ (by simp) L k Q) $$ [Hcraq HL Hau Hlc1] with ⟨HL, %σ, HQ, #Hrf⟩
    · iframe; iframe #
    imodintro
    wp_auto
    wp_apply wp_map_lookup1 $$ Hlatm with Hlatm
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hh Ht Hnbm Hlatm HS HL Hrole]
    · inext
      iexists h, true, nbrs, lat, S
      iframe; iframe #
      isplitr
      · ipureintro; exact HlatS
      simp only [↓reduceIte]
      iexists L; iframe
      ipureintro; exact HL
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists σ
    iframe HQ
    have hv : (lat !! k).getD (zero_val w64) = cvOf L k := HL k
    rw [hv]
    iexact Hrf

end proofs

end NodeP

end github_com.despreston.go_craq

end Perennial
