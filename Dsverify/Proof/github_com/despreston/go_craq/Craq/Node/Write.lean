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

section write
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- A neighbors map entry (or the zero neighbor) is a valid neighbor. -/
theorem nbrOk_lookup (cfg : Cfg GF) (nbrs : GMap w64 node.neighbor) (p : w64) :
    ([∗map] _p ↦ nb ∈ nbrs, nbrOk cfg nb) ⊢ nbrOk cfg ((nbrs !! p).getD (zero_val node.neighbor)) := by
  cases h : nbrs !! p with
  | none =>
    iintro -
    unfold nbrOk
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  | some nb =>
    exact BI.BigSepM.bigSepM_lookup (Φ := fun _ nb => nbrOk (hG := hG) cfg nb) h

/-- `errors.New(msg)` for a non-empty message: an error with a non-empty message. -/
theorem wp_errorsNew_NE (msg : GoString) (h : msg ≠ []) :
    ⊢ ∀ Φ : val → IProp GF, (∀ err : GoInterface, errNE err -∗ Φ #err) -∗
      WP (App (Val (@! errors.New)) (Val #msg)) {{ Φ }} := by
  iintro %Φ HΦ
  wp_apply errors.wp_New_errorString as %x ⟨-, #Hx⟩
  iapply HΦ
  unfold errNE
  iexists msg
  isplitr
  · ipureintro; exact h
  unfold net.rpc.errMsg
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact errorString_isError
  iexact Hx

theorem wp_sendCommitToPrev (cfg : Cfg GF) (n : Loc) (lg : Loc) (hlg : lg ≠ null)
    (prev : node.neighbor) (k : GoString) (v : w64) (hk : keyOk k) :
    ⊢ ∀ Φ : val → IProp GF,
      isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node -∗
      structFieldRef node.Node go!"log" n ↦□ lg -∗ nbrOk cfg prev -∗ cvLb cfg.γ k v -∗
      (∀ err : GoInterface, (⌜err = interface.nil⌝ ∨ errNE err) -∗ Φ #err) -∗
      WP (App (App (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"sendCommitToPrev" #n))
        (Val #prev)) (Val #k)) (Val #v)) {{ Φ }} := by
  iintro %Φ #Hpkg #Hlog #Hnb #Hcv HΦ
  wp_method_call
  wp_call
  obtain ⟨rpc, addr⟩ := prev
  unfold nbrOk
  icases Hnb with (%Hnil | #Hc)
  · obtain ⟨h1, -⟩ := Hnil
    simp only at h1
    subst h1
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  · unfold isNodeClient
    icases Hc with ⟨%e, ⟨%He, %Ha⟩, #Hspec⟩
    simp only at He
    subst He
    icases Hspec with ⟨-, -, HC, -⟩
    wp_auto
    wp_apply HC $$ %hk Hcv
    iintro %err Herr
    icases Herr with (%Herr | #Herr)
    · subst Herr
      wp_auto
      iapply HΦ; ileft; ipureintro; rfl
    · ihave %Hok := errAny_ok err $$ Herr
      obtain ⟨ei, rfl⟩ := Hok
      wp_auto
      wp_log [GoInterface.ok ei]
      · iapply argOks1; iapply argOk_err $$ Herr
      unfold models_lab.errAny
      icases Herr with ⟨%ei', %Hei, %Hty, #HE⟩
      cases Hei
      wp_apply HE
      iintro %msg
      wp_auto
      wp_apply wp_errorsNew_NE _ (by simp)
      iintro %err' Herr'
      wp_auto
      iapply HΦ; iright; iexact Herr'

theorem hasVer_write (S : StoreS) (k x : GoString) (v : w64) : (S.write k x v).hasVer k v = true :=
  (StoreS.hasVer_iff _ k v).2 ⟨x, false, (StoreS.mem_write S k x v _).2 (Or.inr rfl)⟩

theorem wp_Write (HL : Laws (GF := GF)) (cfg : Cfg GF) (n : Loc) (a : GoString)
    (k : GoString) (sl : GoSlice) (x : GoString) (v : w64) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node -∗
      isNode cfg n a -∗ sl ↦*□ x -∗ valsElem cfg.γ v k x -∗
      ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∗ cvLb cfg.γ k v ∨ errNE err) -∗ Φ #err) -∗
      WP (App (App (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"Write" #n)) (Val #k))
        (Val #sl)) (Val #v)) {{ Φ }} := by
  iintro #Hpkg #Hn #Hsl #Hve HΦ
  unfold isNode isNodeDef
  icases Hn with ⟨#Hctx, %Ha, -, %st, %γs, %nbM, %latM, #Hfields⟩
  ihave #Hfields' := Hfields
  iunfold nodeFields at Hfields'
  icases Hfields' with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  ihave #Hstore' := Hstore
  iunfold isStore at Hstore'
  icases Hstore' with ⟨%e, %he, -⟩
  subst he
  wp_method_call
  wp_call
  wp_auto
  wp_log [interface.mkOk go.string #k, interface.mkOk go.uint64 #v]
  · iapply argOks2
    isplitr
    · iapply argOk_string
    · iapply argOk_u64
  wp_apply (lc := 1) sync.Mutex.wp_Lock $$ [$Hmu] with ⟨Hlocked, Hlk⟩
  iunfold lockInv at Hlk
  icases Hlk with ⟨%h, %t, %nbrs, %lat, %S, Hls, Hrole⟩
  iunfold lockedState at Hls
  icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs, HS, %HlatS, Htail⟩
  wp_apply (wp_store_Write cfg a γs e S k sl x v) $$ [$Hstore $Hinv $HS $Hsl $Hve] as HS
  cases t
  · -- not the tail: forward to the successor
    simp only [Bool.not_false]
    wp_auto
    wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
    ihave #Hnext := nbrOk_lookup cfg nbrs (W64 1) $$ Hnbrs
    wp_pures
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hh Ht Hnbm Hlatm HS Htail Hrole]
    · inext
      unfold lockInv lockedState
      iexists h, false, nbrs, lat, (S.write k x v)
      iframe; iframe #
      ipureintro
      intro k'; rw [StoreS.maxCommitted_write]; exact HlatS k'
    generalize (nbrs !! W64 1).getD (zero_val node.neighbor) = nb at *
    obtain ⟨rpc, addr⟩ := nb
    unfold nbrOk
    icases Hnext with (%Hnil | #Hc)
    · obtain ⟨h1, -⟩ := Hnil
      simp only at h1
      subst h1
      wp_auto
      ihave ⟨#HnoSucc, -, -, -⟩ := node_vars $$ Hpkg
      ihave ⟨%err, #He, #HeMsg, -⟩ := newVar_errMsg' $$ HnoSucc
      wp_auto
      iapply HΦ; iright
      iapply errNE_of_errMsg $$ HeMsg
      decide
    · unfold isNodeClient
      icases Hc with ⟨%ec, ⟨%He, %Ha'⟩, #Hspec⟩
      simp only at He
      subst He
      icases Hspec with ⟨-, HW, -⟩
      wp_auto
      wp_apply HW $$ Hsl Hve
      iintro %err Herr
      icases Herr with (⟨%Herr, #Hcv⟩ | #Herr)
      · subst Herr
        wp_auto
        iapply HΦ; ileft; iframe Hcv; ipureintro; rfl
      · ihave %Hok := errAny_ok err $$ Herr
        obtain ⟨ei, rfl⟩ := Hok
        wp_auto
        wp_log [GoInterface.ok ei]
        · iapply argOks1; iapply argOk_err $$ Herr
        unfold models_lab.errAny
        icases Herr with ⟨%ei', %Hei, %Hty, #HE⟩
        cases Hei
        wp_apply HE
        iintro %msg
        wp_auto
        wp_apply wp_errorsNew_NE _ (by simp)
        iintro %err' Herr'
        wp_auto
        iapply HΦ; iright; iexact Herr'
  · simp only [Bool.not_true]
    wp_auto
    wp_apply (wp_commitM HL cfg n a (interface.ok e) γs nbM latM h true nbrs lat (S.write k x v) k v)
      $$ [Hh Ht Hnbm Hlatm HS Htail Hlc1]
    · iframe Hctx Hfields
      unfold lockedState
      iframe; iframe #
      isplitr
      · ipureintro; intro k'; rw [StoreS.maxCommitted_write]; exact HlatS k'
      iright; iframe; ipureintro; rfl
    iintro %err Hres
    rw [hasVer_write]
    simp only [↓reduceIte]
    icases Hres with ⟨%Herr, %Hko, #Hcv, Hls⟩
    subst Herr
    unfold lockedState
    icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs', HS, %HlatS', Htail⟩
    wp_auto
    wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
    ihave #Hprev := nbrOk_lookup cfg nbrs (W64 0) $$ Hnbrs
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hh Ht Hnbm Hlatm HS Htail Hrole]
    · inext
      unfold lockInv lockedState
      iexists h, true, nbrs, _, _
      iframe; iframe #
      ipureintro; exact HlatS'
    wp_apply wp_sendCommitToPrev (hlg := Hch.2) (hk := Hko) $$ Hpkg Hlog Hprev Hcv
    iintro %err -
    wp_auto
    iapply HΦ; ileft; iframe Hcv; ipureintro; rfl

/-- `n.commitAndSend(k, v)` of a committed version. -/
theorem wp_commitAndSend (HL : Laws (GF := GF)) (cfg : Cfg GF) (n : Loc) (a : GoString)
    (k : GoString) (v : w64) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node -∗
      isNode cfg n a -∗ cvLb cfg.γ k v -∗
      (∀ err : GoInterface, (⌜err = interface.nil⌝ ∨ errNE err) -∗ Φ #err) -∗
      WP (App (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"commitAndSend" #n))
        (Val #k)) (Val #v)) {{ Φ }} := by
  iintro #Hpkg #Hn #Hcv HΦ
  unfold isNode isNodeDef
  icases Hn with ⟨#Hctx, %Ha, -, %st, %γs, %nbM, %latM, #Hfields⟩
  ihave #Hfields' := Hfields
  iunfold nodeFields at Hfields'
  icases Hfields' with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] with ⟨Hlocked, Hlk⟩
  iunfold lockInv at Hlk
  icases Hlk with ⟨%h, %t, %nbrs, %lat, %S, Hls, Hrole⟩
  wp_apply (wp_commitM HL cfg n a st γs nbM latM h t nbrs lat S k v) $$ [Hls]
  · iframe Hctx Hfields Hls
    ileft; iexact Hcv
  iintro %err Hres
  cases hv : S.hasVer k v
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hres with ⟨#Herr, Hls⟩
    ihave #Hem := errNotFound_errMsg err $$ Herr
    ihave %Hok := errMsg_ok err _ $$ Hem
    obtain ⟨ei, rfl⟩ := Hok
    iunfold lockedState at Hls
    icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs, HS, %HlatS, Htail⟩
    wp_auto
    wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hh Ht Hnbm Hlatm HS Htail Hrole]
    · inext
      unfold lockInv lockedState
      iexists h, t, nbrs, lat, S
      iframe; iframe #
      ipureintro; exact HlatS
    iapply HΦ; iright
    iapply errNE_of_errMsg $$ Hem
    decide
  · simp only [↓reduceIte]
    icases Hres with ⟨%Herr, %Hko, #Hcv', Hls⟩
    subst Herr
    iunfold lockedState at Hls
    icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs, HS, %HlatS, Htail⟩
    wp_auto
    wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
    ihave #Hprev := nbrOk_lookup cfg nbrs (W64 0) $$ Hnbrs
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hh Ht Hnbm Hlatm HS Htail Hrole]
    · inext
      unfold lockInv lockedState
      iexists h, t, nbrs, _, _
      iframe; iframe #
      ipureintro; exact HlatS
    wp_if_destruct
    · iapply HΦ; ileft; ipureintro; rfl
    · wp_apply wp_sendCommitToPrev (hlg := Hch.2) (hk := Hko) $$ Hpkg Hlog Hprev Hcv
      iintro %err Herr
      wp_auto
      iapply HΦ $$ Herr

theorem wp_Commit (HL : Laws (GF := GF)) (cfg : Cfg GF) (n : Loc) (a : GoString)
    (k : GoString) (v : w64) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node -∗
      isNode cfg n a -∗ cvLb cfg.γ k v -∗
      ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∨ errNE err) -∗ Φ #err) -∗
      WP (App (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"Commit" #n)) (Val #k))
        (Val #v)) {{ Φ }} := by
  iintro #Hpkg #Hn #Hcv HΦ
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_commitAndSend HL cfg n a k v $$ Hpkg Hn Hcv
  iintro %err Herr
  wp_auto
  iapply HΦ $$ Herr

end write

end NodeP

end github_com.despreston.go_craq

end Perennial
