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

section startp
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [π : NetProtoGS]

instance itemPtr_persistent_st' (p : Loc) (k : GoString) (v : w64) (x : GoString) :
    Persistent (itemPtr (hG := hG) p k v x) := by
  unfold itemPtr; infer_instance

theorem wp_backfillLatest (HL : Laws (GF := GF)) (cfg : Cfg GF) (n : Loc) (a : GoString)
    (st : GoInterface) (γs : GName) (nbM latM : Loc) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗
        nodeFields cfg n a st γs nbM latM) -∗ Φ #interface.nil -∗
      WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"backfillLatest" #n)) (Val #()))
        {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hf⟩ HΦ
  unfold nodeFields
  icases Hf with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  ihave #Hstore' := Hstore
  iunfold isStore at Hstore'
  icases Hstore' with ⟨%e, %he, -⟩
  subst he
  wp_method_call
  wp_call
  wp_auto
  wp_apply (wp_with_defer) as %defer Hdefer
  wp_apply (wp_store_AllCommitted_inv HL cfg a γs e) $$ [$Hstore $Hinv] as %sl %S0 %L0 Hsl #Hcov %HL0
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] with ⟨Hlocked, Hlk⟩
  unfold lockInv
  icases Hlk with ⟨%h, %t, %nbrs, %lat, %S, Hls, Hrole⟩
  unfold lockedState
  icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs, HS, %HlatS, Htail⟩
  -- the snapshot's committed versions are below the latest map
  iapply fupd_wp
  iinv Hinv with Hi Hclose
  unfold nodeInv
  imod Hi with ⟨%S', %Ln, HS', Hln, %HLn, #Hfi⟩
  unfold storeOwn
  ihave %Heq := ghostVar_agree γs S _ S' _ $$ HS HS'
  subst Heq
  ihave %Hle := HL.nlog_covers_le cfg.γ a Ln L0 $$ [Hln Hcov]
  · iframe Hln Hcov
  imod Hclose $$ [HS' Hln] with -
  · inext; iexists S, Ln; iframe; iframe #; ipureintro; exact HLn
  imodintro
  have Hbound : ∀ k, uint.Z (S0.maxCommitted k) ≤ uint.Z (latOf lat k) := by
    intro k; rw [HlatS k, ← HLn k, ← HL0 k]; exact Hle k
  unfold itemsIn
  icases Hsl with ⟨%ps, %es, Hsl, %Hes, #Hps⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (j : w64) (it : Loc),
      "i" ∷ i_ptr ↦ j ∗ "item" ∷ item_ptr ↦ it ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (ps.length : Int)⌝) $$ [i item]
  · iexists _, _
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z j).toNat < ps.length := by word
    obtain ⟨p, Hp⟩ : ∃ p, ps[(sint.Z j).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨Hj.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z j) ps (DFrac.own 1) p Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hp
    ihave #Hip := BI.BigSepL.bigSepL_lookup (Φ := fun i p => iprop(∃ e, ⌜es[i]? = some e⌝ ∗
        itemPtr (hG := hG) p e.1 e.2.1 e.2.2.1)) Hp $$ Hps
    icases Hip with ⟨%ent, %Hent, #Hip⟩
    unfold itemPtr
    icases Hip with ⟨#Hk, #Hv, -⟩
    wp_auto
    wp_apply wp_map_lookup1 $$ Hlatm with Hlatm
    wp_if_destruct
    · exfalso
      have hmem : ent ∈ es := List.mem_of_getElem? Hent
      obtain ⟨hi, hc⟩ := Hes.2 ent hmem
      have hub := StoreS.maxCommitted_ub S0 ent.1 ent.2.2.1 ent.2.1
        (by have := (StoreS.mem_items S0 ent.1 _).1 hi; rw [hc] at this; exact this)
      have := Hbound ent.1
      unfold latOf at this
      have h0 : (zero_val w64 : w64) = W64 0 := rfl
      rw [h0] at Hif; omega
    · wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      exact ⟨by word, by word⟩
  · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hh Ht Hnbm Hlatm HS Htail Hrole]
    · inext
      iexists h, t, nbrs, lat, S
      iframe; iframe #
      ipureintro; exact HlatS
    iexact HΦ

theorem wp_connectToCoordinator (cfg : Cfg GF) (n : Loc) (a : GoString)
    (st : GoInterface) (γs : GName) (nbM latM : Loc) (cc : GoInterface) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗
        nodeFields cfg n a st γs nbM latM ∗ ⌜a ∈ cfg.chain⌝ ∗
        structFieldRef node.Node go!"cdr" n ↦□ cc ∗ freshCoordClient cfg cc ∗ joinTicket cfg.γ a) -∗
      (∀ err : GoInterface, (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"connectToCoordinator" #n))
        (Val #())) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hf, %Ha, #Hcdr, Hcc, Htok⟩ HΦ
  unfold nodeFields
  icases Hf with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  wp_method_call
  wp_call
  unfold freshCoordClient
  icases Hcc with ⟨%ec, %Hec, Hconn⟩
  subst Hec
  wp_auto
  wp_apply Hconn as %err Herr
  icases Herr with (⟨%Herr, #Hcl⟩ | #Herr)
  · subst Herr
    wp_auto
    wp_log [interface.mkOk go.string #cfg.cAddr]
    · iapply argOks1; iapply argOk_string
    unfold isCoordClient
    icases Hcl with ⟨%ec', %Hec', #Hcs⟩
    cases Hec'
    icases Hcs with ⟨Hadd, -⟩
    wp_apply Hadd $$ %a [] Htok as %p %err Herr
    · ipureintro; exact Ha
    icases Herr with (%Herr | #Herr)
    · subst Herr
      wp_auto
      iapply HΦ; ileft; ipureintro; rfl
    · ihave #Herr' := Herr
      unfold models_lab.errAny
      icases Herr' with ⟨%ei, %Hei, %Hty, #HE⟩
      subst Hei
      wp_auto
      wp_apply HE
      iintro %msg
      wp_auto
      wp_logln [interface.mkOk go.string #msg]
      · iapply argOks1; iapply argOk_string
      iapply HΦ; iright; iexact Herr
  · ihave %Hok := errAny_ok err $$ Herr
    obtain ⟨ei, rfl⟩ := Hok
    wp_auto
    wp_logln [interface.mkOk go.string #(go!"Error connecting to the coordinator")]
    · iapply argOks1; iapply argOk_string
    iapply HΦ; iright; iexact Herr

end startp

end NodeP

open NodeP

section startspec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [π : NetProtoGS]

theorem node.wp_Start (HL : NodeP.Laws (GF := GF)) : node.wp_Start.spec (GF := GF) (hG := hG) := by
  intro cfg n a
  wp_start_folded as ⟨#Hn, Hsr, Htok⟩
  unfold isNode NodeP.isNodeDef
  icases Hn with ⟨#Hctx, %Ha, -, %st, %γs, %nbM, %latM, #Hf⟩
  unfold nodeStartRes NodeP.startResDef
  icases Hsr with ⟨-, -, %cc, #Hcdr, Hcc⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply (NodeP.wp_backfillLatest HL cfg n a st γs nbM latM) $$ [$Hpkg $Hf]
  wp_apply (NodeP.wp_connectToCoordinator cfg n a st γs nbM latM cc) $$ [$Hpkg $Hf $Hcdr $Hcc $Htok]
  · ipureintro; exact Ha
  iintro %err Herr
  icases Herr with (%Herr | #Herr)
  · subst Herr
    wp_auto
    iapply HΦ; itrivial
  · ihave %Hok := NodeP.errAny_ok err $$ Herr
    obtain ⟨ei, rfl⟩ := Hok
    ihave #Hf' := Hf
    unfold NodeP.nodeFields
    icases Hf' with ⟨%f, %lg, %ch, -, -, -, -, -, -, -, #Hlog, -, %Hch, -⟩
    wp_auto
    wp_log [GoInterface.ok ei]
    · iapply NodeP.argOks1; iapply NodeP.argOk_err $$ Herr
    iapply HΦ; itrivial

end startspec

end github_com.despreston.go_craq

end Perennial
