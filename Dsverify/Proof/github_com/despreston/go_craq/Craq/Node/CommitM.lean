module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Common
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Store
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Log

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

section commitm
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogSpecs GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- The latest map after committing `v` of `k`. -/
def bumpLat (lat : GMap GoString w64) (k : GoString) (v : w64) : GMap GoString w64 :=
  if uint.Z (latOf lat k) < uint.Z v then lat.insert k v else lat

theorem latOf_bumpLat (lat : GMap GoString w64) (k : GoString) (v : w64) (k' : GoString) :
    latOf (bumpLat lat k v) k' =
      if k' = k ∧ uint.Z (latOf lat k) < uint.Z v then v else latOf lat k' := by
  unfold bumpLat
  split
  · rename_i h
    by_cases hk : k' = k
    · subst hk
      rw [if_pos ⟨rfl, h⟩]
      unfold latOf
      rw [GMap.lookup_insert_eq]; rfl
    · rw [if_neg (fun hh => hk hh.1)]
      unfold latOf
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]
  · rename_i h
    rw [if_neg (fun hh => h hh.2)]

theorem nodeN_disj : ↑craqN ∪ clientMask ⊆ (⊤ \ ↑nodeN : CoPset) := by
  intro p hp
  refine LawfulSet.mem_diff.2 ⟨CoPset.mem_full, fun hn => ?_⟩
  rcases LawfulSet.mem_union.1 hp with h | h
  · exact (ndot_ne_disjoint nroot (by decide : ("craq" : String) ≠ "craq_node")) p ⟨h, hn⟩
  · unfold clientMask craqEop at h
    exact (LawfulSet.mem_diff.1 h).2 (LawfulSet.mem_union.2 (Or.inr hn))

/-- The ghost side of a commit of `v` of `k` (a version the store has): the commit's `cvLb`, and
the tail token follows the latest map (by the commit law at the active tail). -/
theorem commit_shift (HL : Laws (GF := GF)) (cfg : Cfg GF) (t : Bool) (lat : GMap GoString w64)
    (k : GoString) (v : w64) (x : GoString) :
    ⊢ isCraq cfg.γ -∗ valsElem cfg.γ v k x -∗
      ((cvLb cfg.γ k v ∨ ⌜t = true⌝ ∗ £ 1) ∗ tailRes cfg t lat) ={⊤ \ ↑nodeN}=∗
        cvLb cfg.γ k v ∗ tailRes cfg t (bumpLat lat k v) := by
  iintro #Hcraq #Hve ⟨Hmode, Htail⟩
  icases Hmode with (#Hcv | ⟨%Ht, Hlc⟩)
  · cases t
    · imodintro
      isplitr
      · iexact Hcv
      unfold tailRes; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    · unfold tailRes
      simp only [↓reduceIte]
      icases Htail with ⟨%L, HL', %HlatL⟩
      ihave %Hle := HL.tailTok_cvLb cfg.γ L k v $$ [HL' Hcv]
      · iframe HL' Hcv
      have hb : bumpLat lat k v = lat := by
        unfold bumpLat; rw [if_neg]; rw [HlatL k]; omega
      rw [hb]
      imodintro
      isplitr
      · iexact Hcv
      iexists L; iframe
      ipureintro; exact HlatL
  · subst Ht
    unfold tailRes
    simp only [↓reduceIte]
    icases Htail with ⟨%L, HL', %HlatL⟩
    imod (HL.commit cfg.γ (⊤ \ ↑nodeN) nodeN_disj L v k x) $$ [Hcraq HL' Hve Hlc] with HL'
    · iframe; iframe #
    ihave ⟨HL', #Hlb⟩ := HL.tailTok_lb cfg.γ _ k $$ HL'
    have hc := HL.cvOf_commit L k k v
    simp only [_root_.true_and] at hc
    ihave #Hcv := HL.cvLb_mono cfg.γ k _ v (by rw [hc]; split <;> omega) $$ Hlb
    imodintro
    isplitr
    · iexact Hcv
    iexists _
    iframe HL'
    ipureintro
    intro k'
    rw [latOf_bumpLat, HL.cvOf_commit, HlatL k, HlatL k']

theorem wp_commitM (HL : Laws (GF := GF)) (cfg : Cfg GF) (n : Loc) (a : GoString) (st : GoInterface)
    (γs : GName) (nbM latM : Loc) (h t : Bool) (nbrs : GMap w64 node.neighbor)
    (lat : GMap GoString w64) (S : StoreS) (k : GoString) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ craqCtx cfg ∗
        nodeFields cfg n a st γs nbM latM ∗ lockedState cfg γs n nbM latM h t nbrs lat S ∗
        (cvLb cfg.γ k v ∨ ⌜t = true⌝ ∗ £ 1)) -∗
      (∀ err : GoInterface,
        (if S.hasVer k v then
          iprop(⌜err = interface.nil⌝ ∗ ⌜keyOk k⌝ ∗ cvLb cfg.γ k v ∗
            lockedState cfg γs n nbM latM h t nbrs (bumpLat lat k v) (S.commit k v))
        else iprop(errNotFound err ∗ lockedState cfg γs n nbM latM h t nbrs lat S)) -∗
        Φ #err) -∗
      WP (App (App (Val #(methods (go.GoType.PointerType node.Node.ty)
        go!"commit" #n)) (Val #k)) (Val #v)) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hctx, #Hf, Hls, Hmode⟩ HΦ
  unfold nodeFields
  icases Hf with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  unfold lockedState
  icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs, HS, %HlatS, Htail⟩
  ihave #Hstore' := Hstore
  iunfold isStore at Hstore'
  icases Hstore' with ⟨%e, %he, -⟩
  subst he
  ihave #Hcraq : isCraq cfg.γ $$ [Hctx]
  · unfold craqCtx; icases Hctx with ⟨#H, -⟩; iexact H
  wp_method_call
  wp_call
  wp_auto
  wp_apply (wp_store_Commit HL cfg a γs e S k v
    iprop((cvLb cfg.γ k v ∨ ⌜t = true⌝ ∗ £ 1) ∗ tailRes cfg t lat)
    (tailRes cfg t (bumpLat lat k v))) $$ [$Hstore $Hinv $HS Hmode Htail]
  · iframe
    iintro %x %c %hmem #Hve HP
    iapply commit_shift HL cfg t lat k v x $$ Hcraq Hve HP
  iintro %err Hres
  cases hv : S.hasVer k v
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hres with ⟨#Herr, HS, Hmode, Htail⟩
    ihave #Hem := errNotFound_errMsg err $$ Herr
    ihave %Hok := errMsg_ok err _ $$ Hem
    obtain ⟨ei, rfl⟩ := Hok
    wp_auto
    wp_log [interface.mkOk go.string #k, interface.mkOk go.uint64 #v, GoInterface.ok ei]
    · iapply argOks3
      isplitr; · iapply argOk_string
      isplitr; · iapply argOk_u64
      iapply argOk_err
      iapply errMsg_errAny $$ Hem
    iapply HΦ
    iframe; iframe #
    ipureintro; exact HlatS
  · simp only [↓reduceIte]
    icases Hres with ⟨%Herr, %Hko, HS, #Hcv, Htail⟩
    subst Herr
    wp_auto
    wp_apply wp_map_lookup1 $$ Hlatm with Hlatm
    obtain ⟨Hch, -⟩ := Hch
    subst Hch
    wp_if_destruct
    · wp_apply wp_mapInsert $$ Hlatm with Hlatm
      iapply HΦ
      simp only [↓reduceIte]
      isplitr; · ipureintro; trivial
      isplitr; · ipureintro; exact Hko
      have hb : bumpLat lat k v = lat.insert k v := by
        unfold bumpLat; rw [if_pos]; exact Hif
      rw [hb]
      iframe; iframe #
      ipureintro
      intro k'
      rw [← hb, latOf_bumpLat, StoreS.maxCommitted_commit S k v hv, HlatS k, HlatS k']
    · iapply HΦ
      simp only [↓reduceIte]
      isplitr; · ipureintro; trivial
      isplitr; · ipureintro; exact Hko
      have hb : bumpLat lat k v = lat := by
        unfold bumpLat; rw [if_neg]; exact Hif
      rw [hb]
      iframe; iframe #
      ipureintro
      intro k'
      rw [← hb, latOf_bumpLat, StoreS.maxCommitted_commit S k v hv, HlatS k, HlatS k']

end commitm

end NodeP

end github_com.despreston.go_craq

end Perennial
