/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/snapstore/Sink__Close.lean (241f27e).
-/
/-
The proof of `snapstore.Sink.Close`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Sink__Close
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.snapstore

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.snapstore.Sink.Close.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.snapstore.Sink.Close.spec (GF := GF) (hG := hG) :=
  fun k st γ eof id ver idx term cfgIdx cfg o R => by
  wp_start as ⟨#Hcore, Hst, Hc⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  cases o with
  | none =>
    simp only [sinkSt]
    wp_auto
    wp_end
  | some bs =>
    simp only [sinkSt]
    icases Hst with ⟨%sdsl, Hdata, Hsl, Hcap, Hclosed, Hsize⟩
    iNamed Hcore
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    have Hsz : sdsl.len = W64 (bs.length : Int) := by word
    rw [Hsz]
    ipersist Hsize
    ihave #Hmeta : (k.[Sink, go!"meta"] ↦□ sinkMeta ver idx term cfgIdx cfg id bs) $$ []
    · iapply typedPointsto_combine _ _ _ Hmnn
      simp only [TypedPointsto.typedPointstoDef, sinkMeta]
      iframe #
    iNamed Hstore
    wp_auto
    wp_apply (lc := 1) wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
    iNamed HR
    wp_auto
    -- the commit (the linearization point): the latest becomes `newerSnap o m bs`
    iapply wp_ncfupd _ _ rfl
    iintro Hnc
    imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤) (E2 := ⊤ \ ↑storeN) (by solve_ndisj)) with Hmask
    unfold sinkCommit
    imod Hc $$ Hnc with ⟨Hnc, HAU⟩
    imod lc_fupd_elim_later (E := ∅) $$ Hlc1 HAU with ⟨%old, Hown, Hclose⟩
    unfold ownLatest
    ihave %Heq := ghostVar_agree _ _ _ _ _ $$ Hown Hg
    subst Heq
    imod ghostVar_update_halves (newerSnap old (sinkMeta ver idx term cfgIdx cfg id bs) bs) γ _ _
      $$ Hown Hg with ⟨Hown, Hg⟩
    imod Hclose $$ Hown with HR
    imod Hmask with -
    imodintro
    iframe Hnc
    ipersist Hsl
    cases old with
    | none =>
      simp only [latestCell]
      icases Hcell with %Hhas
      subst Hhas
      wp_auto
      wp_apply wp_Unlock $$ [$Hmu $Hlocked Hg Hhas Hmt Hdat Hnid]
      · inext
        unfold storeLocked ownLatest
        iexists (newerSnap none (sinkMeta ver idx term cfgIdx cfg id bs) bs), true,
          sinkMeta ver idx term cfgIdx cfg id bs, sdsl, nid
        iframe
        simp only [newerSnap, latestCell]
        isplitr
        · ipureintro; simp
        iexact Hsl
      iapply HΦ; iframe
    | some p =>
      obtain ⟨m0, b0⟩ := p
      simp only [latestCell]
      icases Hcell with ⟨⟨%Hhas, %Hmt⟩, #Hb0⟩
      subst Hhas Hmt
      wp_auto
      wp_if_destruct
      · rw [newerSnap_upd _ _ _ _ (by simp only [sinkMeta]; left; exact Hif)]
        wp_apply wp_Unlock $$ [$Hmu $Hlocked Hg Hhas Hmt Hdat Hnid]
        · inext
          unfold storeLocked ownLatest
          iexists (some (sinkMeta ver idx term cfgIdx cfg id bs, bs)), true,
            sinkMeta ver idx term cfgIdx cfg id bs, sdsl, nid
          iframe
          simp only [latestCell]
          isplitr
          · ipureintro; simp
          iexact Hsl
        iapply HΦ; iframe
      wp_if_destruct
      · wp_if_destruct
        · rw [newerSnap_upd _ _ _ _ (by simp only [sinkMeta]; right; simp [Hif])]
          wp_apply wp_Unlock $$ [$Hmu $Hlocked Hg Hhas Hmt Hdat Hnid]
          · inext
            unfold storeLocked ownLatest
            iexists (some (sinkMeta ver idx mt.Term' cfgIdx cfg id bs, bs)), true,
              sinkMeta ver idx mt.Term' cfgIdx cfg id bs, sdsl, nid
            iframe
            simp only [latestCell]
            isplitr
            · ipureintro; simp
            iexact Hsl
          iapply HΦ; iframe
        · rw [newerSnap_keep _ _ _ _ (by simp only [sinkMeta]; rintro (h | ⟨-, h⟩) <;> omega)]
          wp_apply wp_Unlock $$ [$Hmu $Hlocked Hg Hhas Hmt Hdat Hnid]
          · inext
            unfold storeLocked ownLatest
            iexists (some (mt, b0)), true, mt, dsl, nid
            iframe
            simp only [latestCell]
            isplitr
            · ipureintro; simp
            iexact Hb0
          iapply HΦ; iframe
      · rw [newerSnap_keep _ _ _ _ (by simp only [sinkMeta]; rintro (h | ⟨h, -⟩); exact absurd h (by assumption); exact absurd h.symm (by assumption))]
        wp_apply wp_Unlock $$ [$Hmu $Hlocked Hg Hhas Hmt Hdat Hnid]
        · inext
          unfold storeLocked ownLatest
          iexists (some (mt, b0)), true, mt, dsl, nid
          iframe
          simp only [latestCell]
          isplitr
          · ipureintro; simp
          iexact Hb0
        iapply HΦ; iframe

end proof

end Perennial
