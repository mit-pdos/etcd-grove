/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/New.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

set_option linter.unusedSectionVars false

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

set_option goose.wp.extras true

/-- Per-element lists of `K` resources, as `K` lists over the elements. -/
theorem bigSepL_transpose {A : Type} (T : A → IProp GF) (l : List A) (K : Nat) :
    ([∗list] x ∈ l, [∗list] _y ∈ List.replicate K (), T x) ⊢
      [∗list] _y ∈ List.replicate K (), [∗list] x ∈ l, T x := by
  induction K with
  | zero =>
    iintro _
    simp only [List.replicate]
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | succ K ih =>
    iintro H
    simp only [List.replicate_succ]
    ihave H := (BigSepL.bigSepL_mono (Ψ := fun _ x => iprop(T x ∗
        [∗list] _y ∈ List.replicate K (), T x)) (fun _ => BigSepL.bigSepL_cons.1)) $$ H
    icases BigSepL.bigSepL_sep_eqv.1 $$ H with ⟨H1, H2⟩
    iapply BigSepL.bigSepL_cons.2
    iframe H1
    iapply ih $$ H2


theorem isShardV_intro (sh mp : Loc) (R : GoString → GoInterface → IProp GF) (γi : GName) :
    sh.[ConcurrentMapShared, go!"items"] ↦□ mp ∗
      sync.isRWMutexGuard (sh.[ConcurrentMapShared, go!"RWMutex"]) (shardP mp R γi) ⊢
    isShardV sh R γi := by
  iintro ⟨#H1, #H2⟩
  iunfold isShardV
  iexists mp
  iframe H1 H2

theorem shardTok_intro (sh mp : Loc) (R : GoString → GoInterface → IProp GF) (γi : GName) :
    sh.[ConcurrentMapShared, go!"items"] ↦□ mp ∗
      sync.ownRWMutex (sh.[ConcurrentMapShared, go!"RWMutex"]) (shardP mp R γi) ⊢
    shardTok sh R γi := by
  iintro ⟨#H1, H2⟩
  iunfold shardTok
  iexists mp
  iframe H1 H2

theorem NewV.wp_proof : NewV.spec (GF := GF) := fun n R => by
  wp_start as ⟨#Hn, %Hn0⟩
  iapply wp_fupd
  wp_auto
  wp_apply (wp_slice_make2 (V := Loc) n) as %sl ⟨Hsl, -⟩
  · ipureintro; word
  ihave HL : (∃ (iv : w64) (done : List (Loc × GName)), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (done.map Prod.fst ++
        List.replicate (sint.nat n - done.length) (zero_val Loc)) ∗
      "Hdone" ∷ ([∗list] p ∈ done, isShardV p.1 R p.2 ∗
        ghostVar p.2 (1 : Qp).half (∅ : GMap GoString GoInterface) ∗
        [∗list] _y ∈ List.replicate cmapReaders (), shardTok p.1 R p.2) ∗
      "%Hi" ∷ ⌜sint.Z iv = done.length ∧ done.length ≤ sint.nat n⌝ : IProp GF) $$ [i Hsl]
  · iexists _, []
    simp only [List.map_nil, List.nil_append, List.length_nil, Nat.sub_zero]
    iframe
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; simp
  wp_for HL
  wp_if_destruct
  · have hlt : sint.Z iv < sint.Z n := by simpa using Hif
    wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %mp HM
    iStructNamed «$r0»
    ipersist items
    imod ghostVar_alloc (GF := GF) (∅ : GMap GoString GoInterface) with ⟨%γi, Hgi⟩
    icases (ghostVar_split_half (GF := GF) γi 1 (∅ : GMap GoString GoInterface)).1 $$ Hgi
      with ⟨Hgi, Hgi'⟩
    imod sync.init_RWMutex (shardP mp R γi) (E := ⊤) _ $$ [HM Hgi] RWMutex with Htoks
    · inext; iunfold shardP; iexists ∅; iframe HM Hgi
      iintro !> %k %v %Hk; simp at Hk
    have hlen : sint.nat n = done.length + (sint.nat n - done.length) := by omega
    ihave %Hl := ownSlice_len _ _ _ $$ Hsl
    simp only [List.length_append, List.length_replicate, List.length_map] at Hl
    have hb : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z sl.len := by constructor <;> word
    rw [if_pos hb]
    wp_apply wp_store_slice_index $$ [$Hsl] as Hsl
    · ipureintro; simp; word
    have hK : Int.toNat sync.rwmutex.actualMaxReaders = (cmapReaders - 1) + 1 := by
      unfold cmapReaders; have := sync.actualMaxReaders_ge_2; omega
    obtain ⟨Kr, hKr⟩ : ∃ Kr, cmapReaders = Kr + 1 := ⟨_, by rw [← hK]; rfl⟩
    have hKa : Int.toNat sync.rwmutex.actualMaxReaders = Kr + 1 := hKr
    simp only [hKa, List.replicate]
    icases Htoks with ⟨Htok, Htoks⟩
    icases persistent_entails_left (sync.ownRWMutex_isRWMutexGuard _ _) $$ Htok with ⟨Htok, #Hguard⟩
    ihave #Hsh : isShardV «$r0_ptr» R γi $$ []
    · iapply isShardV_intro; iframe items Hguard
    ihave Hts : ([∗list] _y ∈ List.replicate cmapReaders (), shardTok «$r0_ptr» R γi) $$ [Htok Htoks]
    · rw [hKr]
      simp only [List.replicate]
      iapply BigSepL.bigSepL_cons.2
      isplitl [Htok]
      · iapply shardTok_intro; iframe items Htok
      ihave H := BigSepL.bigSepL_impl $$ Htoks
      iapply H
      iintro !> %_ %_ %_ Ht
      iapply shardTok_intro; iframe items Ht
    ihave Hnew : ([∗list] p ∈ done ++ [(«$r0_ptr», γi)], isShardV p.1 R p.2 ∗
        ghostVar p.2 (1 : Qp).half (∅ : GMap GoString GoInterface) ∗
        [∗list] _y ∈ List.replicate cmapReaders (), shardTok p.1 R p.2) $$ [Hdone Hts Hgi']
    · iapply BigSepL.bigSepL_snoc.2
      iframe Hdone
      iframe Hsh Hgi' Hts
    wp_for_post
    iframe
    iexists _, done ++ [(«$r0_ptr», γi)]
    have hset : (done.map Prod.fst ++ List.replicate (sint.nat n - done.length) (zero_val Loc)).set
        (sint.Z iv).toNat «$r0_ptr» = (done ++ [(«$r0_ptr», γi)]).map Prod.fst ++
          List.replicate (sint.nat n - (done ++ [(«$r0_ptr», γi)]).length) (zero_val Loc) := by
      have h1 : (sint.Z iv).toNat = (done.map Prod.fst).length := by simp; omega
      obtain ⟨k, hk⟩ : ∃ k, sint.nat n - done.length = k + 1 := ⟨sint.nat n - done.length - 1, by word⟩
      rw [h1, hk, List.set_append_right _ _ (by omega)]
      simp only [Nat.sub_self, List.replicate_succ, List.set_cons_zero, List.length_append,
        List.length_singleton, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append]
      rw [show sint.nat n - (done.length + 1) = k by omega]
    rw [hset]
    iframe i Hsl Hnew
    ipureintro; simp only [List.length_append, List.length_singleton]; constructor <;> word
  · have hd : done.length = sint.nat n := by
      have : ¬ sint.Z iv < sint.Z n := Hif; word
    rw [hd, Nat.sub_self, List.replicate_zero, List.append_nil]
    imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
    icases BigSepL.bigSepL_sep_eqv.1 $$ Hdone with ⟨#Hshs, Hdone⟩
    icases BigSepL.bigSepL_sep_eqv.1 $$ Hdone with ⟨Hgs, Htoks⟩
    imod ghostVar_alloc (GF := GF) ((∅ : GMap GoString GoInterface), (sint.nat n, done))
      with ⟨%γ, Hg⟩
    icases (ghostVar_split_half (GF := GF) γ 1
      ((∅ : GMap GoString GoInterface), (sint.nat n, done))).1 $$ Hg
      with ⟨Hg, Hview⟩
    imod inv_alloc cmapN ⊤ (cmapInv γ (sint.nat n) done) $$ [Hg Hgs] with #Hinv
    · inext
      iunfold cmapInv
      iexists ∅
      iframe Hg
      simp only [shardPart_empty]
      iexact Hgs
    ihave #Hc : cmapCore sl γ R n done $$ []
    · iunfold cmapCore
      iframe Hn Hsl Hshs Hinv
      ipureintro; exact ⟨Hn0, hd⟩
    imodintro
    iapply HΦ
    iexists γ
    isplitr
    · iunfold isCMapV; iexists n, done; iexact Hc
    isplitl [Hview]
    · iunfold cmapView; iexists _; iexact Hview
    ihave Htoks := bigSepL_transpose _ done cmapReaders $$ Htoks
    ihave H := BigSepL.bigSepL_impl $$ Htoks
    iapply H
    iintro !> %_ %_ %_ Ht
    iunfold readerV
    iexists n, done
    iframe Hc Ht

theorem New.wp_proof (wp_NewV : NewV.spec (GF := GF)) : New.spec (GF := GF) := fun n R => by
  wp_start_folded as ⟨#Hn, %Hn0⟩
  iapply wp_fupd
  wp_apply wp_NewV $$ [$Hn] as %m ⟨%γ, #Hm, Hview, Hrs⟩
  · ipureintro; exact Hn0
  imod cmapOld_alloc ⊤ γ ∅ $$ Hview with #Hold
  imodintro
  iapply HΦ
  isplitr
  · iapply isCMap_intro; iframe Hm Hold
  ihave H := BigSepL.bigSepL_impl $$ Hrs
  iapply H
  iintro !> %_ %_ %_ Hr
  iapply reader_intro
  iframe Hr Hold

end proof

end Perennial.github_com.orcaman.concurrent_map
