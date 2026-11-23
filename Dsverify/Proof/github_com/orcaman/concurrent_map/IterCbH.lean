/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/IterCbH.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`IterCb` with the entry **held** (round 13, sv-swc; additive; requested by sv-swb for
`stopDescs`, notes/prove-swift.md §19 "descState"): the strong spec `IterCbV` whose `fn` step
also gets `cmapHeld γ h k v` (and gives back the same one): while the shard's read lock is held, no writer
can change the shard, so the entry `k ↦ v` is in the client's **current** view for the whole
call, not only in the view observed when the lock was taken. Go: `IterCb` holds the shard's
read lock while it calls `fn` (concurrent-map v1.0.0's `IterCb`), so a concurrent `Remove` of
`k` waits for `fn` to return.

* `cmapHeld γ h k v` (`h : HeldId`, abstract to clients): shard `i`'s ghost fraction (the reader's, from `shardP`) at a part `Mi`
  with `Mi !! k = some v`, with the map's invariant;
* `cmapHeld_view` (the law): with `cmapView γ M` (e.g. from the client's own invariant), under
  a mask containing `cmapN`: `M !! k = some v`;
* `ConcurrentMap.IterCbVH.spec`, proved (`ConcurrentMap.IterCbVH.wp_proof`, `IterCbV`'s proof
  with the shard's ghost fraction lent to each `fn` call; no callee hypothesis).
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

/-- Which shard fraction holds an entry (`cmapHeld`'s index; clients treat it abstractly). -/
structure HeldId [GooseExts] where
  n : Nat
  shs : List (Loc × GName)
  i : Nat
  p : Loc × GName
  q : Qp
  Mi : GMap GoString GoInterface

section held
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]

/-- The entry `k ↦ v` is held in the map's view `γ` (see the file header): a reader's fraction
of its shard's ghost variable. -/
def cmapHeld (γ : GName) (h : HeldId) (k : GoString) (v : GoInterface) : IProp GF :=
  iprop(inv cmapN (cmapInv γ h.n h.shs) ∗ ghostVar h.p.2 h.q h.Mi ∗
    ⌜h.shs[h.i]? = some h.p ∧ h.Mi !! k = some v⌝)

/-- **The held entry is in the current view.** -/
theorem cmapHeld_view (E : CoPset) (hE : ↑cmapN ⊆ E) (γ : GName) (h : HeldId) (k : GoString)
    (v : GoInterface) (M : GMap GoString GoInterface) :
    cmapHeld (GF := GF) γ h k v ∗ cmapView γ M ⊢
      |={E}=> cmapHeld γ h k v ∗ cmapView γ M ∗ ⌜M !! k = some v⌝ := by
  obtain ⟨n, shs, i, p, q, Mi⟩ := h
  iintro ⟨Hh, Hview⟩
  iunfold cmapHeld at Hh
  icases Hh with ⟨#Hinv, Hg, %Hp⟩
  iinv Hinv with Hi0 Hclose
  iunfold cmapInv at Hi0
  icases Hi0 with ⟨%M0, >Hv, >Hs⟩
  iunfold cmapView at Hview
  icases Hview with ⟨%c, Hview⟩
  icombine Hview Hv gives % ⟨_, Heq⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
  icases (BigSepL.bigSepL_lookup_acc Hp.1).1 $$ Hs with ⟨Hi, Hback⟩
  icombine Hg Hi gives % ⟨_, HeqI⟩
  ihave Hs := Hback $$ %p Hi
  rw [list_set_lookup_self _ _ _ Hp.1]
  imod Hclose $$ [Hv Hs] with _
  · inext; iunfold cmapInv; iexists M; iframe Hv Hs
  imodintro
  isplitl [Hg]
  · iunfold cmapHeld; iframe Hinv Hg; ipureintro; exact Hp
  isplitl [Hview]
  · iunfold cmapView; iexists _; iexact Hview
  ipureintro
  have h := Hp.2
  rw [HeqI, lookup_shardPart] at h
  split at h
  · exact h
  · cases h

end held

section spec
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

/-- `IterCbV` whose `fn` step also holds the entry (`cmapHeld γ h k v`, the same given back; see the file
header). -/
abbrev ConcurrentMap.IterCbVH.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) (fn : GoFunc)
    (I : List (GMap GoString GoInterface) → List (GoString × GoInterface) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ readerV m γ R ∗
      I [] [] ∗
      □ (∀ (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface)),
          I obs vis -∗
          |={⊤ \ ↑cmapN, ∅}=> ∃ M : GMap GoString GoInterface, cmapView γ M ∗
            (cmapView γ M ={∅, ⊤ \ ↑cmapN}=∗ I (obs ++ [M]) vis)) ∗
      □ (∀ (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface))
          (k : GoString) (v : GoInterface) (h : HeldId) (Φ : val → IProp GF),
          ⌜∃ M, obs.getLast? = some M ∧ M !! k = some v⌝ -∗ R k v -∗ cmapHeld γ h k v -∗
          I obs vis -∗
          ▷ (cmapHeld γ h k v ∗ I obs (vis ++ [(k, v)]) -∗ Φ #()) -∗
          WP (App (App (Val #fn) (Val #k)) (Val #v)) {{ Φ }}) }}
    (App (Val #(methods ConcurrentMap.ty go!"IterCb" #m)) (Val #fn))
  {{ RET #(); readerV m γ R ∗
      ∃ (n : Nat) (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface)),
        cmapShards n ∗ I obs vis ∗ ⌜iterTrace n obs vis⌝ }}

end spec

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

set_option goose.wp.extras true

theorem ConcurrentMap.IterCbVH.wp_proof : ConcurrentMap.IterCbVH.spec (GF := GF) :=
    fun m γ R fn I => by
  wp_start as ⟨Hr, HI, #Hobs, #Hfn⟩
  iunfold readerV at Hr
  icases Hr with ⟨%n, %shs, #Hc, Htoks⟩
  ihave #Hc' := Hc
  iunfold cmapCore at Hc'
  icases Hc' with ⟨#Hn, #Hsl, %Hns, #Hinv, #Hshs⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_map] at Hl
  wp_auto
  ihave HL : (∃ (iv dv : w64) (obs : List (GMap GoString GoInterface))
      (vis : List (GoString × GoInterface)), "i" ∷ i_ptr ↦ iv ∗ "idx" ∷ idx_ptr ↦ dv ∗
      "Htoks" ∷ ([∗list] p ∈ shs, shardTok p.1 R p.2) ∗ "HI" ∷ I obs vis ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ sint.Z m.len ∧
        iterTraceUpTo (sint.nat n) (sint.nat iv) obs vis⌝ : IProp GF) $$ [i idx Htoks HI]
  · iexists _, _, [], []; iframe; ipureintro
    refine ⟨by decide, by word, ?_⟩
    exact iterTraceUpTo_nil _
  wp_for HL
  wp_if_destruct
  · have hb : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z m.len := ⟨Hi.1, by simpa using Hif⟩
    rw [if_pos hb]
    obtain ⟨p, hp⟩ : ∃ p, shs[(sint.Z iv).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have hp' : (shs.map Prod.fst)[(sint.Z iv).toNat]? = some p.1 := by
      rw [List.getElem?_map, hp]; rfl
    wp_apply wp_load_slice_index _ _ _ _ p.1 Hi.1 $$ [$Hsl] as -
    · ipureintro; exact hp'
    rw [if_pos hb]
    wp_apply wp_load_slice_index _ _ _ _ p.1 Hi.1 $$ [$Hsl] as -
    · ipureintro; exact hp'
    icases (BigSepL.bigSepL_lookup_acc hp).1 $$ Htoks with ⟨Htok, Hback⟩
    iunfold shardTok at Htok
    icases Htok with ⟨%mp, #Hitems, Htok⟩
    wp_method_call; wp_call
    wp_apply sync.RWMutex.wp_RLock $$ [$Htok] as ⟨Hrl, HP⟩
    iunfold shardP at HP
    icases HP with ⟨%Mi, HM, Hgi, #HR⟩
    imod cmap_observe γ (sint.nat n) shs _ p hp _ Mi (fun M => I (obs ++ [M]) vis)
      $$ [Hgi HI] with ⟨Hgi, %M, %HMi, HI⟩
    · iframe Hinv Hgi
      iapply Hobs $$ HI
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply (wp_map_for_range (fun keys (j : Int) => iprop(∃ (kv : GoString) (vv : GoInterface),
        key_ptr ↦ kv ∗ value_ptr ↦ vv ∗ fn_ptr ↦ fn ∗
        ghostVar p.2 sync.rfrac.half Mi ∗
        I (obs ++ [M]) (vis ++ entriesOf Mi (keys.take j.toNat)) ∗ ⌜0 ≤ j⌝))) $$ HM
    iintro %keys %hkeys
    isplitl [key value fn HI Hgi]
    · iexists _, _
      simp only [Int.toNat_zero, List.take_zero]
      rw [show entriesOf Mi [] = [] from rfl, List.append_nil]
      iframe; ipureintro; omega
    isplitl []
    · imodintro
      iintro %j %key %u ⟨%hk1, %hk2⟩ ⟨%kv, %vv, Hk, Hv, Hf, Hgi, HI, %hj⟩
      wp_auto
      ihave #HRk := HR $$ %key %u %hk2
      ihave Hheld : cmapHeld γ (HeldId.mk (sint.nat n) shs (sint.Z iv).toNat p sync.rfrac.half Mi) key u
        $$ [Hgi]
      · iunfold cmapHeld
        iframe Hinv Hgi
        ipureintro; exact ⟨hp, hk2⟩
      wp_apply Hfn $$ %(obs ++ [M]) %(vis ++ entriesOf Mi (keys.take j.toNat)) %key %u
        %(HeldId.mk (sint.nat n) shs (sint.Z iv).toNat p sync.rfrac.half Mi) [] HRk Hheld HI
        as ⟨Hheld, HI⟩
      · ipureintro
        refine ⟨M, by simp, ?_⟩
        rw [HMi, lookup_shardPart] at hk2
        split at hk2
        · exact hk2
        · cases hk2
      iunfold cmapHeld at Hheld
      icases Hheld with ⟨-, Hgi, -⟩
      unfold forMapPostcondition
      iright; ileft
      isplit
      · ipureintro; rfl
      · iexists _, _
        iframe
        have hjn : (j + 1).toNat = j.toNat + 1 := by omega
        rw [hjn, entriesOf_take_succ Mi keys _ key u hk1 hk2, List.append_assoc]
        iframe
        ipureintro; omega
    iintro ⟨%kv, %vv, Hk, Hv, Hf, Hgi, HI, -⟩ HM
    wp_auto
    wp_method_call; wp_call
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HM Hgi] as Htok
    · inext; iunfold shardP; iexists Mi; iframe HM Hgi HR
    ihave Htoks := Hback $$ %p [Htok]
    · iunfold shardTok; iexists mp; iframe Hitems Htok
    rw [list_set_lookup_self _ _ _ hp]
    obtain ⟨hmem, hsize, hnd⟩ := hkeys
    have htake : keys.take ((GMap.size Mi : Int)).toNat = keys := by
      rw [Int.toNat_natCast, ← hsize, List.take_length]
    rw [htake]
    wp_for_post
    iframe
    iexists _, _, (obs ++ [M]), (vis ++ entriesOf Mi keys)
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    have hiv : sint.nat (iv + W64 1) = sint.nat iv + 1 := by word
    rw [hiv]
    have := iterTraceUpTo_snoc (sint.nat n) (sint.nat iv) obs vis M (entriesOf Mi keys) Hi.2.2
      (by
        have hi : (sint.Z iv).toNat = sint.nat iv := rfl
        rw [← hi, ← HMi]; exact entriesOf_perm Mi keys hmem hnd)
    exact this
  · have hiv : sint.nat iv = sint.nat n := by
      have : ¬ sint.Z iv < sint.Z m.len := by simpa using Hif
      word
    iapply HΦ
    isplitl [Htoks]
    · iunfold readerV; iexists n, shs; iframe Hc Htoks
    iexists (sint.nat n), obs, vis
    iframe HI
    isplitl []
    · iapply cmapCore_shards $$ Hc
    ipureintro
    refine ⟨by word, ?_⟩
    have := Hi.2.2; rw [hiv] at this; exact this

end proof

end Perennial.github_com.orcaman.concurrent_map
