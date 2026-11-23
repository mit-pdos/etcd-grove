/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/IterCbP.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`IterCb` with pinned entries (round 16, sv-swb; additive; the "stronger `IterCb`" requested in
round 13 for `stopDescs`, notes/prove-swift.md §19 and §22): Go's `IterCb` calls `fn(k, v)` while
holding `k`'s shard's read lock, so no writer changes that shard during the call. `fn` gets a
**pin** `cmapPin γ k v π` (the read lock's fraction of the shard's ghost variable, `π` its data),
which it returns; with the pin, any atomic step that holds the client's view `cmapView γ M` learns
`M !! k = some v` (`cmapPin_lookup`, opening `cmapN`). So a client whose entries' resources sit
in its own invariant next to `cmapView` (the descriptors' `descInv`) can access entry `k`'s
resources during `fn` although the entry's owner may remove it concurrently in Go's terms only
after `fn` returns.

* `ConcurrentMap.IterCbVP.spec`: `IterCbVN` with the pin; proved (`IterCbVP.wp_proof`, the proof
  of `IterCbVN` with the shard's ghost fraction lent to `fn`); no callee hypothesis.
* `cmapPin_lookup`.
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.IterCbN

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

set_option linter.unusedSectionVars false

section pind
variable [GooseExts]

/-- A pin's data: the shard count, the shards, the shard's index and entry, the fraction of its
ghost variable, and the shard's contents. -/
structure PinD where
  n : Nat
  shs : List (Loc × GName)
  i : Nat
  p : Loc × GName
  q : Qp
  Mi : GMap GoString GoInterface

end pind

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **A pinned entry** `k ↦ v` of the map with view `γ` (see the file header). -/
def cmapPin (γ : GName) (k : GoString) (v : GoInterface) (π : PinD) : IProp GF :=
  iprop(inv cmapN (cmapInv γ π.n π.shs) ∗ ghostVar π.p.2 π.q π.Mi ∗
    ⌜π.shs[π.i]? = some π.p ∧ π.Mi !! k = some v⌝)

end defs

section steps
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- With a pin, the client's view has the pinned entry. -/
theorem cmapPin_lookup (γ : GName) (k : GoString) (v : GoInterface) (π : PinD)
    (M : GMap GoString GoInterface) (E : CoPset) (hE : ↑cmapN ⊆ E) :
    cmapPin (GF := GF) γ k v π ∗ cmapView γ M ⊢
      |={E}=> ⌜M !! k = some v⌝ ∗ cmapPin γ k v π ∗ cmapView γ M := by
  iintro ⟨Hpin, Hview⟩
  iunfold cmapPin at Hpin
  icases Hpin with ⟨#Hinv, Hg, %Hp⟩
  iinv Hinv with Hi0 Hclose
  iunfold cmapInv at Hi0
  icases Hi0 with ⟨%M0, >Hv, >Hs⟩
  iunfold cmapView at Hview
  icases Hview with ⟨%c, Hview⟩
  icombine Hview Hv gives % ⟨_, Heq⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
  icases (BigSepL.bigSepL_lookup_acc Hp.1).1 $$ Hs with ⟨Hi, Hback⟩
  icombine Hg Hi gives % ⟨_, HeqI⟩
  ihave Hs := Hback $$ %π.p Hi
  rw [list_set_lookup_self _ _ _ Hp.1] at *
  imod Hclose $$ [Hv Hs] with _
  · inext; iunfold cmapInv; iexists M; iframe Hv Hs
  imodintro
  have hk := Hp.2
  rw [HeqI, lookup_shardPart] at hk
  split at hk
  · isplitr
    · ipureintro; exact hk
    isplitl [Hg]
    · iunfold cmapPin; iframe Hinv Hg; ipureintro; exact Hp
    iunfold cmapView; iexists _; iexact Hview
  · cases hk

end steps

section spec
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

/-- `IterCbVN` whose `fn` step also gets the entry's pin, given back (see the file header). -/
abbrev ConcurrentMap.IterCbVP.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) (fn : GoFunc)
    (I : List (GMap GoString GoInterface) → List (GoString × GoInterface) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ readerV m γ R ∗
      I [] [] ∗
      □ (∀ (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface)),
          I obs vis -∗
          |={⊤ \ ↑cmapN, ∅}=> ∃ M : GMap GoString GoInterface, cmapView γ M ∗
            (cmapView γ M ={∅, ⊤ \ ↑cmapN}=∗ I (obs ++ [M]) vis)) ∗
      □ (∀ (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface))
          (k : GoString) (v : GoInterface) (π : PinD) (Φ : val → IProp GF),
          ⌜(∃ M, obs.getLast? = some M ∧ M !! k = some v) ∧ k ∉ vis.map Prod.fst⌝ -∗
          cmapPin γ k v π -∗ R k v -∗ I obs vis -∗
          ▷ (cmapPin γ k v π -∗ I obs (vis ++ [(k, v)]) -∗ Φ #()) -∗
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

theorem ConcurrentMap.IterCbVP.wp_proof : ConcurrentMap.IterCbVP.spec (GF := GF) :=
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
        I (obs ++ [M]) (vis ++ entriesOf Mi (keys.take j.toNat)) ∗
        ghostVar p.2 (sync.rfrac).half Mi ∗ ⌜0 ≤ j⌝))) $$ HM
    iintro %keys %hkeys
    isplitl [key value fn HI Hgi]
    · iexists _, _
      simp only [Int.toNat_zero, List.take_zero]
      rw [show entriesOf Mi [] = [] from rfl, List.append_nil]
      iframe; ipureintro; omega
    isplitl []
    · imodintro
      iintro %j %key %u ⟨%hk1, %hk2⟩ ⟨%kv, %vv, Hk, Hv, Hf, HI, Hgi, %hj⟩
      wp_auto
      ihave #HRk := HR $$ %key %u %hk2
      wp_apply Hfn $$ %(obs ++ [M]) %(vis ++ entriesOf Mi (keys.take j.toNat)) %key %u
        %(⟨sint.nat n, shs, (sint.Z iv).toNat, p, (sync.rfrac).half, Mi⟩ : PinD) [] [Hgi] HRk HI
        as Hpin HI
      · ipureintro
        have hk2' := hk2
        rw [HMi, lookup_shardPart] at hk2'
        split at hk2'
        · rename_i hsh
          refine ⟨⟨M, by simp, hk2'⟩, ?_⟩
          exact fresh_key (sint.nat n) (sint.nat iv) obs vis Mi keys j.toNat key Hi.2.2 hsh
            hkeys.2.2 hk1
        · cases hk2'
      · iunfold cmapPin
        iframe Hinv Hgi
        ipureintro; exact ⟨hp, hk2⟩
      iunfold cmapPin at Hpin
      icases Hpin with ⟨-, Hgi, -⟩
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
    iintro ⟨%kv, %vv, Hk, Hv, Hf, HI, Hgi, -⟩ HM
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
