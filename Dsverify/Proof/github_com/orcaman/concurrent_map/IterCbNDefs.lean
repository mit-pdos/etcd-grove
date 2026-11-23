/-
The definitions, specs and lemmas of `IterCbN.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

set_option linter.unusedSectionVars false

theorem not_mem_take_of_nodup {α : Type} (l : List α) (i : Nat) (a : α) (hnd : l.Nodup)
    (h : l[i]? = some a) : a ∉ l.take i := by
  intro hm
  have hd : a ∈ l.drop i := by
    rw [List.mem_iff_getElem?]; exact ⟨0, by simp [List.getElem?_drop, h]⟩
  rw [← List.take_append_drop i l] at hnd
  exact (List.nodup_append.mp hnd).2.2 a hm a hd rfl

section pure
variable [GooseExts]

/-- The entries visited in the first `i` shards are in those shards. -/
theorem iterTraceUpTo_shard_lt (n i : Nat) (obs : List (GMap GoString GoInterface))
    (vis : List (GoString × GoInterface)) (h : iterTraceUpTo n i obs vis) :
    ∀ p ∈ vis, shardOf n p.1 < i := by
  obtain ⟨hlen, ls, hls, rfl, hperm⟩ := h
  rintro ⟨k, v⟩ hp
  obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hl
  have hjl : j < i := by
    have := (List.getElem?_eq_some_iff.mp hj).1; omega
  obtain ⟨M, hM⟩ : ∃ M, obs[j]? = some M := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hin := (hperm j M l hM hj).mem_iff.mp hpl
  rw [GMap.mem_toList, lookup_shardPart] at hin
  split at hin
  · rename_i hs; simp only; omega
  · cases hin

/-- The fact `fn` learns (see the file header). -/
theorem fresh_key (n iv : Nat) (obs : List (GMap GoString GoInterface))
    (vis : List (GoString × GoInterface)) (Mi : GMap GoString GoInterface) (keys : List GoString)
    (j : Nat) (key : GoString) (hvis : iterTraceUpTo n iv obs vis) (hkey : shardOf n key = iv)
    (hnd : keys.Nodup) (hk : keys[j]? = some key) :
    key ∉ (vis ++ entriesOf Mi (keys.take j)).map Prod.fst := by
  rw [List.map_append, List.mem_append, entriesOf_keys]
  rintro (h | h)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    have := iterTraceUpTo_shard_lt n iv obs vis hvis p hp
    omega
  · exact not_mem_take_of_nodup keys j key hnd hk (List.mem_filter.mp h).1

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

/-- `IterCbV` whose `fn` step also gets `k ∉ vis.map Prod.fst` (see the file header). -/
abbrev ConcurrentMap.IterCbVN.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) (fn : GoFunc)
    (I : List (GMap GoString GoInterface) → List (GoString × GoInterface) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ readerV m γ R ∗
      I [] [] ∗
      □ (∀ (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface)),
          I obs vis -∗
          |={⊤ \ ↑cmapN, ∅}=> ∃ M : GMap GoString GoInterface, cmapView γ M ∗
            (cmapView γ M ={∅, ⊤ \ ↑cmapN}=∗ I (obs ++ [M]) vis)) ∗
      □ (∀ (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface))
          (k : GoString) (v : GoInterface) (Φ : val → IProp GF),
          ⌜(∃ M, obs.getLast? = some M ∧ M !! k = some v) ∧ k ∉ vis.map Prod.fst⌝ -∗
          R k v -∗ I obs vis -∗
          ▷ (I obs (vis ++ [(k, v)]) -∗ Φ #()) -∗
          WP (App (App (Val #fn) (Val #k)) (Val #v)) {{ Φ }}) }}
    (App (Val #(methods ConcurrentMap.ty go!"IterCb" #m)) (Val #fn))
  {{ RET #(); readerV m γ R ∗
      ∃ (n : Nat) (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface)),
        cmapShards n ∗ I obs vis ∗ ⌜iterTrace n obs vis⌝ }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

set_option goose.wp.extras true


/-- (2') `m.IterCb(fn)` with the view `M` owned: `fn` is called on each entry of `M` once (and
on nothing else), `J vis` collecting them; `fn` learns that its key is fresh. -/
theorem ConcurrentMap.wp_IterCbOwnN (wp_IterCbVN : ConcurrentMap.IterCbVN.spec (GF := GF)) (m : GoSlice) (γ : GName)
    (R : GoString → GoInterface → IProp GF) (fn : GoFunc) (M : GMap GoString GoInterface)
    (J : List (GoString × GoInterface) → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ readerV m γ R ∗
        cmapView γ M ∗ J [] ∗
        □ (∀ (vis : List (GoString × GoInterface)) (k : GoString) (v : GoInterface)
            (Φ : val → IProp GF), ⌜M !! k = some v ∧ k ∉ vis.map Prod.fst⌝ -∗ R k v -∗ J vis -∗
            ▷ (J (vis ++ [(k, v)]) -∗ Φ #()) -∗
            WP (App (App (Val #fn) (Val #k)) (Val #v)) {{ Φ }}) }}
      (App (Val #(methods ConcurrentMap.ty go!"IterCb" #m)) (Val #fn))
    {{ RET #(); readerV m γ R ∗ cmapView γ M ∗
        ∃ vis : List (GoString × GoInterface), J vis ∗ ⌜vis.Perm M.toList⌝ }} := by
  wp_start_folded as ⟨Hr, Hv, HJ, #Hfn⟩
  wp_apply (wp_IterCbVN m γ R fn
      (fun obs vis => iprop(cmapView γ M ∗ J vis ∗ ⌜∀ M' ∈ obs, M' = M⌝)))
    $$ [Hr Hv HJ] as ⟨Hr, %n, %obs, %vis, -, ⟨Hv, HJ, %Hobs⟩, %Htr⟩
  · iframe Hr
    isplitl [Hv HJ]
    · iframe Hv HJ; ipureintro; intro _ h; simp at h
    isplitl []
    · imodintro
      iintro %obs %vis ⟨Hv, HJ, %Hobs⟩
      iapply cmapView_au γ M (fun M => M) (fun M' => iprop(cmapView γ M ∗ J vis ∗
        ⌜∀ M'' ∈ obs ++ [M'], M'' = M⌝))
      iframe Hv
      iintro Hv
      iframe Hv HJ
      ipureintro
      intro M'' h
      rcases List.mem_append.mp h with h | h
      · exact Hobs M'' h
      · simp at h; exact h
    · imodintro
      iintro %obs %vis %k %v %Φ' %Hlast HR ⟨Hv, HJ, %Hobs⟩ HΦ'
      iapply Hfn $$ %vis %k %v %Φ' [] HR HJ [Hv HΦ']
      · ipureintro
        obtain ⟨⟨M', hM', hk⟩, hnv⟩ := Hlast
        rw [← Hobs M' (List.mem_of_getLast? hM')]; exact ⟨hk, hnv⟩
      · inext
        iintro HJ
        iapply HΦ'
        iframe Hv HJ
        ipureintro; exact Hobs
  iapply HΦ
  iframe Hr Hv
  iexists vis
  iframe HJ
  ipureintro
  exact iterTrace_perm n obs vis M Htr Hobs

end proof

end Perennial.github_com.orcaman.concurrent_map
