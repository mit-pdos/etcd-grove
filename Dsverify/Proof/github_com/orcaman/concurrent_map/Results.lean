/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/Results.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
What clients derive from the concurrent map's linked specs when they own the view outright (no
concurrent writer): `IterCb` visits exactly the map's entries (use (2'), `iterTrace_perm`), and
`Remove` deletes from the view; with `foldl_delete_empty` / `iterTrace_remove_all` (use (3')),
removing each key a pass collected empties the map. Use (1') (`iterTrace_visits`) needs the
general `wp_IterCbV`, the view in the client's own invariant.
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

set_option linter.unusedSectionVars false

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

set_option goose.wp.extras true

/-- (2') `m.IterCb(fn)` with the view `M` owned: `fn` is called on each entry of `M` once (and
on nothing else), `J vis` collecting them. -/
theorem ConcurrentMap.wp_IterCbOwn (m : GoSlice) (γ : GName)
    (R : GoString → GoInterface → IProp GF) (fn : GoFunc) (M : GMap GoString GoInterface)
    (J : List (GoString × GoInterface) → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ readerV m γ R ∗
        cmapView γ M ∗ J [] ∗
        □ (∀ (vis : List (GoString × GoInterface)) (k : GoString) (v : GoInterface)
            (Φ : val → IProp GF), ⌜M !! k = some v⌝ -∗ R k v -∗ J vis -∗
            ▷ (J (vis ++ [(k, v)]) -∗ Φ #()) -∗
            WP (App (App (Val #fn) (Val #k)) (Val #v)) {{ Φ }}) }}
      (App (Val #(methods ConcurrentMap.ty go!"IterCb" #m)) (Val #fn))
    {{ RET #(); readerV m γ R ∗ cmapView γ M ∗
        ∃ vis : List (GoString × GoInterface), J vis ∗ ⌜vis.Perm M.toList⌝ }} := by
  wp_start_folded as ⟨Hr, Hv, HJ, #Hfn⟩
  wp_apply (ConcurrentMap.wp_IterCbV m γ R fn
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
        obtain ⟨M', hM', hk⟩ := Hlast
        rw [← Hobs M' (List.mem_of_getLast? hM')]; exact hk
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

/-- (3') `m.Remove(key)` with the view `M` owned: it becomes `GMap.delete key M`. -/
theorem ConcurrentMap.wp_RemoveOwn (m : GoSlice) (γ : GName)
    (R : GoString → GoInterface → IProp GF) (key : GoString) (M : GMap GoString GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMapV m γ R ∗
        cmapView γ M }}
      (App (Val #(methods ConcurrentMap.ty go!"Remove" #m)) (Val #key))
    {{ RET #(); cmapView γ (GMap.delete key M) }} := by
  wp_start_folded as ⟨#Hm, Hv⟩
  iapply (ConcurrentMap.wp_RemoveV m γ R key) $$ [] [Hv HΦ]
  · iframe Hpkg Hm
  · inext
    iapply cmapView_au γ M (fun M => GMap.delete key M) (fun _ => iprop(True -∗ Φ #()))
    iframe Hv
    iintro Hv _
    iapply HΦ $$ Hv

end results

end Perennial.github_com.orcaman.concurrent_map
