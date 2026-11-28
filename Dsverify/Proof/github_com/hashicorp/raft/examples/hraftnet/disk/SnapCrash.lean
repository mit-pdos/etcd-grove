/-
(hraft_robust R3) **`snapsCrash`**, the snapshot store's crash lemma, as `diskCrash` (`Crash.lean`): at a crash,
the invariant (opened with its crash token and closed on its crashed side) and `durable`'s crash lemma
(`durInv_crash`, on `g.f`) give the file's contents for the next generation's boot (`durFound`, `durFoundTmp`,
the rest of the crash), and what they hold: the committed latest (`snapHolds v lat svs`, with `svs` the latest's
servers, which its slice holds), or, a `Close`'s window open and its new file surviving, the close obligation
`Qc m b` back with `|b| < 2^63` and the next latest `newerSnap lat m b`, or, in `FreshSnaps`'s window, the
caller's `Wf` back (the file unconstrained). `lat` is the client's view, agreed with the invariant's half and
dropped. The next generation's `OpenSnaps` takes the pure `snapHolds v lat' svs` and gives back the latest up to
its servers slice (`latEquiv`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.SnapLemmas
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Crash

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

open Iris Iris.BI Iris.ProofMode Iris.Std github_com.hashicorp.raft proto EtcdGrove Fs

section ns
variable [GooseExts]

/-- `durable`'s namespace is open with the snapshot store's invariant open. -/
theorem durN_sub_diff_snaps : (↑DurFs.durN : CoPset) ⊆ ⊤ \ ↑snapsN := by
  intro x hx
  rw [Std.LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h => snapsN_not_durN x h hx⟩

set_option maxRecDepth 100000 in
/-- The shared os invariant's namespace is open with the snapshot store's invariant open. -/
theorem osShN_sub_diff_snaps : (↑osShN : CoPset) ⊆ ⊤ \ ↑snapsN := by
  intro x hx
  rw [Std.LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h => ?_⟩
  have h1 := nclose_subseteq' _ (mask_ndot_ne' nroot "hraftstore" "osfsShared" (by decide)) x h
  rw [Std.LawfulSet.mem_diff] at h1
  exact h1.2 hx

end ns

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- An image's latest that represents `lat` holds it, with the latest's servers. -/
theorem snapHolds_of_rep (lat : SnapLatest) (lt : SLat) (nid : w64) (hok : ltOk lt) :
    latRep (GF := GF) lat lt ⊢
      ∃ svs : List Server, ⌜snapHolds (some (encSnap ⟨nid, lt⟩)) lat svs⌝ ∗ latSrvs lat svs := by
  rcases lat with _ | ⟨m, b⟩ <;> rcases lt with _ | ⟨sm, b'⟩ <;> simp only [latRep, latSrvs]
  · iintro -
    iexists []
    isplit
    · ipureintro; exact ⟨⟨nid, none⟩, (ltOk_iff nid none).2 hok, rfl, trivial⟩
    · itrivial
  · iintro H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H
  · iintro ⟨%hb, #Hmr⟩
    subst hb
    unfold metaRep cfgRep
    icases Hmr with ⟨%hp, %svs, #Hs, %hsv⟩
    iexists svs
    iframe #
    ipureintro
    exact ⟨⟨nid, some (sm, b')⟩, (ltOk_iff nid _).2 hok, rfl, rfl, hp, hsv.symm⟩

/-- **The snapshot store's crash lemma** (see the file header). -/
theorem snapsCrash (Q : OsState → OsState → Prop) (L' : GooseLocalGS GF) (g : SnapGen)
    (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) (Dl : List Ino) (tt : Bool) (V' : Hist)
    (lat : SnapLatest)
    (hD : ∀ i ∈ Dl, V'.now.entry g.f.J g.f.b ≠ some (.file i) ∧ V'.now.entry g.f.J g.f.tb ≠ some (.file i)) :
    ⊢ snapsInv g Qc Wf -∗ crashed (hC := hG.goose_localGS.goose_crashGS) -∗ token g.γk -∗ £ 1 -∗
      DurFs.durInv (L := hG.goose_localGS) g.γd g.f -∗ DurFs.durCrashTok (GF := GF) g.γd -∗
      osSharedInv (L := hG.goose_localGS) g.R -∗
      snapsOwn g lat -∗
      crashRest Q (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) Dl tt V' ={⊤}=∗
      ∃ (v : Option GoString) (Dl' : List Ino),
        ⌜∀ i ∈ Dl', V'.now.entry g.f.J g.f.b = some (.file i) ∨ V'.now.entry g.f.J g.f.tb = some (.file i)⌝ ∗
        DurFs.durFound (L := L') g.f V'.now v ∗ DurFs.durFoundTmp (L := L') g.f V'.now ∗
        crashRest Q (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) (Dl' ++ Dl) tt V' ∗
        ((∃ svs : List Server, ⌜snapHolds v lat svs⌝ ∗ latSrvs lat svs) ∨
          (∃ (m : SnapshotMeta) (b : List w8), Qc m b ∗ ⌜b.length < 2 ^ 63⌝ ∗
            ∃ svs : List Server, ⌜snapHolds v (newerSnap lat m b) svs⌝ ∗ latSrvs (newerSnap lat m b) svs) ∨
          Wf) := by
  iintro #Hinv #Hcr Htk Hlc #Hdi Hdc #Hsh HA Hrest
  iunfold snapsInv at Hinv
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hb, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc Hb with Hb
  iunfold snapsBody at Hb
  icases Hb with ⟨%lat0, %lt, %w, %s, Hds, Hrec0, Hb⟩
  icases Hb with (⟨Hl, #Hr, %Hok, Hwin⟩ | ⟨-, Htk'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Htk Htk'
  iunfold snapsOwn at HA
  ihave %HAe := ghostVar_agree _ _ _ _ _ $$ HA Hl
  subst HAe
  imod DurFs.durInv_crash Q hG.goose_localGS L' g.γd g.f g.R Dl tt V' s (⊤ \ ↑snapsN) durN_sub_diff_snaps
    osShN_sub_diff_snaps hD $$ Hdi Hcr Hdc Hds Hsh Hrest
    with ⟨%v, %Dl', ⟨%hv, %hDl'⟩, Hds, Hf, Ht, Hrest⟩
  ihave Hres : iprop((∃ svs : List Server, ⌜snapHolds v lat svs⌝ ∗ latSrvs lat svs) ∨
      (∃ (m : SnapshotMeta) (b : List w8), Qc m b ∗ ⌜b.length < 2 ^ 63⌝ ∗
        ∃ svs : List Server, ⌜snapHolds v (newerSnap lat m b) svs⌝ ∗ latSrvs (newerSnap lat m b) svs) ∨
      Wf) $$ [Hwin]
  · cases w with
    | idle =>
      simp only [snapWinRes]
      icases Hwin with %Hidle
      obtain ⟨nid, rfl⟩ := Hidle
      have hv' : v = some (encSnap ⟨nid, lt⟩) := by
        rcases hv with h | h; exact h; simp at h
      subst hv'
      ileft
      iapply snapHolds_of_rep lat lt nid Hok $$ Hr
    | «open» m b sm nid sy =>
      simp only [snapWinRes]
      icases Hwin with ⟨%Hf', #Hmr, HQc⟩
      obtain ⟨hnew, hb, hok', hcur, halt⟩ := Hf'
      rcases hv with hv | hv
      · iright; ileft
        iexists m, b
        iframe HQc
        isplitr
        · ipureintro; exact hb
        rw [hnew, hv, hcur]
        iapply snapHolds_of_rep (some (m, b)) (some (sm, b)) nid hok'
        simp only [latRep]
        iframe #
      · ileft
        rcases halt with h | ⟨-, nid0, h⟩
        · rw [h] at hv; cases hv
        · rw [h] at hv; cases hv
          iapply snapHolds_of_rep lat lt nid0 Hok $$ Hr
    | fresh r =>
      simp only [snapWinRes]
      icases Hwin with ⟨HWf, -⟩
      iright; iright; iexact HWf
  imod Hclose $$ [Hds Hrec0 Htk] with -
  · inext; iunfold snapsBody; iexists lat, lt, w, s; iframe Hds Hrec0; iright; iframe #; iframe
  imodintro
  iexists v, Dl'
  iframe
  ipureintro; exact hDl'

end crash

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
