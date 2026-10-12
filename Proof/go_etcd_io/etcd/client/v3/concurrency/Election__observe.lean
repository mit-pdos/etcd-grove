/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Election__observe.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__observe
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Spec.go_etcd_io.etcd.client.v3.WithFirstCreate
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__Err

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

/-- The owner get's fields: no revision, not serializable, not a prefix get. -/
theorem observe_ownerOp_rev (pfx : GoString) :
    (ownerOp pfx).base.rev = W64 0 ∧ (ownerOp pfx).base.serializable = false ∧
      (ownerOp pfx).isPrefixGet pfx = false := by
  by_cases h : pfx = [] <;> simp [ownerOp, opGetModel, opFold, withTopM, withPrefixM, withSortM,
    withLimitM, OpFull.getInit, OpFull.newOp, OpModel.zero, h, OpFull.isPrefixGet]

/-- **The owner get** (`OpGet(pfx, WithFirstCreate()...)`) lists nothing on an empty state, and
otherwise one key-value, the leader. -/
theorem ownerOp_kvs' (pfx : GoString) (s kvs : List EtcdKv) (hp : pfx ≠ [])
    (hwf : EtcdStateWf pfx s) (h : rangeKvsOk (ownerOp pfx) (rangeSel s (ownerOp pfx)) kvs) :
    (kvs = [] → s = []) ∧ (∀ w, kvs = [w] → LeaderKvState w s) ∧ (kvs = [] ∨ ∃ w, kvs = [w]) := by
  obtain ⟨hkey, he, hso, hst, hl, hc, hko, h1, h2, h3, h4⟩ := ownerOp_fields pfx hp
  have hsel : rangeSel s (ownerOp pfx) = s := by
    unfold rangeSel; rw [rangeIn_prefix_all pfx _ s hp hwf hkey he, List.filter_eq_self]
    intro v _; exact kvFilterOk_zero _ v h1 h2 h3 h4
  rw [hsel] at h
  obtain ⟨l, hperm, -, hsorted, -, rfl⟩ := h
  have hsorted := hsorted hso
  rw [hst] at hsorted
  cases l with
  | nil =>
    refine ⟨fun _ => List.eq_nil_of_subset_nil (fun x hx => hperm.symm.subset hx), ?_, ?_⟩
    · intro w hw; simp [hc, hl, hko] at hw
    · left; simp [hc, hl, hko]
  | cons w l' =>
    have hk : (if (ownerOp pfx).base.countOnly then []
        else ((if 0 < sint.Z (ownerOp pfx).base.limit then (w :: l').take
          (sint.Z (ownerOp pfx).base.limit).toNat else w :: l').map
          (fun v => if (ownerOp pfx).keysOnly then { v with value := [] } else v))) = [w] := by
      simp [hc, hl, hko]
    rw [hk]
    refine ⟨fun h => by simp at h, ?_, Or.inr ⟨w, rfl⟩⟩
    intro w' hw'
    simp only [List.cons.injEq, and_true] at hw'
    subst hw'
    refine ⟨hperm.subset (by simp), ?_⟩
    intro v hv
    rcases List.mem_cons.1 (hperm.symm.subset hv) with rfl | hv'
    · exact Int.le_refl _
    · have := (List.pairwise_cons.1 hsorted).1 v hv'; simpa [kvLeBy] using this

theorem evs_sorted_le {xs : List EvModel} (hs : EvRevSorted xs) {i j : Nat} {a b : EvModel}
    (ha : xs[i]? = some a) (hb : xs[j]? = some b) (hij : i ≤ j) : sint.Z a.rev ≤ sint.Z b.rev := by
  rcases Nat.lt_or_eq_of_le hij with h | rfl
  · unfold EvRevSorted at hs
    rw [List.pairwise_iff_getElem] at hs
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hb
    exact hs i j hi hj h
  · rw [ha] at hb; cases hb; exact Int.le_refl _

/-- The position after a response bounds its events and the position before it. -/
theorem evs_pos (xs : List EvModel) (c : w64) (hs : EvRevSorted xs)
    (hall : ∀ e ∈ xs, sint.Z c < sint.Z e.rev) :
    sint.Z c ≤ sint.Z ((xs.getLast?.map EvModel.rev).getD c) ∧
      ∀ (k : Nat) (e : EvModel), xs[k]? = some e →
        sint.Z e.rev ≤ sint.Z ((xs.getLast?.map EvModel.rev).getD c) := by
  cases hx : xs.getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hx
    subst hx
    simp
  | some l =>
    have hl := List.getLast?_eq_getElem? (l := xs)
    rw [hx] at hl
    simp only [Option.map_some, Option.getD_some]
    refine ⟨Int.le_of_lt (hall l (List.mem_of_getLast? hx)), ?_⟩
    intro k e hk
    have := (List.getElem?_eq_some_iff.1 hk).1
    exact evs_sorted_le hs hk hl.symm (by omega)

section anchor
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- What `observe` knows of the key-value `v` it sent at `R`, for forwarding the puts of its key:
`v` was the leader at `R` (the get), or the prefix was empty at an earlier `R0` (the first put). -/
def obsAnchor (pfx : GoString) (v : EtcdKv) (R : w64) : IProp GF :=
  iprop((∃ s0 : List EtcdKv, □ etcdState R pfx s0 ∗ ⌜LeaderKvState v s0⌝) ∨
    (∃ R0 : w64, □ etcdState R0 pfx [] ∗ ⌜sint.Z R0 < sint.Z R⌝))

instance obsAnchor_persistent (pfx : GoString) (v : EtcdKv) (R : w64) :
    Persistent (obsAnchor (GF := GF) pfx v R) := by
  unfold obsAnchor; infer_instance

/-- Every key alive at `e` after an empty prefix at `R0 ≤ e` was created after `R0`. -/
theorem empty_after (pfx : GoString) (R0 e : w64) (s : List EtcdKv) (h : sint.Z R0 ≤ sint.Z e) :
    etcdState (GF := GF) R0 pfx [] ∗ etcdState e pfx s ⊢
      ⌜∀ w ∈ s, sint.Z R0 < sint.Z w.createRev⌝ := by
  iintro ⟨H0, He⟩
  ihave %Hp := etcdState_create_persist e R0 pfx s [] $$ [$He $H0]
  ipureintro
  intro w hw
  refine Int.lt_of_not_ge fun hle => ?_
  obtain ⟨v', hv', -⟩ := Hp w hw hle h
  simp at hv'

/-- The first put after an empty prefix: `v`, alive at `e ≥ R0`, is observed (third case), and
`R0 < e`. -/
theorem first_put (pfx : GoString) (R0 e : w64) (v : EtcdKv) (s : List EtcdKv) (hv : v ∈ s)
    (h : sint.Z R0 ≤ sint.Z e) :
    □ etcdState (GF := GF) R0 pfx [] ∗ □ etcdState e pfx s ⊢
      observedAt pfx v e ∗ obsAnchor pfx v e ∗ ⌜sint.Z R0 < sint.Z e⌝ := by
  iintro ⟨#H0, #He⟩
  ihave %Hemp := empty_after pfx R0 e s h $$ [$H0 $He]
  by_cases heq : R0 = e
  · subst heq
    ihave %Hag := etcdState_agree R0 pfx [] s $$ [$H0 $He]
    subst Hag
    simp at hv
  have hlt : sint.Z R0 < sint.Z e := by
    have : sint.Z R0 ≠ sint.Z e := fun h' => heq (by word)
    omega
  isplitr
  · unfold observedAt
    iexists s
    iframe He
    isplitr
    · ipureintro; exact hv
    iright; iright
    iexists R0
    iframe H0
    ipureintro; exact ⟨hlt, Hemp⟩
  isplitr
  · unfold obsAnchor
    iright
    iexists R0
    iframe H0
    ipureintro; exact hlt
  ipureintro; exact hlt

/-- **Forwarding a put of the observed key**: `v` (of `v0`'s key), alive at `e > R`, is observed
at `e`: the leader if it has `v0`'s create revision and `v0` was the leader at `R` (no key older
is left: `etcdState_create_persist`), re-created otherwise (second case); after an empty prefix,
the third case. -/
theorem anchor_forward (pfx : GoString) (v0 v : EtcdKv) (R e : w64) (s : List EtcdKv)
    (hv : v ∈ s) (hk : v.key = v0.key) (hRe : sint.Z R < sint.Z e) :
    obsAnchor (GF := GF) pfx v0 R ∗ □ etcdState e pfx s ⊢ observedAt pfx v e := by
  iintro ⟨#HA, #He⟩
  unfold obsAnchor
  icases HA with (⟨%s0, #Hs0, %Hl⟩ | ⟨%R0, #H0, %HR0⟩)
  · ihave %Hrevs := etcdState_revs R pfx s0 $$ Hs0
    ihave %Hp := etcdState_create_persist e R pfx s s0 $$ [$He $Hs0]
    have hc0R : sint.Z v0.createRev ≤ sint.Z R := by
      have := Hrevs v0 Hl.1; omega
    have hmin : ∀ w ∈ s, sint.Z v0.createRev ≤ sint.Z w.createRev := by
      intro w hw
      refine Int.not_lt.1 fun hlt => ?_
      obtain ⟨w', hw', -, hwc⟩ := Hp w hw (by omega) (by omega)
      have := Hl.2 w' hw'
      rw [hwc] at this; omega
    unfold observedAt
    iexists s
    iframe He
    isplitr
    · ipureintro; exact hv
    by_cases hc : v.createRev = v0.createRev
    · ileft
      ipureintro
      intro w hw; rw [hc]; exact hmin w hw
    · iright; ileft
      iexists v0.createRev, R
      isplitr
      · unfold lockedAt
        iexists s0
        iframe Hs0
        ipureintro; rw [hk]; exact Hl.locked
      ipureintro
      refine ⟨hRe, ?_, hmin⟩
      have h1 := hmin v hv
      have h2 : sint.Z v.createRev ≠ sint.Z v0.createRev := fun h' => hc (by word)
      omega
  · ihave %Hemp := empty_after pfx R0 e s (by omega) $$ [$H0 $He]
    unfold observedAt
    iexists s
    iframe He
    isplitr
    · ipureintro; exact hv
    iright; iright
    iexists R0
    iframe H0
    ipureintro; exact ⟨by omega, Hemp⟩

/-- The index facts of the list after appending the next response's revision. -/
theorem obs_append_idx (L : List w64) (Rl R : w64) (n : Nat)
    (hL : L.length = n + 1 ∧ L.getLast? = some Rl) :
    (L ++ [R])[n]? = some Rl ∧ (L ++ [R])[n + 1]? = some R := by
  constructor
  · rw [List.getElem?_append_left (by omega), ← hL.2, List.getLast?_eq_getElem?, hL.1]; rfl
  · rw [List.getElem?_append_right (by omega), hL.1]; simp

/-- The `n`-th response, from its index facts. -/
theorem obs_elem (γ : ObserveNames) (pfx : GoString) (n : Nat) (Rp R : w64) (p : Loc)
    (h : sint.Z Rp ≤ sint.Z R) :
    monoListIdxOwn (GF := GF) γ.revs n Rp ∗ monoListIdxOwn γ.revs (n + 1) R ∗ etcdReached R ∗
      observeResp pfx p R ⊢ observeElem γ pfx (n : Int) p := by
  iintro ⟨#H1, #H2, #H3, #H4⟩
  unfold observeElem
  iexists Rp, R
  simp only [Int.toNat_natCast]
  iframe H1 H2 H3 H4
  ipureintro; exact h

/-- An observed revision is positive (a key-value of its state was created at a positive one). -/
theorem observedAt_pos (pfx : GoString) (v : EtcdKv) (R : w64) :
    observedAt (GF := GF) pfx v R ⊢ ⌜0 < sint.Z R⌝ := by
  unfold observedAt
  iintro ⟨%s, #Hs, %Hv, -⟩
  ihave %Hr := etcdState_revs R pfx s $$ Hs
  ipureintro
  have := Hr v Hv
  omega

/-- `Watch(key, WithRev(rev))` is a range watch of the key `key` from `rev` that does not panic. -/
theorem keyWatch_opts (key : GoString) (rev : w64) :
    (opWatchModel key [withRevM rev]).isRangeWatch rev = true ∧
      ¬ opWatchPanics key [withRevM rev] ∧ (opWatchModel key [withRevM rev]).key = key ∧
      (opWatchModel key [withRevM rev]).base.rangeEnd = [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [opWatchModel, opWatchPanics, OpFull.watchPanics, opFold, OpFull.getInit, OpFull.newOp,
    OpModel.zero, withRevM, OpFull.isRangeWatch]

/-- `Watch(pfx, WithRev(rev), WithPrefix())` is a range watch of the prefix from `rev` that does
not panic. -/
theorem prefixWatch_opts (pfx : GoString) (rev : w64) (hp : pfx ≠ []) :
    (opWatchModel pfx [withRevM rev, withPrefixM]).isRangeWatch rev = true ∧
      ¬ opWatchPanics pfx [withRevM rev, withPrefixM] ∧
      (opWatchModel pfx [withRevM rev, withPrefixM]).key = pfx ∧
      (opWatchModel pfx [withRevM rev, withPrefixM]).base.rangeEnd = prefixRangeEnd pfx := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [opWatchModel, opWatchPanics, OpFull.watchPanics, opFold, OpFull.getInit, OpFull.newOp,
    OpModel.zero, withRevM, withPrefixM, OpFull.isRangeWatch, hp]

end anchor

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem Election.observe.wp_proof (wp_Client : Session.Client.spec (GF := GF) (hG := hG))
    (wp_WFC : EtcdGrove.WithFirstCreate.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_Err : WatchResponse.Err.spec (GF := GF) (hG := hG)) :
    Election.observe.spec (GF := GF) (hG := hG) := by
  intro e s γs client id pfx ctx cs ch γ sent L Rl
  wp_start as ⟨#He, #Hctx, #Hcc, #Hch, Hprod, Hauth, #HRl, %HL, %HRl0⟩
  ihave #He' := He
  iunfold isElection at He'
  icases He' with ⟨#Hes, #Hepfx, %Hpfx, #Hsess, #Hcl⟩
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  wp_apply wp_Client s γs client id $$ [$Hpkg $Hsess]
  ihave #Hcl' := Hcl
  iunfold isEtcdMutexClient at Hcl'
  icases Hcl' with ⟨%kv, %wt, %cctx, %ccs, #Hkvf, #Hwf, -, -, #HKV, -, -, #HW⟩
  iunfold isObserveChan at Hch
  ipersist e
  ipersist ch
  ipersist ctx
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave IH : iprop(∃ (sent : List Loc) (L : List w64) (Rl : w64),
      "Hprod" ∷ spscProducer γ.spsc sent ∗ "Hauth" ∷ monoListAuthOwn γ.revs 1 L ∗
      "#HRl" ∷ etcdReached Rl ∗ "%HL" ∷ ⌜L.length = sent.length + 1 ∧ L.getLast? = some Rl⌝ ∗
      "%HRl0" ∷ ⌜0 ≤ sint.Z Rl⌝) $$
      [Hprod Hauth]
  · iexists sent, L, Rl
    simp only [named]
    iframe
    iframe HRl
    ipureintro; exact ⟨HL, HRl0⟩
  iclear HRl
  clear HL HRl0 sent L Rl
  ipersist client
  iunfold isEtcdKV at HKV
  iunfold isEtcdRangeWatcher at HW
  ihave #HchC : isChan ch γ.spsc.chanName Loc $$ []
  · ihave #H := Hch
    unfold isSpsc
    icases H with ⟨$, -⟩
  ihave #Hctx1 := Hctx
  iNamed Hctx1
  wp_for IH
  wp_apply wp_WFC $$ [$Hcv] as %slf ⟨#Hslf, -⟩
  (try wp_auto)
  ihave #HG := HKV $$ %ctx %cs %pfx %slf %(withTopM (W64 2) (W64 1)) %Rl
  wp_apply HG $$ [] as %gresp %gerr #Hgres
  · iframe Hctx Hslf HRl
    ipureintro
    exact ⟨ownerOp_not_panics pfx, ownerOp_t pfx⟩
  iunfold kvGetResult at Hgres
  icases Hgres with (%Hgne | ⟨%Hgnil, %R0, %gm, #HgRev, -, #HR0, %HR0le, Hgr⟩)
  · obtain ⟨e', rfl⟩ : ∃ e', gerr = GoInterface.ok e' := by
      cases gerr with
      | nil => exact absurd rfl Hgne
      | ok e' => exact ⟨e', rfl⟩
    (try wp_auto)
    wp_for_post
    wp_apply wp_spsc_close γ.spsc ch (observeElem γ pfx) (fun _ => iprop(True)) sent
      $$ [$Hch $Hprod]
    (try wp_auto)
    iapply HΦ; itrivial
  subst Hgnil
  obtain ⟨Hrev0, -, HoP⟩ := observe_ownerOp_rev pfx
  have HR0lo : sint.Z Rl ≤ sint.Z R0 := HR0le.1 (observe_ownerOp_rev pfx).2.1
  rw [ite_eq_right (c := (opGetModel pfx (withTopM (W64 2) (W64 1))).isPrefixGet pfx = true)
    (by rw [show opGetModel pfx (withTopM (W64 2) (W64 1)) = ownerOp pfx from rfl, HoP]; simp)]
  unfold getRespRange
  rw [ite_eq_left (show (opGetModel pfx (withTopM (W64 2) (W64 1))).base.rev = W64 0 ∧
      KeyRangeUnder pfx (opGetModel pfx (withTopM (W64 2) (W64 1))).key
        (opGetModel pfx (withTopM (W64 2) (W64 1))).base.rangeEnd from
    ⟨Hrev0, ownerOp_under pfx Hpfx⟩)]
  icases Hgr with ⟨%s0, %gsl, %gps, %gkvs, #Hs0, %Hwf0, #Hgsl, #Hgps, #Hgkvs, %Hgok⟩
  obtain ⟨Hk0, Hk1, Hk01⟩ := ownerOp_kvs' pfx s0 gkvs Hpfx Hwf0 Hgok
  iunfold kvPtrsAt at Hgkvs
  icases Hgkvs with ⟨%Hgl, #Hgkv⟩
  ihave %Hgsl' := ownSlice_len $$ Hgps
  (try wp_auto)
  ipersist resp
  wp_join (Q := fun r => iprop((⌜r = executeVal⌝ ∗ ∃ (kvp hdrp : Loc) (v : EtcdKv) (R : w64),
      "kv" ∷ kv_ptr ↦ kvp ∗ "hdr" ∷ hdr_ptr ↦ hdrp ∗ "%Hhdrp" ∷ ⌜hdrp ≠ null⌝ ∗
      "#HhR" ∷ structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdrp ↦□ R ∗
      "#Hkvp" ∷ kvValAt kvp v ∗ "#Hobs" ∷ observedAt pfx v R ∗ "#Hanc" ∷ obsAnchor pfx v R ∗
      "#HRr" ∷ etcdReached R ∗
      "%HJ" ∷ ⌜pfx <+: v.key ∧ sint.Z Rl ≤ sint.Z R ∧ sint.Z R < 2 ^ 63 - 1⌝) ∨
      ⌜r = returnVal #()⌝)) with [kv hdr]
  · -- the prefix is empty: watch it for the first put
    have Hgk : gkvs = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← Hgl, Hgsl'.1, Hif]; rfl
    have Hs0e := Hk0 Hgk
    subst Hs0e
    -- `Watch` needs `0 ≤ rev`: `R0 ≥ Rl ≥ 0` (the loop keeps `0 ≤ Rl`, from `Observe`'s `lo`)
    have HR0pos : 0 ≤ sint.Z R0 := by omega
    wp_apply context.wp_WithCancel iprop(True) ctx cs $$ [$Hctx $Hcc]
        as %ctxB %γB %cancelB ⟨#HcancelB, #HctxB, #HccB⟩
    ihave #HcancelB' := context.cancel_spec_forget _ _ _ $$ HcancelB
    iunfold getRespRev at HgRev
    icases HgRev with ⟨%ghdr, #Hgh, %Hghnn, #HghR⟩
    (try wp_auto)
    wp_apply wp_WithRev R0 $$ [$Hcv] as %fr #Hfr
    wp_apply wp_WithPrefix $$ [$Hcv] as %fp #Hfp
    wp_apply wp_slice_literal (l := [fr, fp])
    isplitr
    · ipureintro; rfl
    iintro %slo ⟨Hslo, -⟩
    ipersist Hslo
    generalize hsl : slice.mk slo _ _ = optsSl
    ihave #Hopts : optsAt optsSl ([withRevM R0, withPrefixM] : List (OpFull → OpFull)) $$ []
    · iunfold optsAt
      iexists _
      iframe Hslo
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %f' %g %Hf' %Hg
      rcases i with _ | _ | i
      · cases Hf'; cases Hg; iexact Hfr
      · cases Hf'; cases Hg; iexact Hfp
      · simp at Hf'
    obtain ⟨Hw1, Hw2, Hw3, Hw4⟩ := prefixWatch_opts pfx R0 Hpfx
    ihave #HWa := HW $$ %ctxB %({ cs with PDone := iprop(cs.PDone ∨ True), Done_gn := γB })
      %pfx %optsSl %([withRevM R0, withPrefixM] : List (OpFull → OpFull)) %R0
    (try wp_auto)
    wp_apply HWa $$ [] as %wch %γw ⟨#Hwch, Hwcons, #Hcur0⟩
    · iframe HctxB Hopts
      ipureintro
      refine ⟨Hw1, Hw2, HR0pos, ?_⟩
      rw [Hw3, Hw4]; exact keyRangeUnder_prefix pfx Hpfx
    (try wp_auto)
    ihave IHB : iprop(∃ (kvp hdrp : Loc) (rcv : List go_etcd_io.etcd.client.v3.WatchResponse) (c : w64),
        "kv" ∷ kv_ptr ↦ kvp ∗ "hdr" ∷ hdr_ptr ↦ hdrp ∗
        "Hwcons" ∷ spscConsumer γw.spsc rcv ∗ "#Hcur" ∷ monoListIdxOwn γw.cur rcv.length c ∗
        "HJB" ∷ (⌜kvp = null⌝ ∨ ∃ (v : EtcdKv) (R : w64), ⌜hdrp ≠ null⌝ ∗
          structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdrp ↦ R ∗
          kvValAt kvp v ∗ observedAt pfx v R ∗ obsAnchor pfx v R ∗ etcdReached R ∗
          ⌜pfx <+: v.key ∧ sint.Z Rl ≤ sint.Z R ∧ sint.Z R < 2 ^ 63 - 1⌝)) $$ [kv hdr Hwcons]
    · iexists _, _, [], _
      simp only [named]
      iframe
      iframe Hcur0
      ileft; ipureintro; rfl
    wp_for IHB
    by_cases hkn : kvp = null
    rotate_left
    · -- a put was found: `cancel()`, the join
      simp only [hkn, decide_false, Bool.false_eq_true, ↓reduceIte]
      icases HJB with (%Hc | ⟨%v', %R', %Hhn, HhR, #Hkvp, #Hobs, #Hanc, #HRr, %HJ'⟩)
      · exact Hc.elim
      (try wp_auto)
      ipersist HhR
      wp_apply HcancelB'
      · imodintro; itrivial
      (try wp_auto)
      ileft
      isplitr
      · ipureintro; rfl
      iexists kvp, hdrp, v', R'
      simp only [named]
      iframe
      iframe HhR Hkvp Hobs Hanc HRr
      ipureintro; exact ⟨Hhn, HJ'⟩
    subst hkn
    simp only [_root_.decide_true, ↓reduceIte]
    (try wp_auto)
    wp_bind (App (Val (chan.receive _)) _)
    wp_apply wp_spsc_receive γw.spsc wch
      (rangeWatchElem γw pfx (opWatchModel pfx [withRevM R0, withPrefixM]) R0)
      (fun _ => iprop(True)) rcv $$ [$Hwch $Hwcons] as %wv %ok Hrecv
    cases ok
    · -- closed: `cancel()`, return
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hrecv with ⟨-, %Hv⟩
      (try wp_auto)
      wp_apply HcancelB'
      · imodintro; itrivial
      (try wp_auto)
      wp_for_post
      iright; ipureintro; rfl
    simp only [↓reduceIte]
    icases Hrecv with ⟨HP, Hwcons⟩
    (try wp_auto)
    wp_apply wp_Err wr_ptr wv (DFrac.own 1) $$ [$wr] as %werr ⟨wr, %Herr⟩
    obtain ⟨e', rfl⟩ | rfl : (∃ e', werr = GoInterface.ok e') ∨ werr = GoInterface.nil := by
      cases werr with
      | ok e' => exact Or.inl ⟨e', rfl⟩
      | nil => exact Or.inr rfl
    · (try wp_auto)
      wp_apply HcancelB'
      · imodintro; itrivial
      (try wp_auto)
      wp_for_post
      iright; ipureintro; rfl
    (try wp_auto)
    iunfold rangeWatchElem at HP
    icases HP with ⟨%r, %c0, %c', #Hevs, Hhdr, %Hflags, #Hc0, #Hc', #Hok⟩
    simp only [Int.toNat_natCast] at *
    ihave %Hceq := mono_list_idx_agree γw.cur rcv.length c0 c $$ Hc0 Hcur
    subst Hceq
    iunfold rangeWatchRespOk at Hok
    icases Hok with ⟨%Hsort, #Hevok⟩
    iunfold eventsAt at Hevs
    icases Hevs with ⟨%ls, #Hls, %Hlen, #Hev⟩
    (try wp_auto)
    ihave %Hsl := ownSlice_len $$ Hls
    ihave IHR : iprop(∃ (n : w64) (e0 : Loc),
        "i" ∷ i_ptr ↦ n ∗ "ev" ∷ ev_ptr ↦ e0 ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ls.length : Int)⌝ ∗
        "Hhdr" ∷ watchHdrOwn wv.Header' r ∗ "kv" ∷ kv_ptr ↦ null ∗ "hdr" ∷ hdr_ptr ↦ hdrp)
      $$ [i ev Hhdr kv hdr]
    · iexists W64 0, _
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    wp_for IHR
    wp_if_destruct
    · have Hlt : sint.nat n < ls.length := by word
      obtain ⟨l, Hl⟩ : ∃ l, ls[sint.nat n]? = some l := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨ev0, He⟩ : ∃ e, r.events[sint.nat n]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z wv.Events'.len := ⟨Hn.1, by word⟩
      rw [ite_eq_left Hbnd]
      icases ownSlice_elem_acc (sint.Z n) l wv.Events' DFrac.discard ls Hn.1 Hl $$ Hls
        with ⟨#Hle, -⟩
      ihave #He := Hev $$ %(sint.nat n) %l %ev0 %Hl %He
      iunfold eventAt at He
      icases He with ⟨%keySl', #Htyp, #HevKv, -⟩
      ihave #Hevok' := Hevok $$ %(sint.nat n) %ev0 %He
      iunfold rangeWatchEvOk at Hevok'
      icases Hevok' with ⟨%Hek, #Hereach, -, #Hput⟩
      (try wp_auto)
      wp_if_destruct
      · -- the first put: `hdr, kv = wr.Header, ev.Kv`, `hdr.Revision = kv.ModRevision`, break
        ihave Hp := Hput $$ %Hif
        icases Hp with ⟨%v', #Hv'kv, %Hv'k, %s', #Hs', %Hv's⟩
        have Hne : r.events ≠ [] := by intro h; rw [h] at He; simp at He
        iunfold watchHdrOwn at Hhdr
        rw [if_neg Hne]
        icases Hhdr with ⟨%Hhn, Hf⟩
        ihave #Hv'kv' := Hv'kv
        iunfold kvValAt at Hv'kv'
        icases Hv'kv' with ⟨%kS, %vS, -, -, -, #HmR, -, -, -, -⟩
        (try wp_auto)
        wp_for_post
        (try wp_auto)
        wp_for_post
        ihave #Hfp := first_put pfx R0 ev0.rev v' s' Hv's.1 Hek.2.1 $$ [$Hs0 $Hs']
        icases Hfp with ⟨#Hobs', #Hanc', %HR0e⟩
        iframe
        iexists ev0.kv, wv.Header', rcv ++ [wv], c'
        simp only [named, List.length_append, List.length_singleton]
        iframe
        iframe Hc'
        iright
        iexists v', v'.modRev
        iframe Hf
        rw [Hv'k.2]
        iframe Hv'kv Hobs' Hanc' Hereach
        ipureintro
        refine ⟨Hhn, ?_, by omega, Hek.2.2.1⟩
        · rw [Hv'k.1]
          have := Hek.1; rw [Hw3, Hw4] at this
          exact (inRange_prefix pfx ev0.key Hpfx).1 this
      -- not a put: the next event
      wp_for_post
      iframe
      iexists n + W64 1, l
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    -- no put in this response: the next one
    wp_for_post
    iframe
    iexists null, hdrp, rcv ++ [wv], c'
    simp only [named, List.length_append, List.length_singleton]
    iframe
    iframe Hc'
    try (ileft; ipureintro; rfl)
  · -- the get found the leader
    obtain ⟨w, rfl⟩ : ∃ w, gkvs = [w] := by
      rcases Hk01 with h | h
      · exfalso; apply Hif
        subst h
        have : sint.nat gsl.len = 0 := by rw [← Hgsl'.1, Hgl]; rfl
        word
      · exact h
    obtain ⟨kp, rfl⟩ : ∃ kp, gps = [kp] := by
      match gps, Hgl with
      | [kp], _ => exact ⟨kp, rfl⟩
    have Hlead := Hk1 w rfl
    iunfold getRespRev at HgRev
    icases HgRev with ⟨%ghdr, #Hgh, %Hghnn, #HghR⟩
    (try wp_auto)
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z gsl.len by
      simp at Hgsl'; word)]
    icases ownSlice_elem_acc (sint.Z (W64 0)) kp gsl DFrac.discard [kp] (by word) (by simp)
      $$ Hgps with ⟨#Hkpe, -⟩
    (try wp_auto)
    ihave #Hkv := Hgkv $$ %0 %kp %w %rfl %rfl
    ileft
    isplitr
    · ipureintro; rfl
    iexists kp, ghdr, w, R0
    simp only [named]
    iframe
    iframe HghR Hkv HR0
    ihave #Hlk : leaderKvAt (GF := GF) pfx w R0 $$ []
    · unfold leaderKvAt; iexists s0; iframe Hs0; ipureintro; exact Hlead
    isplitr
    · ipureintro; exact Hghnn
    isplitr
    · iapply leaderKvAt_observedAt $$ Hlk
    isplitr
    · unfold obsAnchor; ileft; iexists s0; iframe Hs0; ipureintro; exact Hlead
    ipureintro
    exact ⟨Hwf0.2 w Hlead.1, HR0lo, HR0le.2⟩
  iintro Hr
  icases Hr with (⟨%Hr, %kvp, %hdrp, %v, %R, Hj⟩ | %Hr) <;> subst Hr
  rotate_left
  · (try wp_auto)
    wp_for_post
    wp_apply wp_spsc_close γ.spsc ch (observeElem γ pfx) (fun _ => iprop(True)) sent
      $$ [$Hch $Hprod]
    (try wp_auto)
    iapply HΦ; itrivial
  iNamed Hj
  (try wp_auto)
  wp_apply wp_slice_literal (l := [kvp])
  isplitr
  · ipureintro; rfl
  iintro %slk ⟨Hslk, -⟩
  ipersist Hslk
  (try wp_auto)
  iStructNamedPrefix «$v0» "F"
  iclear Fstate FMore FCount FunknownFields FsizeCache F_
  ipersist FHeader
  ipersist FKvs
  ihave #Hresp : observeResp (GF := GF) pfx «$v0_ptr» R $$ []
  · unfold observeResp getRespOneKv
    iexists hdrp, R, kvp, v
    iframe FHeader HhR Hkvp Hobs
    isplitr
    · ipureintro; exact Hhdrp
    iexists _
    iframe FKvs Hslk
  imod monoListAuthOwn_update_app (GF := GF) [R] $$ Hauth with ⟨Hauth, #Hlb⟩
  ihave #Hi1 := monoListIdxOwn_get sent.length Rl (obs_append_idx L Rl R sent.length HL).1 $$ Hlb
  ihave #Hi2 := monoListIdxOwn_get (sent.length + 1) R
    (obs_append_idx L Rl R sent.length HL).2 $$ Hlb
  ihave #Hel := obs_elem γ pfx sent.length Rl R «$v0_ptr» HJ.2.1 $$ [$Hi1 $Hi2 $HRr $Hresp]
  wp_apply +noauto HDone as %dch %dγ #Hdone
  wp_auto_lc 3
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `ch <- resp`
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ.spsc.chanName,
      «$v0_ptr»
    isplit
    · ipureintro; exact ⟨rfl, rfl⟩
    isplit
    · iexact HchC
    iapply spsc_send_au γ.spsc ch _ _ sent «$v0_ptr» _ $$ Hch [$Hlc1 $Hlc2 $Hlc3] [Hprod]
    · iframe Hprod Hel
    inext
    iintro Hprod
    (try wp_auto)
    wp_apply context.wp_WithCancel iprop(True) ctx cs $$ [$Hctx $Hcc]
        as %ctx' %γ' %cancel ⟨#Hcancel, #Hctx', #Hcc'⟩
    ihave #Hcancel' := context.cancel_spec_forget _ _ _ $$ Hcancel
    ihave #Hctx2 := Hctx'
    iNamedPrefix Hctx2 "C"
    (try wp_auto)
    ihave #Hkvp' := Hkvp
    iunfold kvValAt at Hkvp'
    icases Hkvp' with ⟨%keySl, %valSl, #HkK, #HkKs, -, -, -, -, -, -⟩
    (try wp_auto)
    wp_apply wp_bytes_to_string keySl v.key DFrac.discard $$ [$HkKs] as -
    (try wp_auto)
    ihave %HRpos := observedAt_pos pfx v R $$ Hobs
    wp_apply wp_WithRev (R + W64 1) $$ [$Hcv] as %fr #Hfr
    wp_apply wp_slice_literal (l := [fr])
    isplitr
    · ipureintro; rfl
    iintro %slo ⟨Hslo, -⟩
    ipersist Hslo
    generalize hsl : slice.mk slo _ _ = optsSl
    ihave #Hopts : optsAt optsSl ([withRevM (R + W64 1)] : List (OpFull → OpFull)) $$ []
    · iunfold optsAt
      iexists _
      iframe Hslo
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %f' %g %Hf' %Hg
      rcases i with _ | i
      · cases Hf'; cases Hg; iexact Hfr
      · simp at Hf'
    obtain ⟨Hw1, Hw2, Hw3, Hw4⟩ := keyWatch_opts v.key (R + W64 1)
    ihave #HWa := HW $$ %ctx' %({ cs with PDone := iprop(cs.PDone ∨ True), Done_gn := γ' })
      %v.key %optsSl %([withRevM (R + W64 1)] : List (OpFull → OpFull)) %(R + W64 1)
    (try wp_auto)
    wp_apply HWa $$ [] as %wch %γw ⟨#Hwch, Hwcons, #Hcur0⟩
    · iframe Hctx' Hopts
      ipureintro
      refine ⟨Hw1, Hw2, by word, ?_⟩
      rw [Hw3, Hw4]; exact keyRangeUnder_key pfx v.key HJ.1
    (try wp_auto)
    have HcR : R + W64 1 - W64 1 = R := by word
    rw [HcR]
    ihave IH2 : iprop(∃ (sent : List Loc) (L : List w64) (Rl c : w64)
        (rcv : List go_etcd_io.etcd.client.v3.WatchResponse) (kd : Bool),
        "Hprod" ∷ spscProducer γ.spsc sent ∗ "Hauth" ∷ monoListAuthOwn γ.revs 1 L ∗
        "#HRl" ∷ etcdReached Rl ∗ "%HL" ∷ ⌜L.length = sent.length + 1 ∧ L.getLast? = some Rl⌝ ∗
        "Hwcons" ∷ spscConsumer γw.spsc rcv ∗ "#Hcur" ∷ monoListIdxOwn γw.cur rcv.length c ∗
        "%Hc" ∷ ⌜sint.Z Rl ≤ sint.Z c ∧ sint.Z R ≤ sint.Z c⌝ ∗ "%HRl0" ∷ ⌜0 ≤ sint.Z Rl⌝ ∗
        "keyDeleted" ∷ keyDeleted_ptr ↦ kd) $$ [Hprod Hauth Hwcons keyDeleted]
    · iexists sent ++ [«$v0_ptr»], L ++ [R], R, R, [], false
      simp only [named]
      iframe
      iframe HRr Hcur0
      ipureintro
      refine ⟨⟨by simp [HL.1], by simp⟩, ⟨Int.le_refl _, Int.le_refl _⟩, by omega⟩
    iclear HRl
    clear HRl0
    wp_for IH2
    cases kd
    · simp only [Bool.not_false, _root_.decide_true, ↓reduceIte]
      (try wp_auto)
      wp_bind (App (Val (chan.receive _)) _)
      wp_apply wp_spsc_receive γw.spsc wch
        (rangeWatchElem γw pfx (opWatchModel v.key [withRevM (R + W64 1)]) (R + W64 1))
        (fun _ => iprop(True)) rcv $$ [$Hwch $Hwcons] as %wv %ok Hrecv
      cases ok
      · -- the watch closed: `cancel()`, return
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hrecv with ⟨-, %Hv⟩
        (try wp_auto)
        wp_apply Hcancel'
        · imodintro; itrivial
        (try wp_auto)
        wp_for_post
        wp_for_post
        wp_apply wp_spsc_close γ.spsc ch (observeElem γ pfx) (fun _ => iprop(True)) sent
          $$ [$Hch $Hprod]
        (try wp_auto)
        iapply HΦ; itrivial
      simp only [↓reduceIte]
      icases Hrecv with ⟨HP, Hwcons⟩
      iunfold rangeWatchElem at HP
      icases HP with ⟨%r, %c0, %c', #Hevs, Hhdr, %Hflags, #Hc0, #Hc', #Hok⟩
      simp only [Int.toNat_natCast] at *
      ihave %Hceq := mono_list_idx_agree γw.cur rcv.length c0 c $$ Hc0 Hcur
      subst Hceq
      iunfold rangeWatchRespOk at Hok
      icases Hok with ⟨%Hsort, #Hevok⟩
      ihave Hhdr2 : iprop(|==> □ (⌜r.events = []⌝ ∨ (⌜wv.Header' ≠ null⌝ ∗
          structFieldRef etcdserverpb.ResponseHeader go!"Revision" wv.Header' ↦□ r.hdrRev))) $$ [Hhdr]
      · by_cases hev : r.events = []
        · imodintro; ileft; ipureintro; exact hev
        · iright
          unfold watchHdrOwn
          simp only [hev, ↓reduceIte]
          icases Hhdr with ⟨%Hn, Hf⟩
          ipersist Hf
          imodintro
          iframe Hf
          ipureintro; exact Hn
      imod Hhdr2 with #Hhdr'
      iunfold eventsAt at Hevs
      icases Hevs with ⟨%ls, #Hls, %Hlen, #Hev⟩
      (try wp_auto)
      ihave %Hsl := ownSlice_len $$ Hls
      obtain ⟨Hcc', Hle'⟩ := evs_pos r.events c0 Hsort.1 Hsort.2.1
      rw [← Hsort.2.2] at Hcc' Hle'
      ihave IH3 : iprop(∃ (n : w64) (e0 : Loc) (sent : List Loc) (L : List w64) (Rl : w64),
          "i" ∷ i_ptr ↦ n ∗ "ev" ∷ ev_ptr ↦ e0 ∗
          "Hprod" ∷ spscProducer γ.spsc sent ∗ "Hauth" ∷ monoListAuthOwn γ.revs 1 L ∗
          "#HRl" ∷ etcdReached Rl ∗ "%HL" ∷ ⌜L.length = sent.length + 1 ∧ L.getLast? = some Rl⌝ ∗
          "%HRl0" ∷ ⌜0 ≤ sint.Z Rl⌝ ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ls.length : Int)⌝ ∗
          "%Hord" ∷ ⌜sint.Z Rl ≤ sint.Z c' ∧ ∀ (k : Nat) (e : EvModel), sint.nat n ≤ k →
            r.events[k]? = some e → sint.Z Rl ≤ sint.Z e.rev⌝ ∗
          "keyDeleted" ∷ keyDeleted_ptr ↦ false) $$ [i ev Hprod Hauth keyDeleted]
      · iexists W64 0, _, sent, L, Rl
        simp only [named]
        iframe
        iframe HRl
        ipureintro
        refine ⟨HL, HRl0, ⟨by word, by word⟩, Int.le_trans Hc.1 Hcc', fun k e _ he => ?_⟩
        have := Hsort.2.1 e (List.mem_of_getElem? he)
        have := Hc.1
        omega
      iclear HRl
      clear HRl0
      wp_for IH3
      wp_if_destruct
      · have Hlt : sint.nat n < ls.length := by word
        obtain ⟨l, Hl⟩ : ∃ l, ls[sint.nat n]? = some l := ⟨_, List.getElem?_eq_getElem Hlt⟩
        obtain ⟨ev0, He⟩ : ∃ e, r.events[sint.nat n]? = some e :=
          ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
        have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z wv.Events'.len := ⟨Hn.1, by word⟩
        rw [ite_eq_left Hbnd]
        icases ownSlice_elem_acc (sint.Z n) l wv.Events' DFrac.discard ls Hn.1 Hl $$ Hls
          with ⟨#Hle, -⟩
        ihave #He := Hev $$ %(sint.nat n) %l %ev0 %Hl %He
        iunfold eventAt at He
        icases He with ⟨%keySl', #Htyp, #HevKv, -⟩
        ihave #Hevok' := Hevok $$ %(sint.nat n) %ev0 %He
        iunfold rangeWatchEvOk at Hevok'
        icases Hevok' with ⟨%Hek, #Hereach, -, #Hput⟩
        (try wp_auto)
        wp_if_destruct
        · -- a delete: `keyDeleted = true`, break
          wp_for_post
          (try wp_auto)
          wp_for_post
          iframe
          iexists sent, L, Rl, c', rcv ++ [wv], true
          simp only [named, List.length_append, List.length_singleton]
          iframe
          iframe HRl Hc'
          ipureintro
          exact ⟨HL, ⟨Hord.1, Int.le_trans Hc.2 Hcc'⟩, HRl0⟩
        -- not a delete: forward the event's key-value
        -- not a delete, so a put (`rangeWatchEvOk`: an event is one or the other)
        have Htyp0 : ev0.typ = W32 0 := by
          rcases Hek.2.2.2 with h | h
          · exact h
          · exact absurd h (by assumption)
        ihave Hp := Hput $$ %Htyp0
        icases Hp with ⟨%v', #Hv'kv, %Hv'k, %s', #Hs', %Hv's⟩
        have Hek' : ev0.key = v.key := by
          have := Hek.1; rw [Hw3, Hw4] at this; simpa [inRange] using this
        have HRe : sint.Z R < sint.Z ev0.rev := by
          have := Hek.2.1; have : sint.Z (R + W64 1) = sint.Z R + 1 := by word
          omega
        ihave #Hobs' := anchor_forward pfx v v' R ev0.rev s' Hv's.1 (by rw [Hv'k.1, Hek'])
          HRe $$ [$Hanc $Hs']
        icases Hhdr' with (%Hemp | ⟨%Hhn, #HhR'⟩)
        · rw [Hemp] at He; simp at He
        wp_apply wp_slice_literal (l := [ev0.kv])
        isplitr
        · ipureintro; rfl
        iintro %slk' ⟨Hslk', -⟩
        ipersist Hslk'
        (try wp_auto)
        iStructNamedPrefix «$v0» "G"
        iclear Gstate GMore GCount GunknownFields GsizeCache G_
        ipersist GHeader
        ipersist GKvs
        ihave #Hresp' : observeResp (GF := GF) pfx «$v0_ptr» ev0.rev $$ []
        · unfold observeResp getRespOneKv
          iexists wv.Header', r.hdrRev, ev0.kv, v'
          iframe GHeader HhR' Hv'kv Hobs'
          isplitr
          · ipureintro; exact Hhn
          iexists _
          iframe GKvs Hslk'
        have HRle : sint.Z Rl ≤ sint.Z ev0.rev := Hord.2 (sint.nat n) ev0 (Nat.le_refl _) He
        imod monoListAuthOwn_update_app (GF := GF) [ev0.rev] $$ Hauth with ⟨Hauth, #Hlb⟩
        ihave #Hi1 := monoListIdxOwn_get sent.length Rl
          (obs_append_idx L Rl ev0.rev sent.length HL).1 $$ Hlb
        ihave #Hi2 := monoListIdxOwn_get (sent.length + 1) ev0.rev
          (obs_append_idx L Rl ev0.rev sent.length HL).2 $$ Hlb
        ihave #Hel := obs_elem γ pfx sent.length Rl ev0.rev «$v0_ptr» HRle
          $$ [$Hi1 $Hi2 $Hereach $Hresp']
        wp_apply +noauto CHDone as %dch' %dγ' #Hdone'
        wp_auto_lc 3
        wp_apply_core chan.wp_select_blocking
        iapply BigAndL.bigAndL_cons.2
        isplit
        · -- `ch <- resp`: the next event
          simp only [chan.blockingClausePre]
          iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, ch,
            γ.spsc.chanName, «$v0_ptr»
          isplit
          · ipureintro; exact ⟨rfl, rfl⟩
          isplit
          · iexact HchC
          iapply spsc_send_au γ.spsc ch _ _ sent «$v0_ptr» _ $$ Hch [$Hlc1 $Hlc2 $Hlc3] [Hprod]
          · iframe Hprod Hel
          inext
          iintro Hprod
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, l, sent ++ [«$v0_ptr»], L ++ [ev0.rev], ev0.rev
          simp only [named]
          iframe
          iframe Hereach
          ipureintro
          refine ⟨⟨by simp [HL.1], by simp⟩,
            by have := Hord.2 (sint.nat n) ev0 (Nat.le_refl _) He; omega,
            ⟨by word, by word⟩, Hle' (sint.nat n) ev0 He, ?_⟩
          intro k e' hk he'
          exact evs_sorted_le Hsort.1 He he' (by word)
        iapply BigAndL.bigAndL_cons.2
        isplit
        · -- `<-cctx.Done()`: `cancel()`, return
          simp only [chan.blockingClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch', dγ'
          isplit
          · ipureintro; rfl
          isplit
          · iapply context.isContextDone_is_chan $$ Hdone'
          iapply context.isContextDone_receive _ _ _ _ $$ Hdone'
          iintro -
          (try wp_auto)
          wp_apply Hcancel'
          · imodintro; itrivial
          (try wp_auto)
          wp_for_post
          wp_for_post
          wp_for_post
          wp_apply wp_spsc_close γ.spsc ch (observeElem γ pfx) (fun _ => iprop(True)) sent
            $$ [$Hch $Hprod]
          (try wp_auto)
          iapply HΦ; itrivial
        iapply BigAndL.bigAndL_nil.2
        itrivial
      -- the events are done: the next response
      wp_for_post
      iframe
      iexists sent, L, Rl, c', rcv ++ [wv], false
      simp only [named, List.length_append, List.length_singleton]
      iframe
      iframe HRl Hc'
      ipureintro
      exact ⟨HL, ⟨Hord.1, Int.le_trans Hc.2 Hcc'⟩, HRl0⟩
    · simp
      rw [if_neg (fun h => Bool.false_ne_true (go.IntoValInj.intoVal_inj h))]
      (try wp_auto)
      wp_apply Hcancel'
      · imodintro; itrivial
      (try wp_auto)
      wp_for_post
      iframe
      iexists sent, L, Rl
      simp only [named]
      iframe
      iframe HRl
      ipureintro; exact ⟨HL, HRl0⟩
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-ctx.Done()`: return
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, dγ
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro -
    (try wp_auto)
    wp_for_post
    wp_apply wp_spsc_close γ.spsc ch (observeElem γ pfx) (fun _ => iprop(True)) sent
      $$ [$Hch $Hprod]
    (try wp_auto)
    iapply HΦ; itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end concurrency
end EtcdGrove
end Perennial
