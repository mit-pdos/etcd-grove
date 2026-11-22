/-
Lean-first (no Rocq counterpart).

The proof of `(*Replay).validateGet`, on the accepting run: a consistent get, or a too-large
response, or the range over the states finds one from the requested resource version on whose `get`
(with its prefix, or without) is the response; the loop's invariant records that no state visited so
far matched, so falling out of it contradicts `rreplayGetL R x out = true`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay__validateGet
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.GetReadConsistency
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__get
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__ParseResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.IsTooLargeResourceVersion
public import Spec.reflect.DeepEqualK8s

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [errors_sem : _root_.Perennial.errors.Assumptions]
variable [storage_sem : k8s_io.apiserver.pkg.storage.Assumptions]
variable [apierrors_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

/-- The model's `get` on a state at or past the requested resource version answers a deep error
when the key is one `PrepareKey` accepts. -/
theorem rgetL_deep (x : Input) (m : RM) (rv : w64) (hk : keyOkL (storeKeyL x.Key') = true)
    (hp : parseRVD x.MinRV' = some rv) (hle : uint.nat rv ≤ uint.nat m.rv) :
    deepErrE (rgetL x m).err := by
  unfold rgetL
  simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hp, show ¬ uint.nat m.rv < uint.nat rv by omega]
  split
  · split <;> trivial
  · trivial

theorem modelVal_pfx (il rl : Loc) (m : RM) :
    ({ modelVal il rl m with Prefix' := [] } : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model) =
      modelVal il rl { m with pfx := [] } := rfl

theorem Replay.validateGet.wp_proof
    (wp_DE : reflect.DeepEqual.spec_k8s (GF := GF) (hG := hG))
    (wp_GRC : GetReadConsistency.spec (GF := GF) (hG := hG))
    (wp_get : Model.get.spec (GF := GF) (hG := hG))
    (wp_PRV : k8s_etcd3.versioner.ParseResourceVersion.spec (GF := GF) (hG := hG))
    (wp_IsTooLarge : storage.IsTooLargeResourceVersion.spec (GF := GF) (hG := hG))
    (wp_Unwrap : storage.StorageError.Unwrap.spec (GF := GF) (hG := hG)) :
    Replay.validateGet.spec (GF := GF) (hG := hG) := by
  intro rp R r ro x out h4 h0 h1 h2 hpre hkey hok
  wp_start as ⟨#HR, #Hreq, #Hresp⟩
  unfold replayAt
  icases HR with ⟨#Hdrv, %sm, %M, %csl, %cvs, #Hrp, #Hsm, %HMs, %HMrv, %HMch, #HMm, #Hcsl, #Hcvs⟩
  iStructNamed Hrp
  unfold reqRep
  simp only [h4, h0, h1, h2, ↓reduceIte]
  icases Hreq with %Hreq
  obtain ⟨hop, hk, hrv, hinf⟩ := Hreq
  ihave #Hresp0 := Hresp
  unfold respRep
  icases Hresp with ⟨#Ho, #He⟩
  wp_auto
  wp_apply (wp_GRC _)
  rw [hrv]
  unfold rreplayGetL at hok
  by_cases hmin : x.MinRV' = []
  case pos =>
    simp only [hmin, ↓reduceIte, rconsStr, _root_.decide_true]
    wp_auto
    iapply HΦ; ipureintro; rfl
  simp only [hmin, ↓reduceIte] at hok
  simp (config := { decide := true }) only [hmin, ↓reduceIte, rconsStr]
  wp_auto
  obtain ⟨_, hparse, -, hflat, -, -⟩ := hpre
  obtain ⟨rv0, hp⟩ := Option.isSome_iff_exists.1 hparse
  rw [hrv]
  wp_apply (wp_PRV x.MinRV') as %n %perr Hpr
  rw [hp]
  icases Hpr with %Hpr
  obtain ⟨rfl, rfl⟩ := Hpr
  rw [hp] at hok
  simp only at hok
  wp_auto
  ihave ⟨%w, #Hw, %hw⟩ := errRep_apiErrAt wp_Unwrap _ out.err hflat $$ He
  wp_apply (wp_IsTooLarge _ w) $$ [Hw]
  · iexact Hw
  rw [hw]
  cases htl : isTooLargeE out.err
  case true =>
    wp_auto
    iapply HΦ; ipureintro; rfl
  rw [htl, Bool.false_or] at hok
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (keys : List w64) (j : Int) =>
      iprop(∃ (kv : w64) (sv : Loc),
      "HΦ" ∷ (∀ err, ⌜err = GoInterface.nil⌝ -∗ Φ #err) ∗ "«$res0»" ∷ «$res0_ptr» ↦ GoInterface.nil ∗
      "resp" ∷ resp_ptr ↦ ro ∗ "req" ∷ req_ptr ↦ r ∗ "opts" ∷ opts_ptr ↦ r.Get'.Options' ∗
      "reqRV" ∷ reqRV_ptr ↦ n ∗ "state" ∷ state_ptr ↦ sv ∗ "rv" ∷ rv_ptr ↦ kv ∗ "%Hj" ∷ ⌜0 ≤ j⌝ ∗
      "%Hno" ∷ ⌜∀ k ∈ keys.take j.toNat, ∀ st, R.states !! k = some st → uint.nat n ≤ uint.nat k →
        (respEqL (rgetL x st) out || respEqL (rgetL x { st with pfx := [] }) out) = false⌝))
    $$ Hsm
  iintro %keys ⟨%Hk, %Hkl, %Hknd⟩
  isplitl [HΦ «$res0» resp req opts reqRV state rv]
  · iexists _, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨Int.le_refl _, ?_⟩
    intro k hk; simp at hk
  isplitr
  · imodintro
    iintro %j %key %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    wp_auto
    have hj1 : (j + 1).toNat = j.toNat + 1 := by omega
    obtain ⟨st, hst⟩ : ∃ st, R.states !! key = some st := by
      have := HMs key
      rw [Hv] at this
      cases h : R.states !! key with
      | none => rw [h] at this; cases this
      | some st => exact ⟨st, rfl⟩
    wp_if_destruct
    · unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iexists _, _
      simp only [named]
      iframe
      ipureintro
      refine ⟨by omega, ?_⟩
      intro k hk st' hst' hle
      rw [hj1, mem_take_succ_iff Hkey] at hk
      rcases hk with hk | rfl
      · exact Hno k hk st' hst' hle
      · exfalso; word
    ihave ⟨%m, %hm, #Hq⟩ := BigSepM.bigSepM_lookup (Φ := fun rv mp =>
      iprop(∃ m, ⌜R.states !! rv = some m⌝ ∗ modelAt (GF := GF) mp m)) Hv $$ HMm
    rw [hst] at hm
    cases hm
    ihave #Hq0 := Hq
    unfold modelAt modelRep
    icases Hq with ⟨-, %il, %rl, %MI, #Hmv, #Hil, #Hit, #Hrl⟩
    wp_auto
    rw [modelVal_pfx il rl st]
    ipersist stateWithoutPrefix
    have hle : uint.nat n ≤ uint.nat key := by word
    have hd1 : deepErrE (rgetL x st).err := rgetL_deep x st n hkey hp (by rw [HMrv key st hst]; exact hle)
    have hd2 : deepErrE (rgetL x { st with pfx := [] }).err := rgetL_deep x _ n hkey hp (by rw [HMrv key st hst]; exact hle)
    rw [hk]
    wp_apply (wp_get v st x r.Get'.Options' hrv hinf) $$ [] as %re1 #Hre1
    · iframe #
      unfold modelAt modelRep
      iexact Hq0
    unfold respRep
    icases Hre1 with ⟨#Ho1, #He1⟩
    wp_apply (wp_DeepEqual_resp wp_DE re1.Object' re1.Err' ro.Object' ro.Err' (rgetL x st).obj out.obj
      (rgetL x st).err out.err hd1 hflat) $$ []
    · iframe Ho1 He1 Ho He
    rw [show ({ obj := (rgetL x st).obj, err := (rgetL x st).err } : RResp) = rgetL x st from rfl,
      show ({ obj := out.obj, err := out.err } : RResp) = out from rfl]
    cases hb1 : respEqL (rgetL x st) out
    case true =>
      wp_auto
      unfold forMapPostcondition
      iright; iright; iright; ileft
      iexists _
      isplitr
      · ipureintro; rfl
      iintro -
      wp_auto
      iapply HΦ; ipureintro; rfl
    wp_auto
    rw [hk]
    wp_apply (wp_get stateWithoutPrefix_ptr { st with pfx := [] } x r.Get'.Options' hrv hinf) $$ []
      as %re2 #Hre2
    · iframe #
      unfold modelAt modelRep
      iframe #
    unfold respRep
    icases Hre2 with ⟨#Ho2, #He2⟩
    wp_apply (wp_DeepEqual_resp wp_DE re2.Object' re2.Err' ro.Object' ro.Err'
      (rgetL x { st with pfx := [] }).obj out.obj (rgetL x { st with pfx := [] }).err out.err hd2 hflat) $$ []
    · iframe Ho2 He2 Ho He
    rw [show ({ obj := (rgetL x { st with pfx := [] }).obj, err := (rgetL x { st with pfx := [] }).err } : RResp) =
        rgetL x { st with pfx := [] } from rfl,
      show ({ obj := out.obj, err := out.err } : RResp) = out from rfl]
    cases hb2 : respEqL (rgetL x { st with pfx := [] }) out
    case true =>
      wp_auto
      unfold forMapPostcondition
      iright; iright; iright; ileft
      iexists _
      isplitr
      · ipureintro; rfl
      iintro -
      wp_auto
      iapply HΦ; ipureintro; rfl
    wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists _, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨by omega, ?_⟩
    intro k hk' st' hst' hle'
    rw [hj1, mem_take_succ_iff Hkey] at hk'
    rcases hk' with hk' | rfl
    · exact Hno k hk' st' hst' hle'
    · rw [hst] at hst'; cases hst'; rw [hb1, hb2]
  iintro HP -
  iNamed HP
  exfalso
  obtain ⟨⟨k, st⟩, hmem, hmatch⟩ := List.any_eq_true.1 hok
  rw [GMap.mem_toList] at hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hmatch
  have hkM : (M !! k).isSome = true := by rw [HMs k, hmem]; rfl
  have hkk : k ∈ keys := (Hk k).2 hkM
  rw [show (GMap.size M : Int).toNat = keys.length by omega, List.take_length] at Hno
  have := Hno k hkk st hmem hmatch.1
  rw [hmatch.2] at this
  cases this

end proof

end k8s_correctness
end EtcdGrove
end Perennial
