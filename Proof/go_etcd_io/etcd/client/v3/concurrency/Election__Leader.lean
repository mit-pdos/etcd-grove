/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Leader.lean`. Lean-first (no Rocq
counterpart).

The get `Get(pfx, WithFirstCreate()...)` is the mutex's owner get (`ownerOp`): on a state with keys
it lists exactly one, the first created (`ownerOp_kvs_cases`), on an empty one nothing.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Leader
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Spec.go_etcd_io.etcd.client.v3.WithFirstCreate

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

/-- **The owner get** (`OpGet(pfx, WithFirstCreate()...)`): nothing on an empty state, otherwise
one key-value, the leader. -/
theorem ownerOp_kvs_cases (pfx : GoString) (s kvs : List EtcdKv) (hp : pfx ≠ [])
    (hwf : EtcdStateWf pfx s) (h : rangeKvsOk (ownerOp pfx) (rangeSel s (ownerOp pfx)) kvs) :
    (kvs = [] ∧ s = []) ∨ ∃ w, kvs = [w] ∧ LeaderKvState w s := by
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
    left
    refine ⟨by simp [hc], ?_⟩
    exact List.eq_nil_of_subset_nil (fun x hx => hperm.symm.subset hx) |>.trans rfl
  | cons w l' =>
    right
    refine ⟨w, by simp [hc, hl, hko], hperm.subset (by simp), ?_⟩
    intro v hv
    rcases List.mem_cons.1 (hperm.symm.subset hv) with rfl | hv'
    · exact Int.le_refl _
    · have := (List.pairwise_cons.1 hsorted).1 v hv'; simpa [kvLeBy] using this

theorem ownerOp_isPrefixGet (pfx : GoString) : (ownerOp pfx).isPrefixGet pfx = false := by
  by_cases h : pfx = [] <;> simp [ownerOp, opGetModel, opFold, withTopM, withPrefixM, withSortM,
    withLimitM, OpFull.getInit, OpFull.newOp, OpModel.zero, h, OpFull.isPrefixGet]

theorem ownerOp_rev (pfx : GoString) : (ownerOp pfx).base.rev = W64 0 ∧
    (ownerOp pfx).base.serializable = false := by
  by_cases h : pfx = [] <;> simp [ownerOp, opGetModel, opFold, withTopM, withPrefixM, withSortM,
    withLimitM, OpFull.getInit, OpFull.newOp, OpModel.zero, h]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Election.Leader.wp_proof (hCl : Session.Client.spec (GF := GF) (hG := hG))
    (hWFC : EtcdGrove.WithFirstCreate.spec (GF := GF) (hG := hG)) :
    Election.Leader.spec (GF := GF) (hG := hG) := by
  intro e s γ client id pfx ctx cs lo
  wp_start as ⟨#He, #Hctx, #Hlo⟩
  ihave #He' := He
  iunfold isElection at He'
  icases He' with ⟨#Hes, #Hepfx, %Hpfx, #Hsess, #Hcl⟩
  wp_auto
  wp_apply hCl s γ client id $$ [$Hpkg $Hsess]
  iunfold isEtcdMutexClient at Hcl
  icases Hcl with ⟨%kv, %wt, %cctx, %ccs, #HKVf, -, -, -, #HKV, -, -, -⟩
  (try wp_auto)
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_apply hWFC $$ [$Hcv] as %slf ⟨#Hslf, -⟩
  (try wp_auto)
  iunfold isEtcdKV at HKV
  ihave #HG := HKV $$ %ctx %cs %pfx %slf %(withTopM (W64 2) (W64 1)) %lo
  wp_apply HG $$ [] as %gresp %gerr #Hgres
  · iframe Hctx Hslf Hlo
    ipureintro
    exact ⟨ownerOp_not_panics pfx, ownerOp_t pfx⟩
  iunfold kvGetResult at Hgres
  icases Hgres with (%Hgne | ⟨%Hgnil, %R, %gm, #HgRev, -, #HRR, %HRle, Hgr⟩)
  · obtain ⟨g, rfl⟩ : ∃ g, gerr = GoInterface.ok g := by
      cases gerr with
      | nil => exact absurd rfl Hgne
      | ok g => exact ⟨g, rfl⟩
    wp_auto
    iapply HΦ
    iright; iright
    ipureintro; exact ⟨rfl, Hgne⟩
  subst Hgnil
  have HoP : (opGetModel pfx (withTopM (W64 2) (W64 1))).isPrefixGet pfx = false :=
    ownerOp_isPrefixGet pfx
  rw [ite_eq_right (c := (opGetModel pfx (withTopM (W64 2) (W64 1))).isPrefixGet pfx = true)
    (by rw [HoP]; simp)]
  have HoR := ownerOp_rev pfx
  have HlR : sint.Z lo ≤ sint.Z R := HRle.1 HoR.2
  unfold getRespRange
  rw [ite_eq_left (show (opGetModel pfx (withTopM (W64 2) (W64 1))).base.rev = W64 0 ∧
      KeyRangeUnder pfx (opGetModel pfx (withTopM (W64 2) (W64 1))).key
        (opGetModel pfx (withTopM (W64 2) (W64 1))).base.rangeEnd from
    ⟨HoR.1, ownerOp_under pfx Hpfx⟩)]
  icases Hgr with ⟨%s', %gsl, %gps, %gkvs, #Hs', %Hwf', #Hgsl, #Hgps, #Hgkvs, %Hgok⟩
  ihave %Hgsl' := ownSlice_len $$ Hgps
  iunfold kvPtrsAt at Hgkvs
  icases Hgkvs with ⟨%Hgl, #Hgkv⟩
  wp_auto
  rcases ownerOp_kvs_cases pfx s' gkvs Hpfx Hwf' Hgok with ⟨rfl, rfl⟩ | ⟨w, rfl, Hlead⟩
  · -- no leader
    have Hlen0 : gsl.len = W64 0 := by
      have : gps.length = 0 := by simpa using Hgl
      rw [this] at Hgsl'; word
    rw [Hlen0]
    ihave Hci : (concurrencyInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hci with ⟨-, -, -, -, ⟨%eNL, #HeNL⟩⟩
    wp_auto
    iapply HΦ
    iright; ileft
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold isPkgErr; iframe HeNL; ipureintro; simp
    iexists R
    iframe HRR Hs'
    ipureintro; exact HlR
  · obtain ⟨kp, rfl⟩ : ∃ kp, gps = [kp] := by
      match gps, Hgl with
      | [kp], _ => exact ⟨kp, rfl⟩
    have Hlen1 : gsl.len ≠ W64 0 := by
      intro h; rw [h] at Hgsl'; simp at Hgsl'; revert Hgsl'; decide
    rw [show decide (gsl.len = W64 0) = false by simpa using Hlen1]
    wp_auto
    ihave #Hkv := Hgkv $$ %0 %kp %w %rfl %rfl
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists R, kp, w
    iframe HgRev HRR
    isplitr
    · unfold getRespOneKv; iexists gsl; iframe Hgsl Hgps Hkv
    isplitr
    · unfold leaderKvAt; iexists s'; iframe Hs'; ipureintro; exact Hlead
    ipureintro; exact HlR

end proof

end concurrency
end EtcdGrove
end Perennial
