/-
`replica.New`: the framework's fresh state (`fwFresh`): the read-only fields (`fwRO`), the
fields and table `epaxos.New` sets up, and `fwStart`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.LibDeps
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos_epaxos.replica

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

/-- The `defs` package's state (`defsPkgStateDef`): `LatencyConf` holds `""`. -/
theorem defs_latencyConf :
    (isPkgInit pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica.defs : IProp GF) ⊢
      globalAddr replica.defs.LatencyConf ↦□ ([] : GoString) := by
  iintro #H
  ihave #Hd := isPkgInit_access $$ H
  iexact Hd

variable [EpReplicaDeps GF]

theorem replica.New.spec_holds (hIS : state.InitState.spec (GF := GF)) : replica.New.spec (GF := GF) := by
  intro γ knode id L sl als cfg logger proxy c
  wp_start as ⟨%Hkn, #Hlf, #Hsl, #HCI, Hrs, #Hcfg, %Hpx, #Hproxy, #Hlog⟩
  ihave %Hok := listFinal_ok $$ Hlf
  have hL5 : L.length = 5 := by unfold finalListOk at Hok; rw [Hok.length_eq]; decide
  have hid : id < 5 := by
    have := (List.getElem?_eq_some_iff.mp Hkn.2).1; omega
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have hslen : sl.len = W64 5 := by
    have h1 := Hsll.1; rw [hL5] at h1; have := Hsll.2
    apply BitVec.eq_of_toInt_eq; word
  wp_auto
  rw [hslen]
  wp_apply (wp_slice_make2 (V := GoInterface) (W64 5)) as %peers ⟨Hpeers, -⟩
  · ipureintro; decide
  wp_apply (wp_slice_make2 (V := Loc) (W64 5)) as %readers ⟨Hreaders, -⟩
  · ipureintro; decide
  wp_apply (wp_slice_make2 (V := Loc) (W64 5)) as %writers ⟨Hwriters, -⟩
  · ipureintro; decide
  wp_apply (wp_map_make1 (K := w32) (V := Loc) _ _) as %cw Hcw
  wp_apply (wp_slice_make2 (V := Bool) (W64 5)) as %alive ⟨Halive, -⟩
  · ipureintro; decide
  wp_apply (wp_slice_make2 (V := w32) (W64 5)) as %ppo ⟨Hppo, -⟩
  · ipureintro; decide
  have hIS' := hIS
  unfold state.InitState.spec at hIS'
  wp_apply hIS' as %st Hst
  have hNT := EpReplicaDeps.newTableId (GF := GF)
  unfold rpc.NewTableId.spec at hNT
  wp_apply hNT as %tbl Htbl
  wp_apply (wp_map_make1 (K := GoString) (V := w64) _ _) as %sm Hsm
  wp_apply (chan.wp_make2 (V := Loc) (W64 2000000)) as %pch %γp ⟨#Hpch, %Hpcap, Hpo⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := Loc) (W64 2000000)) as %bch %γb ⟨#Hbch, -, Hbo⟩
  · ipureintro; decide
  wp_apply (wp_slice_make2 (V := w64) (W64 5)) as %ewma ⟨Hewma, -⟩
  · ipureintro; decide
  wp_apply (wp_slice_make2 (V := w64) (W64 5)) as %lat ⟨Hlat, -⟩
  · ipureintro; decide
  -- `defs.LatencyConf` is `""` (the `defs` package's state, `defsPkgStateDef`), so `Dt` stays nil
  ihave #Hdefs : (isPkgInit pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica.defs : IProp GF) $$ []
  · iPkgInit
  ihave #HLC : (globalAddr replica.defs.LatencyConf ↦□ ([] : GoString) : IProp GF) $$ []
  · iapply defs_latencyConf; iexact Hdefs
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr, %Hrn⟩
  icases typedPointsto_split _ _ _ $$ Hr with Hr
  simp only [TypedPointsto.typedPointstoDef]
  icases Hr with ⟨HLogger, HM, HN, HF, HId, HAlias, HPeerAddrList, HPeers, HPeerReaders,
    HPeerWriters, HClientWriters, HConfig, HAlive, HPPO, HState, HRPC, HStableStore, HStats,
    HShutdown, HListener, HProposeChan, HBeaconChan, HThrifty, HExec, HLRead, HDreply, HBeacon,
    HDurable, HEwma, HLatencies, HDt, -⟩
  have hidz : W32 (sint.Z (W64 (id : Int))) = W32 (id : Int) := by
    apply BitVec.eq_of_toInt_eq; word
  rw [hidz]
  -- the read-only fields, and the channels as bags
  ipersist HLogger; ipersist HN; ipersist HF; ipersist HId; ipersist HAlias
  ipersist HPeerAddrList; ipersist HPeers; ipersist HPeerReaders; ipersist HPeerWriters
  ipersist HClientWriters; ipersist HConfig; ipersist HAlive; ipersist HState; ipersist HRPC
  ipersist HStableStore; ipersist HStats; ipersist HShutdown; ipersist HProposeChan
  ipersist HBeaconChan; ipersist HThrifty; ipersist HExec; ipersist HLRead; ipersist HDreply
  ipersist HEwma; ipersist HLatencies; ipersist HDt; ipersist «$v16»
  iapply fupd_wp
  imod (start_bag (proposal γ id) (ChanState.Buffered []) pch γp trivial) $$ Hpch Hpo with #Hpbag
  imod (start_bag (V := Loc) (fun _ => iprop(False)) (ChanState.Buffered []) bch γb trivial)
    $$ Hbch Hbo with #Hbbag
  imodintro
  ihave HI : (∃ k : Nat, "i" ∷ i_ptr ↦ W64 (k : Int) ∗
      "Hppo" ∷ ppo ↦* (((List.range k).map fun (j : Nat) => W32 (((id + 1 + j) % 5 : Nat) : Int)) ++
        List.replicate (5 - k) (W32 0)) ∗
      "%Hk" ∷ ⌜k ≤ 5⌝ : IProp GF) $$ [i Hppo]
  · iexists 0; iframe; ipureintro; omega
  wp_for HI
  wp_if_destruct
  · have hk5 : k < 5 := by word
    ihave %Hpl := ownSlice_len _ _ _ $$ Hppo
    have hpl : sint.Z ppo.len = 5 := by
      have h1 := Hpl.1; simp only [List.length_append, List.length_map, List.length_range,
        List.length_replicate] at h1
      rw [show k + (5 - k) = 5 by omega] at h1; have := Hpl.2; word
    have hkz : sint.Z (W64 (k : Int)) = (k : Int) := by word
    have hval : W32 (sint.Z (BitVec.srem (W64 (sint.Z (W32 (id : Int))) + W64 1 + W64 (k : Int))
        (W64 5))) = W32 (((id + 1 + k) % 5 : Nat) : Int) := by
      rcases id with _ | _ | _ | _ | _ | id <;> rcases k with _ | _ | _ | _ | _ | k <;>
        first | decide | omega
    rw [hval, hkz, hpl, if_pos (by omega)]
    wp_apply wp_store_slice_index ppo (k : Int) _ (W32 (((id + 1 + k) % 5 : Nat) : Int))
      $$ [Hppo] as Hppo
    · iframe; ipureintro; simp; omega
    ihave %Hel := ownSlice_len _ _ _ $$ Hewma
    ihave %Hll := ownSlice_len _ _ _ $$ Hlat
    have hel : sint.Z ewma.len = 5 := by
      have h1 := Hel.1; simp only [List.length_replicate] at h1; have := Hel.2; word
    have hll : sint.Z lat.len = 5 := by
      have h1 := Hll.1; simp only [List.length_replicate] at h1; have := Hll.2; word
    rw [hkz, hel, if_pos (by omega)]
    wp_apply wp_store_slice_index ewma (k : Int) _ (W64 0) $$ [Hewma] as Hewma
    · iframe; ipureintro; simp; omega
    rw [hkz, hll, if_pos (by omega)]
    wp_apply wp_store_slice_index lat (k : Int) _ (W64 0) $$ [Hlat] as Hlat
    · iframe; ipureintro; simp; omega
    have hz : (Perennial.zero_val w64) = W64 0 := rfl
    rw [hz, List.set_replicate_self]
    simp only [Int.toNat_natCast]
    wp_for_post
    iframe
    iexists k + 1
    rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
    have hset : ((List.range k).map (fun (j : Nat) => W32 (((id + 1 + j) % 5 : Nat) : Int)) ++
        List.replicate (5 - k) (W32 0)).set k (W32 (((id + 1 + k) % 5 : Nat) : Int)) =
        (List.range (k + 1)).map (fun (j : Nat) => W32 (((id + 1 + j) % 5 : Nat) : Int)) ++
        List.replicate (5 - (k + 1)) (W32 0) := by
      obtain ⟨m, hm⟩ : ∃ m, 5 - k = m + 1 := ⟨4 - k, by omega⟩
      rw [hm, show 5 - (k + 1) = m by omega, List.set_append_right _ _ (by simp),
        List.range_succ, List.map_append]
      simp [List.replicate_succ]
    rw [hset]
    iframe
    ipureintro; omega
  · have hk : k = 5 := by
      have : ¬ (sint.Z (W64 (k : Int)) < 5) := by
        intro h; exact Hif (by rw [show sint.Z (W64 5) = 5 by decide]; exact h)
      have : ¬ ((k : Int) < 5) := by word
      omega
    subst hk
    iapply HΦ
    iexists (⟨logger, als, sl, peers, readers, writers, cw, cfg, proxy, alive, st, tbl, «$v16_ptr»,
      sm, pch, bch, ewma, lat⟩ : FwPtrs)
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    unfold fwFresh
    have hgd : L.getD id [] = peerAddrOf knode := by
      rw [List.getD_eq_getElem?_getD, Hkn.2]; rfl
    iframe
    isplitr
    · rw [fwRO_unseal]; unfold fwRODef
      simp only [hL5]
      iframe #
      ipureintro; exact ⟨Hpx, ⟨rfl, hid⟩, by rw [Hpcap]; decide⟩
    rw [fwStart_unseal]; unfold fwStartDef
    simp only [hL5, hgd]
    iframe
    simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
    iexact Hppo

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
