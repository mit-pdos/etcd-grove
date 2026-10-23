/-
Lean-first (no Rocq counterpart).

**The ghost state `Main` allocates before the members** (D20, D21, 2026-10-19): putget3's
(`putget3/Alloc.lean`'s `putget3_alloc`, whose steps this repeats, over putget3's `memberBoot`,
`memberBoot_of`, `env₀` and the id lemmas) at a directory given as a parameter (linkv3's `dir3`)
and with the client's `etcdKV` at the third member's names, with that member's start log
`[[], []]` (what `linkvInv_alloc_boot` takes). linkv3's `Main` calls it with its members in
`bootstrap`'s order, `[id₂, id₃, id₁]` (`Defs.lean`), so the third is `linkv3-1`, the member the
client is connected to; the `etcdKV` is the cluster's (D21 M4), at that member's names.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
open putget3 (memberBoot memberBoot_of env₀ pfx_ne id_ne id_nz ccOk)

section alloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **What `Main` takes of the ghost state, for its cluster** (see the file header): putget3's
`putget3_alloc` at the directory `dir`, with the client's `etcdKV` at the third member's names
(and that member's start log). -/
theorem cluster3_alloc (id₁ id₂ id₃ : w64) (bootLog : List EntryM)
    (Hbf : putget3.BootFacts id₁ id₂ id₃ bootLog) (dir : w64 → List GoString)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) :
    ⊢ |={⊤}=> ∃ (γ : RaftNames) (bud : BudgetNames) (ρ₁ ρ₂ ρ₃ : ReqNames)
        (E₁ E₂ E₃ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF)
        (γn : NetNames GF),
      ⌜γ.reCfg = GMap.listToSet [id₁, id₂, id₃] ∧ γ.reDyn = none ∧
        γ.reCCOk = ccOk [id₁, id₂, id₃] ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧
        γ.reNoXfer = true ∧ γn.N = srvNet γ bud ∧ γn.dir = dir ∧ ρ₃.rd.kv.log0 = [[], []] ∧
        ρ₃.rd.kv.wl = putgetWorkload⌝ ∗
      memberBoot putgetWorkload γ bud bootLog ρ₁ E₁ Φs id₁ ∗ netSlot γn id₁ ∗
      memberBoot putgetWorkload γ bud bootLog ρ₂ E₂ Φs id₂ ∗ netSlot γn id₂ ∗
      memberBoot putgetWorkload γ bud bootLog ρ₃ E₃ Φs id₃ ∗ netSlot γn id₃ ∗
      etcdKV ρ₃.rd.kv (kvStateOf (kvModel ρ₃.rd.kv (bootEntries bootLog))) := by
  obtain ⟨hn12, hn13, hn23⟩ := id_ne id₁ id₂ id₃ bootLog Hbf
  obtain ⟨hp12, hp13, hp23⟩ := pfx_ne id₁ id₂ id₃ bootLog Hbf
  have Hnz := id_nz id₁ id₂ id₃ bootLog Hbf
  istart
  imod newServerNames_alloc (GF := GF) with ⟨%idx₁, %cok₁, %rev₁, Hidx₁, Hcok₁, Hrev₁⟩
  imod newServerNames_alloc (GF := GF) with ⟨%idx₂, %cok₂, %rev₂, Hidx₂, Hcok₂, Hrev₂⟩
  imod newServerNames_alloc (GF := GF) with ⟨%idx₃, %cok₃, %rev₃, Hidx₃, Hcok₃, Hrev₃⟩
  let Φs : w64 → w64 → List w8 → GName → IProp GF := fun p =>
    if p = idPfxOf (W16 (uint.Z id₁)) then srvFloorFact (env₀ idx₁ cok₁ rev₁)
    else if p = idPfxOf (W16 (uint.Z id₂)) then srvFloorFact (env₀ idx₂ cok₂ rev₂)
    else srvFloorFact (env₀ idx₃ cok₃ rev₃)
  have HΦ₁ : Φs (idPfxOf (W16 (uint.Z id₁))) = srvFloorFact (env₀ (GF := GF) idx₁ cok₁ rev₁) := by
    simp only [Φs, if_true]
  have HΦ₂ : Φs (idPfxOf (W16 (uint.Z id₂))) = srvFloorFact (env₀ (GF := GF) idx₂ cok₂ rev₂) := by
    simp only [Φs, Ne.symm hp12, if_false, if_true]
  have HΦ₃ : Φs (idPfxOf (W16 (uint.Z id₃))) = srvFloorFact (env₀ (GF := GF) idx₃ cok₃ rev₃) := by
    simp only [Φs, Ne.symm hp13, Ne.symm hp23, if_false]
  have Hpol : ∀ ty d, ccOk [id₁, id₂, id₃] ty d → ty = W32 1 ∧ isConfChangeEncoding d ∧
      ccIdOf d = W64 0 ∧ ccBootOk (GMap.listToSet [id₁, id₂, id₃]) d := fun ty d h => h
  have Hin₁ : id₁ ∈ GMap.listToSet [id₁, id₂, id₃] := by
    rw [GMap.elem_of_list_to_set]; simp
  imod (srvClusterBoot_alloc (GF := GF) (GMap.listToSet [id₁, id₂, id₃])
      (GMap.listToSet [id₁, id₂, id₃]) (ccOk [id₁, id₂, id₃]) [id₁, id₂, id₃] bootLog
      putgetWorkload Φs
      (fun h => GMap.not_elem_of_empty id₁ (h ▸ Hin₁))
      (by
        rw [GMap.elem_of_list_to_set]
        intro h
        exact Hnz _ h rfl)
      rfl Hbf.boot Hpol Hbf.idLow Hbf.idLow0)
    with ⟨%γ, %issued, %cnt, %γk, %Hγ, #Hcinv, #Hcomm, -, Hghosts, #Hkv, Hetcd, #Hcl, #H0,
      #Hpm, #Hrc, Hms, Hwns⟩
  obtain ⟨hcfg, hdyn, hcc, hboot, htr, htx, hc0, hch, hlog, hiss, hwl⟩ := Hγ
  have Hpol' : srvCCPolicy ⟨γ, [], W64 0⟩ := by
    intro ty d h
    simp only at h ⊢
    rw [hcc] at h
    rw [hcfg]
    exact h
  icases Hms with ⟨Hm₁, Hm₂, Hm₃, -⟩
  icases Hwns with ⟨Hw₁, Hw₂, Hw₃, -⟩
  imod budget_alloc_boot (GF := GF) Hrb ⊤ with ⟨%bud, #Hbinv, #Hlb⟩
  -- the nodes' ghost states, out of the map over the cluster
  rw [show toMap (GMap.listToSet [id₁, id₂, id₃]) =
      GMap.insert id₁ () (GMap.insert id₂ () (GMap.insert id₃ () (∅ : GMap w64 Unit))) from rfl]
  ihave ⟨Hg₁, Hgs⟩ := (BigSepM.bigSepM_insert
    (Φ := fun k (_ : Unit) => ownRaftGhost (GF := GF) γ k (bootPState bootLog))
    (by rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (Ne.symm hn12),
      GMap.lookup_insert_ne _ _ (Ne.symm hn13)]; exact GMap.lookup_empty _)).1 $$ Hghosts
  ihave ⟨Hg₂, Hgs⟩ := (BigSepM.bigSepM_insert
    (Φ := fun k (_ : Unit) => ownRaftGhost (GF := GF) γ k (bootPState bootLog))
    (by rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (Ne.symm hn23)]; exact GMap.lookup_empty _)).1 $$ Hgs
  ihave ⟨Hg₃, -⟩ := (BigSepM.bigSepM_insert
    (Φ := fun k (_ : Unit) => ownRaftGhost (GF := GF) γ k (bootPState bootLog))
    (GMap.lookup_empty _)).1 $$ Hgs
  imod (memberBoot_of putgetWorkload γ bud bootLog issued cnt γk Φs id₁ idx₁ cok₁ rev₁ hiss hc0 hch hlog hwl
      Hpol' HΦ₁) $$ Hg₁ Hcomm Hcinv Hbinv Hlb Hcl H0 Hpm Hrc Hkv Hm₁ Hw₁ Hidx₁ Hcok₁ Hrev₁
    with ⟨%ρ₁, -, Hb₁⟩
  imod (memberBoot_of putgetWorkload γ bud bootLog issued cnt γk Φs id₂ idx₂ cok₂ rev₂ hiss hc0 hch hlog hwl
      Hpol' HΦ₂) $$ Hg₂ Hcomm Hcinv Hbinv Hlb Hcl H0 Hpm Hrc Hkv Hm₂ Hw₂ Hidx₂ Hcok₂ Hrev₂
    with ⟨%ρ₂, -, Hb₂⟩
  imod (memberBoot_of putgetWorkload γ bud bootLog issued cnt γk Φs id₃ idx₃ cok₃ rev₃ hiss hc0 hch hlog hwl
      Hpol' HΦ₃) $$ Hg₃ Hcomm Hcinv Hbinv Hlb Hcl H0 Hpm Hrc Hkv Hm₃ Hw₃ Hidx₃ Hcok₃ Hrev₃
    with ⟨%ρ₃, %Hρ₃, Hb₃⟩
  -- the raft network: a slot per member
  imod (netNames_alloc (srvNet γ bud) dir
      (GMap.insert id₁ () (GMap.insert id₂ () (GMap.insert id₃ () (∅ : GMap w64 Unit)))) _)
    with ⟨%γn, %Hγn, Hslots, -⟩
  ihave ⟨Hs₁, Hslots⟩ := (BigSepM.bigSepM_insert
    (Φ := fun k (_ : Unit) => netSlot (GF := GF) γn k)
    (by rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (Ne.symm hn12),
      GMap.lookup_insert_ne _ _ (Ne.symm hn13)]; exact GMap.lookup_empty _)).1 $$ Hslots
  ihave ⟨Hs₂, Hslots⟩ := (BigSepM.bigSepM_insert
    (Φ := fun k (_ : Unit) => netSlot (GF := GF) γn k)
    (by rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (Ne.symm hn23)]; exact GMap.lookup_empty _)).1 $$ Hslots
  ihave ⟨Hs₃, -⟩ := (BigSepM.bigSepM_insert
    (Φ := fun k (_ : Unit) => netSlot (GF := GF) γn k)
    (GMap.lookup_empty _)).1 $$ Hslots
  obtain ⟨hst₃, hc0₃, hch₃, hlog₃, hwl₃⟩ := Hρ₃
  imodintro
  iexists γ, bud, ρ₁, ρ₂, ρ₃, env₀ idx₁ cok₁ rev₁, env₀ idx₂ cok₂ rev₂, env₀ idx₃ cok₃ rev₃, Φs, γn
  iframe Hb₁ Hb₂ Hb₃ Hs₁ Hs₂ Hs₃
  isplitr
  · ipureintro; exact ⟨hcfg, hdyn, hcc, hboot, htr, htx, Hγn.1, Hγn.2, by rw [hlog₃, hlog], by rw [hwl₃, hwl]⟩
  rw [etcdKV_congr ρ₃.rd.kv γk hst₃,
    show kvModel ρ₃.rd.kv (bootEntries bootLog) = kvModel γk (bootEntries bootLog) by
      unfold kvModel; rw [hc0₃, hch₃, hlog₃]]
  iexact Hetcd

end alloc

end linkv3
end EtcdGrove
end Perennial
