/- Lean-first (no Rocq counterpart).

# `k8s/all`: the one closed Kubernetes theorem over the operational semantics

`k8s_adequate` (`notes/k8s-unified-scope.md`, §3.3; restated as `k8s_safe` in `Results.lean`): every
real execution of `k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂` (`TopLevelDefs.lean`:
the package's initialization, then `Main` with the two member counts and the two schedules built as
slice literals) from a fresh
state with one thread, of `n` steps: if the main thread has finished, its result is `#()`; no thread is
stuck; no thread has ended in a panic (no porcupine check of the store's history fails, no API
server's compactor check fails).

It follows from `etcd_adequate_alloc_members` with the members of both clusters (the store cluster's
`k8s_etcd3N.startAddrs k₁`, then the compactor cluster's `k8s_compactorN.startAddrs k₂`), their
bridges, the program's addresses `k8sAddrs k₁ k₂` and data directories `k8sDirs k₁ k₂`, whose
distinctness is `Disjoint.lean`'s; the compactor registry is allocated before the program's proof is
chosen, as the compactor driver's retired closed theorems did, and `Main` receives its claims'
authority with no endpoint claimed. The proof of the body: `k8sall`'s `wp_initialize'`, the two
schedules' slice literals, and `k8s_all.wp_Main` (`MainLinked.lean`).

Its premises are the two retired partition theorems' (`k8s_etcd3_partition_adequate`,
`k8s_compactor_partition_adequate`), once where they coincide; `Hlow` (`k8s_safe`'s, the condition of
idutil's trusted model) is not used by the proof and is stated in `Results.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AdequacyMembers
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.Disjoint
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.InitLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.SchedLit
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.runtime.Start
public import Proof.runtime.Threads

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr

/-! ## The ghost-state bundle -/

/-- The universal camera at slot 0. -/
def k8sGF_allG : AllG k8sGF := ⟨⟨0, rfl⟩⟩

instance k8sGF_gooseGpreS : GooseGpreS k8sGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨k8sGF_allG⟩, ⟨k8sGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := k8sGF_allG

/-- iris-lean's camera of non-atomic invariants, at slot 11: the instance porcupine's results
take. -/
instance k8sGF_naInvG : NaInvG k8sGF := ⟨⟨11, rfl⟩⟩

/-! ## The schedules' slice literals -/

section lit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

/-- **The schedule's slice literal** (the retired drivers' adequacy block, once per schedule): a
schedule of fewer than `2 ^ 63` steps evaluates to a slice that points to the steps. -/
theorem wp_schedLit     (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps : steps.length < 2 ^ 63) (Φ : val → IProp GF) :
    (∀ sl : GoSlice, sl ↦* steps -∗ Φ #sl) ⊢ WP (schedLit steps) {{ Φ }} := by
  iintro HΦ
  unfold schedLit
  iapply (wp_slice_literal (V := github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) (l := steps)
    (kvs := steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))
  have hp := pure_wp_array_lit_full (hlc := HasLC.hasLC) (GF := GF)
    (go.arrayLiteralSize
      (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))
    github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty steps _ rfl
    (by rw [arrayLiteralSize_vals]; simp)
    (by rw [arrayLiteralSize_vals]; simpa using Hsteps)
  have hp' : ∀ Ψ : val → IProp GF,
      iprop(▷ (£ 1 -∗ WP (Val #(array.mk
          (go.arrayLiteralSize
            (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))
          steps)) {{ Ψ }})) ⊢
        WP (App (Val (GoInstruction (CompositeLiteral (go.ArrayType
            (go.arrayLiteralSize
              (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))
            github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty))))
          (Val (LiteralValueV
            (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))))
          {{ Ψ }} :=
    fun Ψ => hp.pure_wp_wp _ _ Ψ [] trivial
  iapply (hp' _)
  inext
  iintro -
  wp_auto
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  iapply HΦ
  iexact Hsl

end lit

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- **`k8s_adequate` along executions with fewer than `2 ^ 28` live threads** (2026-11-22, as
`etcd/all`'s `etcd_adequate_of` since 2026-11-20): the same conclusion for every execution of `n`
steps, `n + 12 ≤ 2 ^ 40` (the backend's write-back budget, `backend.wbInit`), along which fewer than
`2 ^ 28` threads are ever live at once (`RealNstepsBelow`, through
`etcd_adequate_alloc_members_below`): the thread bound is a premise on the execution, not a
consequence of its length. -/
theorem k8s_adequate_below [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8sGF, ContextReadErrs (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8sGF, ContextErrsClient (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (Hafter : ∀ hG : HeapGS .hasLC k8sGF,
      EtcdGrove.clock.RealClock.After.spec (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (k₁ : Nat) (hk₁1 : 1 ≤ k₁) (hk₁ : k₁ ≤ 1000) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (Hlen : ids.length = k₁)
    (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)
    (k₂ : Nat) (hk₂1 : 1 ≤ k₂) (hk₂ : k₂ ≤ 1000) (ids' : List w64) (ps' : List w64)
    (ctxs' : List (List w8)) (boot' : List LogEntry) (Hlen' : ids'.length = k₂)
    (Hbf' : k8s_compactorN.BootFacts ids' ps' ctxs' boot')
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    (clients ops watchers wops : w64) (Hc0 : 0 ≤ sint.Z clients) (Hw0 : 0 ≤ sint.Z watchers)
    (Hc31 : sint.Z clients + sint.Z watchers < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hwops : 0 ≤ sint.Z wops)
    (Hmul : sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60)
    (steps₁ steps₂ : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps₁ : steps₁.length < 2 ^ 63) (Hsteps₂ : steps₂.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂) k8sNames)
    (HAs : addrsUnclaimed (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂) (k8sAddrs k₁ k₂))
    (HDs : dataDirsAbsent (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂) (k8sDirs k₁ k₂))
    (HEnv : verifyEnvOff (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂))
    (n : Nat)
    (Hprem₁ : ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_etcd3N.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) k₁ n ids ps ctxs boot)
    (Hprem₂ : ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_compactorN.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) k₂ n ids' ps' ctxs' boot')
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (k8sDirs k₁ k₂))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNstepsBelow (2 ^ 28) n ([k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂],
      ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 12 ≤ 2 ^ 40) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine etcd_adequate_alloc_members_below (GF := k8sGF) (hbody := rfl) (HWal := HWal) (hn := by omega)
    (hmsL := fun m hm => (List.mem_append.1 hm).elim (k8s_etcd3N.startAddrs_names_len k₁ m)
      (k8s_compactorN.startAddrs_names_len k₂ m))
    (hAsLit := k8s_all.k8sAddrs_lit k₁ k₂ hk₁ hk₂) (HEnv := HEnv)
    github_com.mit_pdos.etcd_grove.examples.k8s.all.initialize'
    (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.all.Main))
      (Val #(W64 (k₁ : Int)))) (Val #clients)) (Val #ops)) (Val #watchers)) (Val #wops))
      (schedLit steps₁)) (Val #(W64 (k₂ : Int)))) (schedLit steps₂))
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm)
    (k8sAddrs k₁ k₂) (k8s_all.k8sAddrs_nodup k₁ k₂ hk₁ hk₂) (k8sDirs k₁ k₂)
    (k8s_all.k8sDirs_nodup k₁ k₂ hk₁ hk₂)
    (k8s_etcd3N.startAddrs k₁ ++ k8s_compactorN.startAddrs k₂)
    (k8s_etcd3N.bridges k₁ ++ k8s_compactorN.bridges k₂)
    (k8s_all.k8sAddrs_perm k₁ k₂) (k8s_all.k8sDirs_perm k₁ k₂)
    σ g ⟨trivial, trivial, trivial⟩ ⟨trivial, Hfs, trivial⟩ Hlctx Hinit Hthreads HNs HAs HDs
    (2 ^ 28) n κs t2 σ2 Hsteps' fun hG HN HT => ?_
  letI : HeapGS .hasLC k8sGF := k8sHeapAt hG lctx
  -- the compactor registry, allocated before the program's proof is chosen (as the compactor
  -- driver's retired closed theorems): `Main` receives the claims' authority, no endpoint claimed
  refine ⟨GName, fun γ => EtcdGrove.k8s.regAuth (reg := ⟨γ⟩) (∅ : GMap GoString GName),
    EtcdGrove.k8s.regAuth_alloc, fun γ => ?_⟩
  letI : EtcdGrove.k8s.CompactorRegistry := ⟨γ⟩
  haveI := Hctx hG
  haveI := Hcec hG
  unfold progOk
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.k8s.all.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.k8s.all.getIsPkgInit_wf, ?_⟩
  ihave #Hp1 := Hprem₁ hG
  ihave #Hp2 := Hprem₂ hG
  iintro #Hinit Htok ⟨⟨Hms, Hbs⟩, Hreg⟩
  icases Hms with ⟨Hms1, Hms2⟩
  icases Hbs with ⟨Hbs1, Hbs2⟩
  unfold k8s_etcd3N.startAddrs k8s_compactorN.startAddrs
  rw [BigSepL.bigSepL_map, BigSepL.bigSepL_map]
  wp_bind (schedLit steps₂)
  iapply wp_schedLit steps₂ Hsteps₂
  iintro %sl₂ Hsl₂
  imod ownSlice_persist _ _ _ $$ Hsl₂ with #Hsl₂
  wp_bind (schedLit steps₁)
  iapply wp_schedLit steps₁ Hsteps₁
  iintro %sl₁ Hsl₁
  imod ownSlice_persist _ _ _ $$ Hsl₁ with #Hsl₁
  haveI : ThreadBoundLe k8sGF (2 ^ 28) := ⟨by rw [HT]; word⟩
  haveI : ReceiptBoundLe k8sGF (2 ^ 48) := ⟨by rw [HN]; omega⟩
  haveI : ReceiptBoundLe k8sGF (n + 1) := ⟨by rw [HN]; omega⟩
  have hM := k8s_all.wp_Main (GF := k8sGF) (Hafter hG) k₁ n ids ps ctxs boot k₂ ids' ps' ctxs'
    boot' clients ops watchers wops sl₁ sl₂ steps₁ steps₂ (srvLevels_of_max HT) hk₁1 hk₁ Hlen Hbf
    hk₂1 hk₂ Hlen' Hbf' (by unfold bootWB backend.wbInit; omega) Haf Hbuq Hrf Hdbo inferInstance
    EtcdGrove.rpctypesEtcdError_asTarget k8s_etcd3.storageErrTyOk_holds k8s_etcd3.objTyOk_holds
    Hc0 Hw0 Hc31 Hops Hwops Hmul
  wp_apply hM $$ [Hms1 Hbs1 Hms2 Hbs2 Htok Hreg]
  · iframe; iframe #
  ipureintro
  rfl

/-- **The one closed Kubernetes theorem, over the operational semantics** (see the file header):
every real execution of `k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂` from a fresh state
with one thread, of `n` steps: if the main thread has finished, its result is `#()`; no thread is stuck; no
thread has ended in a panic. -/
theorem k8s_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8sGF, ContextReadErrs (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8sGF, ContextErrsClient (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (Hafter : ∀ hG : HeapGS .hasLC k8sGF,
      EtcdGrove.clock.RealClock.After.spec (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (k₁ : Nat) (hk₁1 : 1 ≤ k₁) (hk₁ : k₁ ≤ 1000) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (Hlen : ids.length = k₁)
    (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)
    (k₂ : Nat) (hk₂1 : 1 ≤ k₂) (hk₂ : k₂ ≤ 1000) (ids' : List w64) (ps' : List w64)
    (ctxs' : List (List w8)) (boot' : List LogEntry) (Hlen' : ids'.length = k₂)
    (Hbf' : k8s_compactorN.BootFacts ids' ps' ctxs' boot')
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    (clients ops watchers wops : w64) (Hc0 : 0 ≤ sint.Z clients) (Hw0 : 0 ≤ sint.Z watchers)
    (Hc31 : sint.Z clients + sint.Z watchers < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hwops : 0 ≤ sint.Z wops)
    (Hmul : sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60)
    (steps₁ steps₂ : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps₁ : steps₁.length < 2 ^ 63) (Hsteps₂ : steps₂.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂) k8sNames)
    (HAs : addrsUnclaimed (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂) (k8sAddrs k₁ k₂))
    (HDs : dataDirsAbsent (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂) (k8sDirs k₁ k₂))
    (HEnv : verifyEnvOff (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂))
    (n : Nat)
    (Hprem₁ : ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_etcd3N.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) k₁ n ids ps ctxs boot)
    (Hprem₂ : ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_compactorN.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) k₂ n ids' ps' ctxs' boot')
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (k8sDirs k₁ k₂))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNsteps n ([k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂],
      ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  k8s_adequate_below Hctx Hcec Hafter k₁ hk₁1 hk₁ ids ps ctxs boot Hlen Hbf k₂ hk₂1 hk₂ ids' ps'
    ctxs' boot' Hlen' Hbf' Haf Hbuq Hrf Hdbo clients ops watchers wops Hc0 Hw0 Hc31 Hops Hwops Hmul
    steps₁ steps₂ Hsteps₁ Hsteps₂ HNs HAs HDs HEnv n Hprem₁ Hprem₂ σ g Hfs HWal Hlctx Hinit Hthreads
    κs t2 σ2 ((RealNstepsBelow.of_one Hsteps' Hthreads).mono (by omega)) (by omega)

end adequacy

end EtcdGrove
end Perennial
