/-
**The ghost state authkv's `Main` allocates before its member, with auth on** (2026-10-30).
Lean-first (no Rocq counterpart).

`ak_alloc`: `common.alloc1`'s allocation (the member's names, its storage registry, the raft
network with the directory `akDir id`) with the mode-`on` cluster and member
(`srvClusterBootOn_alloc`, `srvMemberBootOn_alloc`): what `startServer` takes (`memberBootOn`),
the client's `etcdKV` at the boot state (its first consistent index `0`, `SetUp`'s, and start log `[[], []]`, the watch's), which the history invariant is allocated at (`akHist_alloc`:
the boot state is admitted, `stateHistOk_boot`), and the client's view of the auth history at the
start (`authHistView … [srvAuthSt0]`, what `SetUp` takes).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Hist
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAllocOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **What authkv's `Main` takes of the ghost state, for its member** (see the file header). -/
theorem ak_alloc (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlow : uint.Z id % 2 ^ 16 ≠ 0) (HB : BootLog [id] ctxs boot)
    (Hcc : ∀ e ∈ LogEntry.toEntries boot 0,
      ccIdOf e.Data' = W64 0 ∧ ccBootOk (GMap.listToSet [id]) e.Data')
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hrb2 : receiptBound GF + boot.length ≤ 2 ^ 61) :
    ⊢ bootMarshal (GF := GF) [id] ctxs (LogEntry.toEntries boot 0) ={⊤}=∗
      ∃ (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
        (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (σ₀ : KVState),
      ⌜γ.vs = [id] ∧ γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧
        γ.boot = LogEntry.toEntries boot 0 ∧ γn.N = srvNet γ ∧ γn.dir = akDir id ∧
        stateHistOk σ₀ ∧ ρ.rd.kv.c0 = W64 0 ∧ ρ.rd.kv.log0 = [[], []]⌝ ∗
      common.memberBootOn γ ctxs ρ E₀ Φs id ∗ netHttpOk γn id ∗
      etcdKV ρ.rd.kv σ₀ ∗ authHistView ρ.rd.kv [srvAuthSt0] := by
  iintro #Hmarsh
  imod newServerNames_alloc (GF := GF) with ⟨%idx, %cok, %rev, Hidx, Hcok, Hrev⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%reg, Hreg⟩
  have Hid0 : id ≠ W64 0 := by
    intro h; apply Hlow; rw [h]; decide
  let Φs : w64 → w64 → List w8 → GName → IProp GF := fun _ => srvFloorFact (common.env₀ idx cok rev)
  imod (srvClusterBootOn_alloc (GF := GF) [id] ctxs boot Φs reg Hrb Hrb2 HB (by simp) (by simp)
      (by simpa using Hid0.symm) Hcc (by simp) (by simpa using Hlow)) $$ Hmarsh
    with ⟨%γ, %issued, %cnt, %γk, %Hγ, #Hsrl, #Hkv, Hetcd, Hview, #Hcl, #H0, #Hpm, #Hrc, Hms,
      Hwns⟩
  obtain ⟨hvs, hrule, hboot, hreg, hc0, hch, hlog, hiss, hkc⟩ := Hγ
  icases BigSepL.bigSepL_cons.1 $$ Hms with ⟨⟨Hp, Hnb, Hsd⟩, -⟩
  icases BigSepL.bigSepL_cons.1 $$ Hwns with ⟨Hwn, -⟩
  imod (srvMemberBootOn_alloc (GF := GF) γ cnt γk id cok) $$ Hkv Hp Hwn
    with ⟨%ρ, %Hρ, #Hkvρ, Hsh, Hnk, Hwt⟩
  obtain ⟨hraft, hst, hc0', hch', hlog', hcok, hiss', hcnt, hpfx, hhist, hkc'⟩ := Hρ
  imod (netNames_alloc (srvNet γ) (akDir id) (∅ : GMap w64 Unit) ⊤) with ⟨%γn, %Hγn, -, #HregN⟩
  ihave #Hnet := netHttpOk_single γn id
    (fun f hf => dirOne_member id _ f (by rw [Hγn.2] at hf; exact hf)) $$ HregN
  have hσ : stateHistOk (kvStateOf (kvModelOn γk srvAuthSt0 (bootEntries γ.boot))) :=
    stateHistOk_boot γk srvAuthSt0 [id] γ.boot
      (by rw [hboot]; exact srvBootLogOk_of_BootLog _ _ _ HB) hlog
  imodintro
  iexists γ, ρ, common.env₀ idx cok rev, Φs, γn, kvStateOf (kvModelOn γk srvAuthSt0 (bootEntries γ.boot))
  iframe Hnet
  isplitr
  · ipureintro
    exact ⟨hvs, hrule, hboot, Hγn.1, Hγn.2, hσ, by rw [hc0', hc0], by rw [hlog', hlog]⟩
  isplitr [Hetcd Hview]
  · iunfold common.memberBootOn
    simp only [common.env₀]
    rw [hiss', hcnt, hraft, hiss, hvs, hreg]
    rw [← srvPropMint_congr _ γk.ids ρ.ids (by rw [hiss', hiss])]
    iframe Hnb Hsrl Hcl Hpm Hrc Hsh Hidx Hcok Hrev Hnk Hkvρ Hwt Hsd Hreg
    isplitr
    · ipureintro
      exact ⟨rfl, by rw [hc0', hc0], by rw [hch', hch], by rw [hlog', hlog], hcok,
        hpfx, rfl, trivial, by rw [hkc', hkc]⟩
    iunfold idNoZero
    rw [hiss', hiss]
    iexact H0
  rw [etcdKV_congr ρ.rd.kv γk hst]
  iframe Hetcd
  unfold authHistView
  rw [hhist]
  iexact Hview

end alloc

end authkv
end EtcdGrove
end Perennial
