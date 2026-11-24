/- Lean-first (no Rocq counterpart).

# The etcd examples' extensions over the network, with crashes (etcd-dist D4c, 2026-11-24)

`etcdNetExts` (`NetExts.lean`: `[idIssueExt, fsExt at etcdFsSem, netExt]`) with a crash interpretation,
for deployments whose machines crash and restart (`notes/etcd-dist-plan.md` §12): the file extension's
at `etcdFsSem` (`Fs.fs_crash_interpS etcdSQ True`: `etcdFsSem`'s crash is `OsCrash ∧ True`), the net
extension's (`Net.net_crash_interp`: nothing), and **any** crash interpretation `C` of the issue record
(D4b designs the one the proofs will use: the record keyed by incarnation). Over it, `DistCrashAdequacy.lean`'s
general corollary applies (`robust_of_dist_crash_adequacy_etcdNet`): the crash resources split into the file extension's
and the issue record's (`etcdNet_crashStart_split`), and the initial states' conditions come from
`Robust`'s premises and each crashing machine's `FsInit` (`etcdNetExts_crashInitP`; `etcdFsSem`,
`Fs.fsSemWithS`, has no `initLocal` until D4a).

`idIssue_crash_interp_keep` shows that the issue record's semantics today (a crash keeps the record)
already has a crash interpretation: the ghost state kept (`crashStart L L' := ⌜L' = L⌝`, the pattern of
`ExtCrashInterp`'s docstring for durable state). It is an instance of `C`, not a choice for the proofs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NetExts
public import Net.Statement.DistCrashAdequacy
public import GooseLang.Ext.Fs.FilteredSem

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Robustness

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdFsSem
  etcdNetExts_hasIdIssue etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSemOk GooseGlobalGS.gooseInvGS

/-- The crash interpretations of `etcdNetExts`, for a crash interpretation `C` of the issue record: `C`,
the file extension's at `etcdFsSem`, the net extension's. -/
@[reducible] def etcdNetExtsCrashInterp
    (C : @ExtCrashInterp idIssueExt idIssue_semantics idIssue_interp) : GooseCrashInterp :=
  ⟨(C, Fs.fs_crash_interpS etcdSQ (fun _ _ => True), Net.net_crash_interp, ⟨⟩)⟩

/-- The issue record's crash resources of the generations `L` and `L'`, under `C`. -/
def etcdIdCrashRest (C : @ExtCrashInterp idIssueExt idIssue_semantics idIssue_interp)
    {GF : BundledGFunctors} (L L' : GooseLocalGS GF) : IProp GF :=
  @ExtCrashInterp.crashStart idIssueExt idIssue_semantics idIssue_interp C GF
    (extLocalGS idIssueExt (L := L)) (extLocalGS idIssueExt (L := L'))

/-- **The crash resources of `etcdNetExts` split** as `robust_of_dist_crash_adequacy_fs` asks: the file extension's
(crash premise `True`) and the issue record's (`etcdIdCrashRest C`); the net extension's are `emp`. -/
theorem etcdNet_crashStart_split (C : @ExtCrashInterp idIssueExt idIssue_semantics idIssue_interp)
    {GF : BundledGFunctors} (L L' : GooseLocalGS GF) :
    letI := etcdNetExtsCrashInterp C
    extsCrashStart L L' ⊢
      Fs.osCrashStart (fun _ _ => True) (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) ∗
        etcdIdCrashRest C L L' :=
  by
    letI := etcdNetExtsCrashInterp C
    show iprop(etcdIdCrashRest C L L' ∗
      (Fs.osCrashStart (fun _ _ => True) (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) ∗
        (iprop(emp) ∗ iprop(emp)))) ⊢ _
    iintro ⟨Hi, Hf, -⟩
    isplitl [Hf]
    · iexact Hf
    · iexact Hi

/-- The interpretations' conditions on the machines' initial states for `etcdNetExts`, and every
crashing machine's `FsInit`, from `Robust`'s premises and the deployment's `FsInit`
(`etcdNetExts_initP`). -/
theorem etcdNetExts_crashInitP (g : GlobalState) (crashing stable : List (Expr × state))
    (Hfs : ∀ m, m ∈ crashing ++ stable → Fs.FsInit (extLocal Fs.fsExt m.2.world)) :
    extsInitGlobal g → (∀ m, m ∈ crashing ++ stable → extsInitLocal m.2 g) →
      extsInitgP g.globalWorld ∧
      (∀ m, m ∈ crashing ++ stable → extsInitP m.2.world g.globalWorld) ∧
      ∀ m, m ∈ crashing → Fs.FsInit (extLocal Fs.fsExt m.2.world) :=
  fun hg hl =>
    let H := etcdNetExts_initP g (crashing ++ stable) Hfs hg hl
    ⟨H.1, H.2, fun m hm => Hfs m (List.mem_append_left _ hm)⟩

/-- **Distributed crash adequacy as `Robust` for `etcdNetExts`** (`Net.robust_of_dist_crash_adequacy_fs` at the crash interpretations
`etcdNetExtsCrashInterp C`): a crashing machine's generations get, after a crash, the cells' invariant,
the file system's crash rest and the issue record's crash resources under `C` (`etcdIdCrashRest C`). -/
theorem robust_of_dist_crash_adequacy_etcdNet (C : @ExtCrashInterp idIssueExt idIssue_semantics idIssue_interp)
    [GoGlobalContext] {GF : BundledGFunctors} [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    (addrs : List GoString) (crashing stable : List (Expr × state)) (g : GlobalState)
    (threads bound lo : Nat) (hlo : lo ≤ bound)
    (Hnd : addrs.Nodup) (Hok : ∀ a ∈ addrs, Net.addrOk a = true)
    (Hfs : ∀ m, m ∈ crashing ++ stable → Fs.FsInit (extLocal Fs.fsExt m.2.world))
    (Hstart : letI := etcdNetExtsCrashInterp C
      ∀ [GooseGlobalGS .hasLC GF], lo ≤ receiptBound GF → receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, Net.addrUnset a) ={⊤}=∗
        ∃ (Pc : Nat → GooseLocalGS GF → IProp GF) (Ps : Nat → IProp GF),
          ⌜∀ (i : Nat) (m : Expr × state), crashing[i]? = some m →
            Net.CrashBootWpG (fun _ _ => True) (etcdIdCrashRest C) lo bound m.1 (Pc i)⌝ ∗
          ⌜∀ (j : Nat) (m : Expr × state), stable[j]? = some m →
            Net.DistBootWpSL lo bound m.1 m.2 (Ps j)⌝ ∗
          ([∗list] i ↦ m ∈ crashing, ∀ L : GooseLocalGS GF,
            ⌜L.goose_go_local_context = lctx⌝ -∗
            ⌜@ThreadGS.threadBound GF L.goose_threadGS = receiptBound GF + 1⌝ -∗
            Net.fsStartResG L (extLocal Fs.fsExt m.2.world) -∗
            ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗ Pc i L) ∗
          [∗list] j ↦ _m ∈ stable, Ps j) :
    Robust crashing stable g threads bound :=
  letI := etcdNetExtsCrashInterp C
  Net.robust_of_dist_crash_adequacy_fs (GF := GF) (fun _ _ => True) (etcdIdCrashRest C)
    (etcdNet_crashStart_split C) addrs crashing stable g threads bound lo hlo Hnd Hok
    (etcdNetExts_crashInitP g crashing stable Hfs) Hstart

/-- **A crash interpretation of the issue record as it is today** (`idIssue_semantics`: a crash keeps
the record): the ghost state kept, `crashStart L L' := ⌜L' = L⌝`. An instance of `C` above (the corollary
applies to today's semantics); D4b's record keyed by incarnation replaces it. -/
@[instance_reducible] def idIssue_crash_interp_keep :
    @ExtCrashInterp idIssueExt idIssue_semantics idIssue_interp where
  crashStart hL hL' := iprop(⌜hL' = hL⌝)
  local_crash _ _ hL σ σ' hc := by
    obtain rfl := (show σ' = σ from hc)
    iintro H
    imodintro
    iexists hL
    iframe H
    ipureintro
    rfl

end EtcdGrove
end Perennial
