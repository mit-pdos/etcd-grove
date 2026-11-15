/-
**A one-member example's start premises, shared** (2026-11-04, K4 of
`notes/k8s-compactor-plan.md`). Lean-first.

The one-member examples (`putget`, `compacted`, `compactwatch`, `lease`, `leasegrant`, `watch`,
`cache`, `txnlin`, `k8s/etcd3`) each defined the same two things, at their own configuration: `BootFacts`, `bootstrap`'s result for
the member as Go computes it, and `premises`, the named Iris premises of their `Main` (`bootstrap`'s
contract at the configuration, `proto.Marshal`'s at the bootstrap log, the raft wrapper's
trust-boundary contracts (until 2026-11-13 also the deployment's `runsNoRequireLeader`); `compactwatch/Defs.lean`'s
header says what each is). Here they are once, at the shared start's configuration of the member
`name` and its two addresses (`cfgOk name name`, `urls1`, `Defs.lean`; the directory `dir1`), with
`kvModel_boot`. Since 2026-11-04 (the user's request) the one-member examples' own names are
abbreviations of these (their `Main.spec`s unchanged in text; `notes/decisions.md`, "The one-member
examples' start, shared"); `auth` keeps its own (its configuration also sets `AuthToken`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **`bootstrap`'s result for a one-member cluster, as Go computes it** (pure facts of the
program): the member id `id` (etcd's, from the configuration's peer URLs and cluster token) with
its 16 low bits not `0` (D19c), and the bootstrap log `bl` with the peers' contexts `ctxs` (one conf
change adding the member), each entry a conf change of id `0` that the server's
`applyConfChange` takes, the boot members' peer URLs valid UTF-8 and pairwise disjoint
(`bootURLsOk`). (2026-11-09, raft-entsize [r3a]/[r3a']: the shared `BootCore` at `[id]`, which
adds the bound on the boot entries, `bootDataOk`; until then its own structure, without it.) -/
abbrev BootFacts (id : w64) (ctxs : List (List w8)) (bl : List LogEntry) : Prop :=
  BootCore [id] ctxs bl

/-- The member id's 16 low bits are not `0` (`BootCore.lowNz` at `[id]`). -/
theorem BootFacts.idLow {id : w64} {ctxs : List (List w8)} {bl : List LogEntry}
    (h : BootFacts id ctxs bl) : uint.Z id % 2 ^ 16 ≠ 0 :=
  h.lowNz id (List.mem_singleton_self id)

/-- **The peer-URL directory of a one-member cluster** (D21 M2; `dirOne`): the member `id`'s peer
URL `http://peer`. -/
def dir1 (peer : GoString) (id : w64) : w64 → List GoString := dirOne id (go!"http://" ++ peer)

/-- **A bootstrap log's KV model is the start log** (its entries conf changes: `kvTableOf_boot`'s,
for the log). Shared copy of `compactwatch`'s (`NoDup.lean`). -/
theorem kvModel_boot (γk : KVNames) (ps : List w64) (bootLog : List EntryM)
    (hb : srvBootLogOk ps bootLog) : kvModel γk (bootEntries bootLog) = γk.log0 := by
  obtain ⟨-, -, he⟩ := hb
  unfold kvModel kvRaftOf kvRaftSt bootEntries
  rw [List.foldl_map]
  suffices h : ∀ (l : List EntryM) (s : mvcc.Log × LeaseTable), (∀ e ∈ l, e.Type' = W32 1) →
      l.foldl (fun s e => kvEntrySt γk.c0 γk.ch0 s (EntryModel.ofM e)) s = s by
    rw [h]
    intro e hm
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
    exact (he k _ (List.getElem?_eq_getElem hk)).2.2.1
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons e l ih =>
    intro s hl
    rw [List.foldl_cons]
    have ht : e.Type' = W32 1 := hl e (List.mem_cons_self ..)
    have : kvEntrySt γk.c0 γk.ch0 s (EntryModel.ofM e) = s := by
      unfold kvEntrySt kvEntry kvTable
      simp only [EntryModel.ofM, ht]
      rfl
    rw [this]
    exact ih s (fun e' h' => hl e' (List.mem_cons_of_mem _ h'))

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A one-member `Main`'s named premises** (persistent; see the file header), for the member
`name` at the peer address `peer` and the client address `client` (the shared start's
configuration `cfgOk name name` and URLs `urls1`, the directory `dir1 peer`), at the bound `N` of
the apply thread's write tokens, the member id `id`, the peers' contexts `ctxs` and the bootstrap
log `boot`. -/
def premises (name peer client : GoString)
    (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry) : IProp GF :=
  iprop(
    (□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
      ⌜cfgOk name name cfg ∧ urls1 name peer client U ∧ γ.vs = [id] ∧
        γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧
        γ.boot = LogEntry.toEntries boot 0⌝ -∗
      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N (dir1 peer id)) ∗
    bootMarshal [id] ctxs (LogEntry.toEntries boot 0) ∗
    rnLoggerZapOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk)

instance premises_persistent (name peer client : GoString) (N : Nat) (id : w64)
    (ctxs : List (List w8)) (boot : List LogEntry) :
    Persistent (premises (GF := GF) name peer client N id ctxs boot) := by
  unfold premises; infer_instance

end defs

end etcdstart
end EtcdGrove
end Perennial
