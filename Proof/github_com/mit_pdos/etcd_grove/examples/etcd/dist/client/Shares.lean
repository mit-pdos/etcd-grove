/- Lean-first (no Rocq counterpart).

# `etcd/dist/client`: the machines' shares of the full dispatch (F8, `notes/etcd-dist-plan.md` §27.2 "The shares")

What the start hands each client-side machine of a deployment, at the global ghost state (`[Gg : GooseGlobalGS]`,
the boot's), under the net extension's registry `π` and the remote library's names `ρ`:
- `wlShare w eps ns`: workload `w`'s orchestrator machine, `eps` the members' client addresses (in the members'
  order), `ns` the workload's client machines' addresses. By `w.kind` (the Go switch's `w.Kind == k`):

  | Kind | Share |
  |---|---|
  | 0 `kv` | `kvOrchPre ns w.ops` (M1) |
  | 1 `watch` | `watchShare writersShare eps ns` (N10a) |
  | 2 `cache` | `cacheShare eps ns` (F6; the same as watch's) |
  | 3 `compact` | `compactShare eps` (F5) |
  | 4 `putget` | `putgetShare eps` (N9a) |
  | 5 `auth` | `authShare eps ns` (`client/AuthShares.lean`; F7 S14) |
  | 6 `authLease` | `False` (D2: its class is a boot hypothesis, `AuthLeaseBootNC`) |
  | 7 `leaseRead` | `∃ Γ, [∗list] a ∈ eps, leaseMember Γ a` |
  | 8 `leaseCatchup` | the same with `Γ.kv.lm = .mono` and `Γ.ls` injective |
  | 9 `leaseExpiry` | the same at `.revocable` |
  | 10 `durable` | `durableShare eps` (N9a) |
  | other | `True` |

- `wlNodeShare w c addr eps`: client machine `c` of workload `w`, at `addr`, `eps` the members' client addresses
  (not rotated; F7 S13), `eps'` those rotated by `c`: `kv` `kvNodePre c addr eps'` (M1); `watch`, `cache`
  `writerNodePre addr eps'` (the writer machine's share: `nodeWatchPre` without its machine-local and pure parts,
  `nodeWatchPre_of`); `auth` `authNodePre addr eps` (`client/AuthShares.lean`, at the endpoints unrotated, as
  `NodeMain` hands them to `principalOp`; F7 S13, linked by `wp_NodeMainAuth`); other kinds `True` (they have no client machine: `NodeMain` returns).
- `orchShareF d j`, `nodeShareF d n`: those at the arguments the dispatch computes from the deployment (as M1's
  `orchShare`/`nodeShare`, `client/KvDefs.lean`), with their `_eq` laws.

The pure facts the arms' callees take beyond the shares are not in them: the boot discharges the machine-level
ones (`Nonempty (WEnv GF)`, the thread bound, `EtcdError` an `errors.As` target), and the dispatch derives the
deployment-level ones from `d.WellFormed` (`wellFormed_wlPure`: the workload's bounds; `members_plain`,
`rotateL_plain`: the endpoints are plain).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KvDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterWire
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WatchWorkDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CacheWorkDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CompactWorkDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KVWorkDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.LeaseDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthShares
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AddrPlain
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Orch
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Node

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net client
open etcd_dist.view etcd_dist_client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
open github_com.mit_pdos.etcd_grove.examples.lib.remote

/-! ## The deployment-level pure facts -/

section pure
variable [GooseExts]

/-- **What the dispatch needs of a workload** beyond its share, from a well-formed deployment
(`wellFormed_wlPure`): its client machines fewer than `2 ^ 31` (`NodeMain`'s `Rotate`); watch's and cache's
operation counts (`RunWatch`, `RunCache`: `len(nodes) * nops` within `int`); durable's client count not negative
(`RunDurable`). -/
def wlPure (w : Workload) : Prop :=
  0 ≤ sint.Z w.goNodeCount ∧ sint.Z w.goNodeCount < 2 ^ 31 ∧
  ((w.kind = W64 1 ∨ w.kind = W64 2) → 0 ≤ sint.Z w.ops ∧ sint.Z w.clients * sint.Z w.ops < 2 ^ 62) ∧
  (w.kind = W64 10 → 0 ≤ sint.Z w.clients)

/-- **A well-formed deployment's workloads** satisfy `wlPure`: from their typed encodings and `BoundsOk`. -/
theorem wellFormed_wlPure {d : Deployment} (hw : d.WellFormed) {w : Workload} (hm : w ∈ d.workloads) :
    wlPure w := by
  obtain ⟨t, he, hwf⟩ := hw
  obtain ⟨-, -, -, hws, -⟩ := he
  have hb : ∀ tw ∈ t.workloads, tw.BoundsOk := by grind [typed.Deployment.WellFormed]
  obtain ⟨tw, htw, henc⟩ := forall₂_mem_right hws w hm
  have hbw := hb tw htw
  cases tw with
  | kv c o =>
    obtain ⟨hk, hc, ho⟩ := henc
    simp only [typed.Workload.BoundsOk] at hbw
    have hn : w.goNodeCount = w.clients := by simp [Workload.goNodeCount, hk]
    refine ⟨by rw [hn]; omega, by rw [hn]; omega, fun h => ?_, fun h => ?_⟩
    · rcases h with h | h <;> rw [hk] at h <;> exact absurd h (by decide)
    · rw [hk] at h; exact absurd h (by decide)
  | watch c o =>
    obtain ⟨hk, hc, ho⟩ := henc
    simp only [typed.Workload.BoundsOk] at hbw
    have hn : w.goNodeCount = w.clients := by simp [Workload.goNodeCount, hk]
    refine ⟨by rw [hn]; omega, by rw [hn]; omega, fun _ => ⟨by omega, ?_⟩, fun h => ?_⟩
    · rw [hc, ho]; exact_mod_cast hbw.2
    · rw [hk] at h; exact absurd h (by decide)
  | cache c o =>
    obtain ⟨hk, hc, ho⟩ := henc
    simp only [typed.Workload.BoundsOk] at hbw
    have hn : w.goNodeCount = w.clients := by simp [Workload.goNodeCount, hk]
    refine ⟨by rw [hn]; omega, by rw [hn]; omega, fun _ => ⟨by omega, ?_⟩, fun h => ?_⟩
    · rw [hc, ho]; exact_mod_cast hbw.2
    · rw [hk] at h; exact absurd h (by decide)
  | durable c =>
    obtain ⟨hk, hc⟩ := henc
    have hn : w.goNodeCount = W64 0 := by simp [Workload.goNodeCount, hk]
    refine ⟨by rw [hn]; decide, by rw [hn]; decide, fun h => ?_, fun _ => by omega⟩
    rcases h with h | h <;> rw [hk] at h <;> exact absurd h (by decide)
  | auth =>
    have hk : w.kind = W64 5 := henc
    have hn : w.goNodeCount = W64 4 := by simp [Workload.goNodeCount, hk]
    refine ⟨by rw [hn]; decide, by rw [hn]; decide, fun h => ?_, fun h => ?_⟩
    · rcases h with h | h <;> rw [hk] at h <;> exact absurd h (by decide)
    · rw [hk] at h; exact absurd h (by decide)
  | _ =>
    have hk := henc
    simp only [typed.Workload.Encodes] at hk
    have hn : w.goNodeCount = W64 0 := by simp [Workload.goNodeCount, hk]
    refine ⟨by rw [hn]; decide, by rw [hn]; decide, fun h => ?_, fun h => ?_⟩
    · rcases h with h | h <;> rw [hk] at h <;> exact absurd h (by decide)
    · rw [hk] at h; exact absurd h (by decide)

theorem mem_rotateL {α : Type} [Inhabited α] {xs : List α} {i : Nat} {x : α} (h : x ∈ rotateL xs i) :
    x ∈ xs := by
  unfold rotateL at h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
  have hlen : 0 < xs.length := by have := List.mem_range.1 hj; omega
  have hk : (i + j) % xs.length < xs.length := Nat.mod_lt _ hlen
  first
    | (rw [getElem!_pos xs ((i + j) % xs.length) hk]; exact List.getElem_mem hk)
    | (simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some];
       exact List.getElem_mem hk)
    | simp [hk]

/-- The client addresses of a well-formed deployment's members are plain endpoints. -/
theorem members_plain {d : Deployment} (Hd : d.WellFormed) :
    plainEndpoints (d.members.map Member.client) := by
  obtain ⟨hne, -⟩ := Hd.members
  refine ⟨fun h => hne (List.map_eq_nil_iff.1 h), fun ep hep => ?_⟩
  obtain ⟨m, hm', rfl⟩ := List.mem_map.1 hep
  apply addrOk_plainEndpoint
  apply Hd.addrs.2
  simp only [Deployment.addrs]
  exact List.mem_append_left _ (List.mem_flatMap.2 ⟨m, hm', by simp⟩)

/-- A rotation of plain endpoints is plain. -/
theorem plainEndpoints_rotateL {eps : List GoString} (h : plainEndpoints eps) (c : Nat) :
    plainEndpoints (rotateL eps c) := by
  obtain ⟨hne, hpl⟩ := h
  refine ⟨fun h => ?_, fun ep hep => hpl ep (mem_rotateL hep)⟩
  have := congrArg List.length h
  rw [rotateL_length] at this
  exact hne (List.eq_nil_of_length_eq_zero this)

/-- The rotated client addresses of a well-formed deployment are plain endpoints. -/
theorem rotateL_plain {d : Deployment} (Hd : d.WellFormed) (c : Nat) :
    plainEndpoints (rotateL (d.members.map Member.client) c) :=
  plainEndpoints_rotateL (members_plain Hd) c

end pure

/-! ## The shares -/

section shares
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt] [GoGlobalContext]
variable [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.raft.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS] [ρ : RemoteGS]

/-- **A lease workload's share**: a view `Γ` of the cluster whose lease facts hold at every client address
(`leaseMember`). -/
def leaseShare (P : DistView → Prop) (eps : List GoString) : IProp GF :=
  iprop(∃ Γ : DistView, ⌜P Γ⌝ ∗ [∗list] a ∈ eps, leaseMember (Gg := Gg) Γ a)

/-- **A writer machine's share** (watch's and cache's client machines, at the global ghost state): a view `Γ`
with auth off whose members serve every endpoint, and `addr` serving the writer service at `Γ`. The machine's
local and pure parts of `nodeWatchPre` are the boot's (`nodeWatchPre_of`). -/
def writerNodePre (addr : GoString) (eps : List GoString) : IProp GF :=
  iprop(∃ Γ : DistView, ⌜Γ.auth = false⌝ ∗ membersAt (Gg := Gg) eps Γ ∗
    svcAddr (Gg := Gg) (writerSvcG (Gg := Gg) Γ) addr)

/-- **Workload `w`'s orchestrator share** (see the file header). -/
def wlShare (w : Workload) (eps ns : List GoString) : IProp GF :=
  if w.kind = W64 0 then kvOrchPre (Gg := Gg) ns w.ops
  else if w.kind = W64 1 then watchShare (Gg := Gg) (writersShare (Gg := Gg)) eps ns
  else if w.kind = W64 2 then cacheShare (Gg := Gg) eps ns
  else if w.kind = W64 3 then compactShare (Gg := Gg) eps
  else if w.kind = W64 4 then putgetShare (Gg := Gg) eps
  else if w.kind = W64 5 then authShare (Gg := Gg) eps ns
  else if w.kind = W64 6 then iprop(False)
  else if w.kind = W64 7 then leaseShare (Gg := Gg) (fun _ => True) eps
  else if w.kind = W64 8 then
    leaseShare (Gg := Gg) (fun Γ => Γ.kv.lm = .mono ∧ ∀ a b : w64, Γ.ls a = Γ.ls b → a = b) eps
  else if w.kind = W64 9 then
    leaseShare (Gg := Gg) (fun Γ => Γ.kv.lm = .revocable ∧ ∀ a b : w64, Γ.ls a = Γ.ls b → a = b) eps
  else if w.kind = W64 10 then durableShare (Gg := Gg) eps
  else iprop(True)

/-- **Client machine `c`'s share in workload `w`** (see the file header), at the members' client addresses `eps`
**not rotated** (F7 S13, W-6's rotation gap): the kv and writer arms at `eps` rotated by `c` (what `NodeMain` hands
their machines); the auth arm `authNodePre addr eps` at `eps` itself (what `NodeMain` hands `principalOp`;
`NodeMainAuth`, linked in `DispatchLinked`). -/
def wlNodeShare (w : Workload) (c : w64) (addr : GoString) (eps : List GoString) : IProp GF :=
  if w.kind = W64 0 then kvNodePre (Gg := Gg) c addr (rotateL eps (sint.nat c))
  else if w.kind = W64 1 ∨ w.kind = W64 2 then writerNodePre (Gg := Gg) addr (rotateL eps (sint.nat c))
  else if w.kind = W64 5 then authNodePre (Gg := Gg) addr eps
  else iprop(True)

/-! ### The arms (each a law, so that no caller unfolds the chain) -/

section arms
variable {w : Workload} {eps ns : List GoString}

theorem wlShare_kv (h : w.kind = W64 0) : wlShare (Gg := Gg) w eps ns = kvOrchPre (Gg := Gg) ns w.ops := by
  unfold wlShare; rw [if_pos h]

theorem wlShare_watch (h : w.kind = W64 1) :
    wlShare (Gg := Gg) w eps ns = watchShare (Gg := Gg) (writersShare (Gg := Gg)) eps ns := by
  unfold wlShare; rw [if_neg (by rw [h]; decide), if_pos h]

theorem wlShare_cache (h : w.kind = W64 2) : wlShare (Gg := Gg) w eps ns = cacheShare (Gg := Gg) eps ns := by
  unfold wlShare; rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]

theorem wlShare_compact (h : w.kind = W64 3) : wlShare (Gg := Gg) w eps ns = compactShare (Gg := Gg) eps := by
  unfold wlShare; rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]

theorem wlShare_putget (h : w.kind = W64 4) : wlShare (Gg := Gg) w eps ns = putgetShare (Gg := Gg) eps := by
  unfold wlShare; rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]

theorem wlShare_auth (h : w.kind = W64 5) : wlShare (Gg := Gg) w eps ns = authShare (Gg := Gg) eps ns := by
  unfold wlShare; rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]

theorem wlShare_authLease (h : w.kind = W64 6) : wlShare (Gg := Gg) w eps ns = iprop(False) := by
  unfold wlShare; rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]

theorem wlShare_leaseRead (h : w.kind = W64 7) :
    wlShare (Gg := Gg) w eps ns = leaseShare (Gg := Gg) (fun _ => True) eps := by
  unfold wlShare; rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]

theorem wlShare_leaseCatchup (h : w.kind = W64 8) :
    wlShare (Gg := Gg) w eps ns =
      leaseShare (Gg := Gg) (fun Γ => Γ.kv.lm = .mono ∧ ∀ a b : w64, Γ.ls a = Γ.ls b → a = b) eps := by
  unfold wlShare; rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]

theorem wlShare_leaseExpiry (h : w.kind = W64 9) :
    wlShare (Gg := Gg) w eps ns =
      leaseShare (Gg := Gg) (fun Γ => Γ.kv.lm = .revocable ∧ ∀ a b : w64, Γ.ls a = Γ.ls b → a = b) eps := by
  unfold wlShare; rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]

theorem wlShare_durable (h : w.kind = W64 10) : wlShare (Gg := Gg) w eps ns = durableShare (Gg := Gg) eps := by
  unfold wlShare; rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]

theorem wlShare_other (h : ¬ kindKnown w.kind) : wlShare (Gg := Gg) w eps ns = iprop(True) := by
  unfold wlShare
  rw [if_neg (fun he => h (by rw [he]; decide)), if_neg (fun he => h (by rw [he]; decide)), if_neg (fun he => h (by rw [he]; decide)), if_neg (fun he => h (by rw [he]; decide)), if_neg (fun he => h (by rw [he]; decide)), if_neg (fun he => h (by rw [he]; decide)), if_neg (fun he => h (by rw [he]; decide)), if_neg (fun he => h (by rw [he]; decide)), if_neg (fun he => h (by rw [he]; decide)), if_neg (fun he => h (by rw [he]; decide)), if_neg (fun he => h (by rw [he]; decide))]

variable {c : w64} {addr : GoString}

theorem wlNodeShare_kv (h : w.kind = W64 0) :
    wlNodeShare (Gg := Gg) w c addr eps = kvNodePre (Gg := Gg) c addr (rotateL eps (sint.nat c)) := by
  unfold wlNodeShare; rw [if_pos h]

theorem wlNodeShare_writer (h : w.kind = W64 1 ∨ w.kind = W64 2) :
    wlNodeShare (Gg := Gg) w c addr eps = writerNodePre (Gg := Gg) addr (rotateL eps (sint.nat c)) := by
  unfold wlNodeShare
  rw [if_neg (by rcases h with h | h <;> rw [h] <;> decide), if_pos h]

theorem wlNodeShare_auth (h : w.kind = W64 5) :
    wlNodeShare (Gg := Gg) w c addr eps = authNodePre (Gg := Gg) addr eps := by
  unfold wlNodeShare
  rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]

theorem wlNodeShare_other (h0 : w.kind ≠ W64 0) (h12 : ¬ (w.kind = W64 1 ∨ w.kind = W64 2))
    (h5 : w.kind ≠ W64 5) : wlNodeShare (Gg := Gg) w c addr eps = iprop(True) := by
  unfold wlNodeShare; rw [if_neg h0, if_neg h12, if_neg h5]

end arms

/-- **The orchestrator machine `j`'s share**: `wlShare` of workload `j` at the members' client addresses and the
workload's client machines, when the deployment has a workload `j` (otherwise the program returns at once). -/
def orchShareF (d : Deployment) (j : w64) : IProp GF :=
  if 0 ≤ sint.Z j then
    match d.workloads[sint.nat j]?, d.nodes[sint.nat j]? with
    | some w, some ns => wlShare (Gg := Gg) w (d.members.map Member.client) ns
    | _, _ => iprop(True)
  else iprop(True)

/-- **The `n`-th client machine's share**: `wlNodeShare` at its workload, its index `c` in it, its address,
and the members' client addresses (`wlNodeShare` rotates them by `c` where its arm needs it), when the deployment
has an `n`-th client machine (otherwise the program returns at once). -/
def nodeShareF (d : Deployment) (n : w64) : IProp GF :=
  if 0 ≤ sint.Z n then
    match d.nodeList[sint.nat n]? with
    | some (w, c, a) => wlNodeShare (Gg := Gg) w (W64 c) a (d.members.map Member.client)
    | none => iprop(True)
  else iprop(True)

/-- **Law**: workload `j`'s share, when the deployment has a workload `j`. -/
theorem orchShareF_eq (d : Deployment) (j : w64) (w : Workload) (ns : List GoString) (h0 : 0 ≤ sint.Z j)
    (hw : d.workloads[sint.nat j]? = some w) (hns : d.nodes[sint.nat j]? = some ns) :
    orchShareF (Gg := Gg) d j = wlShare (Gg := Gg) w (d.members.map Member.client) ns := by
  unfold orchShareF; rw [if_pos h0, hw, hns]

/-- **Law**: the `n`-th client machine's share, when the deployment has an `n`-th client machine. -/
theorem nodeShareF_eq (d : Deployment) (n : w64) (w : Workload) (c : Nat) (a : GoString) (h0 : 0 ≤ sint.Z n)
    (hn : d.nodeList[sint.nat n]? = some (w, c, a)) :
    nodeShareF (Gg := Gg) d n = wlNodeShare (Gg := Gg) w (W64 c) a (d.members.map Member.client) := by
  unfold nodeShareF; rw [if_pos h0, hn]

end shares

/-! ## A writer machine's share, with its local and pure parts -/

section onMachine
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

/-- **`nodeWatchPre` from the writer machine's share** and the machine's level token, at the boot's pure
facts. -/
theorem nodeWatchPre_of (addr : GoString) (eps : List GoString) (hV : Nonempty (WEnv GF))
    (htb : threadBound GF ≤ 2 ^ 30) (hpl : plainEndpoints eps)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    levelTok 0 ∗ writerNodePre (Gg := hG.goose_globalGS) addr eps ⊢ nodeWatchPre addr eps := by
  iintro ⟨Hlt, Hw⟩
  iunfold writerNodePre at Hw
  icases Hw with ⟨%Γ, %Hauth, #Hm, #Ha⟩
  iunfold nodeWatchPre
  iframe Hlt
  iexists Γ
  isplitr
  · ipureintro; exact ⟨Hauth, hV, htb, hpl, hAs⟩
  isplitl []
  · iexact Hm
  · iexact Ha

end onMachine

end etcd_dist
end EtcdGrove
end Perennial

end
