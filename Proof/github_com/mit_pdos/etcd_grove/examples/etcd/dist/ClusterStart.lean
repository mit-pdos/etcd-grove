/- Lean-first (no Rocq counterpart).

# `etcdClusterStart`: the start of a `k`-member etcd deployment (D7, step (e); `notes/putget-dist-plan.md` §13)

Over the global ghost state (no heap), from the protocol registry and every member's two addresses unset:
the cluster's allocation once over the members' ids (`etcdstart.clusterAllocN`: raft's cluster with its
bootstrap log, the server's invariants, each member's slice, the client's `etcdKV`), then per member its
peer address set to rafthttp's protocol (`S5Draft.http_addr_set`, a PLACEHOLDER field taken as a hypothesis:
`S5Draft.lean`) and its client address set to serve etcd's table for its id at the cluster's view
(`etcdAddr_set` at `c.view`, `S2Interim.lean`; O1 option B, `notes/etcd-dist-plan.md` §18.3: the view is the
start's Lean value, no publication). It returns each member's share (`memberStartShare`: the cluster's
facts, every member's peer address fact, its slice, its address fact) and the client machines' share
(`clientStartShare`: the cluster's facts, each member's address fact), with the client's `etcdKV` apart, for
the start that allocates the client's invariant from it. A member's boot turns its share into `memberBoot`
(`etcdstart.memberBoot_of_slice`, at its own heap), whose request names are `kvCongr` to the view's.
(Until 2026-11-25 each member also had a publication name and invariant, `envPub_start`, and published its
view after its boot.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S5Draft
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AllocN

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS


/-! ## `etcdClusterStart`: the start of a `k`-member cluster (see the file header) -/

open go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart

/-- **A member of the cluster at the start**: its peer address (served by its raft handler), its client
address (served by etcd's gRPC API) and its member id. -/
structure ClusterMember where
  peer : GoString
  client : GoString
  id : w64

/-- **The cluster's ghost names** (what `etcdstart.clusterAllocN` chooses): raft's server names `γ`, the
KV names `γk`, the request ids' names, and per member id its store's names, certificate map,
revisions' map and storage registry. -/
structure ClusterNames [GooseExts] where
  γ : SrvRaft
  γk : KVNames
  issued : GName
  cnt : GName
  wn : GName
  fs : GName
  gen : GName
  idx : w64 → srvApi.KVSNames
  cok : w64 → GName
  rev : w64 → GName
  reg : w64 → GName
  /-- per member id, its lessor's name (#50 F7, L3: `clusterStartD` allocates it with its slot, injective over
  all of `w64`; the starts that link no lease contract pass `lsNone`) -/
  ls : w64 → GName
  /-- per member id, its auth names (#50 F7, L3: `clusterStartD` allocates them with their authorities, injective
  over all of `w64`; the other starts pass `auNone`) -/
  au : w64 → EtcdGrove.auth.AuthNames

/-- The constant lessor names of the starts that allocate none (`DistView.ofKV`'s). -/
def ClusterNames.lsNone : w64 → GName := fun _ => 0

/-- The constant auth names of the starts that allocate none (`DistView.ofKV`'s). -/
def ClusterNames.auNone : w64 → EtcdGrove.auth.AuthNames := fun _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- **The cluster's view** (`DistView`, O1 option B): its KV names, its members' lessor names `c.ls` and auth
names `c.au`, and auth off (the start of an auth-off cluster: every member's `memberUp`). At `lsNone`/`auNone`
it is `DistView.ofKV c.γk`. -/
def ClusterNames.view [GooseExts] (c : ClusterNames) : DistView := ⟨c.γk, c.ls, false, c.au⟩

/-- **The start's names are distinct per member** (over all of `w64`): what the lease contracts and the proposed
`Serve_dist`'s guarded premise need of `Γ.ls` and `Γ.au`. -/
def ClusterNames.NamesInj [GooseExts] (c : ClusterNames) : Prop :=
  (∀ a b, c.ls a = c.ls b → a = b) ∧ (∀ a b, c.au a = c.au b → a = b)

section clusterK
variable {GF : BundledGFunctors} [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
  [GoGlobalContext] [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
  [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **What `clusterAllocN` makes true of the names** (its pure post), for the peers `ps`, the bootstrap
log `boot`, the lease mode `lm`, the compaction mode `cmp`, `cret` and the members' ids `ids`. -/
abbrev ClusterOk (c : ClusterNames) (ps : List w64) (boot : List LogEntry) (lm : lease.Mode)
    (cmp : Bool) (cret : Nat) (ids : List w64) : Prop :=
  c.γ.vs = ps ∧ c.γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧
    c.γ.boot = LogEntry.toEntries boot 0 ∧
    c.γk.c0 = W64 0 ∧ c.γk.ch0 = apply.alarmChain false false false ∧ c.γk.log0 = [[], []] ∧
    c.γk.ids.issued = c.issued ∧ c.γk.ids.wn = c.wn ∧ c.γk.ids.fs = c.fs ∧ c.γk.ids.gen = c.gen ∧
    c.γk.cmp = cmp ∧ c.γk.cret = cret ∧ c.γk.lm = lm ∧ kvPfxOk c.γk ∧ ¬ clusterNoSnap c.γ.cl ∧
    (∀ id ∈ ids, lm = .revocable → idPfxOf (W16 (uint.Z id)) ∈ c.γk.gps)

/-- The cluster's persistent facts (`etcdstart.clusterFacts`) at the names `c`. -/
abbrev clusterFactsOf (c : ClusterNames) : IProp GF :=
  clusterFacts c.γ c.γk c.issued c.cnt c.wn c.fs c.gen

/-- Member `id`'s slice (`etcdstart.memberSlice`) at the names `c`, of the cluster of the ids `ids` with
the peers `ps`, their contexts `ctxs` and the bootstrap log `bl`. -/
abbrev memberSliceOf (c : ClusterNames) (ids ps : List w64) (ctxs : List (List w8)) (bl : List EntryM)
    (id : w64) : IProp GF :=
  memberSlice c.γ ps ctxs bl c.cnt c.wn c.fs c.gen (xsOf ids c.idx (idPfxOf (W16 (uint.Z id))))
    (c.idx id) (c.cok id) (c.rev id) (c.reg id) id

/-- **Every member's peer address serves rafthttp's protocol** (persistent; `S5Draft.httpAddrAt`). -/
def peerAddrFacts (S5 : S5Draft GF) (ms : List ClusterMember) : IProp GF :=
  iprop([∗list] m ∈ ms, S5.httpAddrAt m.peer)

instance peerAddrFacts_persistent (S5 : S5Draft GF) (ms : List ClusterMember) :
    Persistent (peerAddrFacts S5 ms) := by
  unfold peerAddrFacts; infer_instance

/-- **Member `m`'s share of the start** (of the cluster `ms` at the names `c`): the cluster's facts, every
member's peer address fact, its slice, and its client address set to serve etcd's table for its id at the
cluster's view. -/
def memberStartShare (S5 : S5Draft GF) (c : ClusterNames) (ms : List ClusterMember) (ps : List w64)
    (ctxs : List (List w8)) (bl : List EntryM) (m : ClusterMember) : IProp GF :=
  iprop(clusterFactsOf c ∗ peerAddrFacts S5 ms ∗ memberSliceOf c (ms.map (·.id)) ps ctxs bl m.id ∗
    etcdAddrAt m.client c.view m.id)

/-- **What every client machine gets of the start** (persistent): each member's client address fact at
the view `Γ`. -/
def clientSvcFacts (ms : List ClusterMember) (Γ : DistView) : IProp GF :=
  iprop([∗list] m ∈ ms, etcdAddrAt m.client Γ m.id)

instance clientSvcFacts_persistent (ms : List ClusterMember) (Γ : DistView) :
    Persistent (clientSvcFacts (GF := GF) ms Γ) := by
  unfold clientSvcFacts; infer_instance

/-- **The client machines' share of the start** (persistent): the cluster's facts, and each member's
client address fact at the cluster's view (`clientSvcFacts`). -/
def clientStartShare (c : ClusterNames) (ms : List ClusterMember) : IProp GF :=
  iprop(clusterFactsOf c ∗ clientSvcFacts ms c.view)

instance clientStartShare_persistent (c : ClusterNames) (ms : List ClusterMember) :
    Persistent (clientStartShare (GF := GF) c ms) := by
  unfold clientStartShare; infer_instance

/-- Every peer address set to rafthttp's protocol (`S5Draft.http_addr_set`, per member). -/
theorem peers_addr_start (S5 : S5Draft GF) (ns : List ClusterMember) :
    ⊢ regCtx -∗ ([∗list] m ∈ ns, addrUnset m.peer) ={⊤}=∗ peerAddrFacts S5 ns := by
  induction ns with
  | nil =>
    iintro #_ _
    imodintro
    iunfold peerAddrFacts
    iempintro
  | cons m ns ih =>
    iintro #Hreg Hs
    ihave Hs := BigSepL.bigSepL_cons.1 $$ Hs
    icases Hs with ⟨Ha, Hs⟩
    imod (S5.http_addr_set ⊤ m.peer) $$ Hreg Ha with #Hp
    imod ih $$ Hreg Hs with #Hps
    imodintro
    iunfold peerAddrFacts
    iunfold peerAddrFacts at Hps
    iapply BigSepL.bigSepL_cons.2
    iframe #

/-- Per member of `ns` (a part of the cluster `ms`), from its slice and its client address unset: its
client address set (`etcdAddr_set` at the cluster's view), its share; and the client machines' facts of
these members. -/
theorem members_svc_start (S5 : S5Draft GF) (c : ClusterNames) (ms : List ClusterMember)
    (ps : List w64) (ctxs : List (List w8)) (bl : List EntryM) (ns : List ClusterMember) :
    ⊢ regCtx -∗ clusterFactsOf c -∗ peerAddrFacts S5 ms -∗
      ([∗list] m ∈ ns, memberSliceOf c (ms.map (·.id)) ps ctxs bl m.id ∗ addrUnset m.client) ={⊤}=∗
        ([∗list] m ∈ ns, memberStartShare S5 c ms ps ctxs bl m) ∗ clientSvcFacts ns c.view := by
  induction ns with
  | nil =>
    iintro #_ #_ #_ _
    imodintro
    iunfold clientSvcFacts
    isplitl
    · iempintro
    · iempintro
  | cons m ns ih =>
    iintro #Hreg #Hcf #Hpf Hs
    ihave Hs := BigSepL.bigSepL_cons.1 $$ Hs
    icases Hs with ⟨⟨Hsl, Ha⟩, Hs⟩
    imod (etcdAddr_set ⊤ m.client c.view m.id) $$ Hreg Ha with #Hat
    imod ih $$ Hreg Hcf Hpf Hs with ⟨Hms, #Hcs⟩
    imodintro
    iunfold clientSvcFacts
    iunfold clientSvcFacts at Hcs
    isplitl [Hsl Hms]
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hsl]
      · unfold memberStartShare
        iframe Hsl
        iframe #
      · iexact Hms
    · iapply BigSepL.bigSepL_cons.2
      iframe #

/-- `clusterAllocN`'s slices over the ids, as `memberSliceOf` over the members. -/
theorem memberSlices_of (ms : List ClusterMember) (ps : List w64) (ctxs : List (List w8))
    (bl : List EntryM) (γ : SrvRaft) (γk : KVNames) (issued cnt wn fs gen : GName)
    (idx : w64 → srvApi.KVSNames) (cok rev reg : w64 → GName) :
    ([∗list] id ∈ ms.map (·.id), memberSlice (GF := GF) γ ps ctxs bl cnt wn fs gen
        (xsOf (ms.map (·.id)) idx (idPfxOf (W16 (uint.Z id)))) (idx id) (cok id) (rev id) (reg id) id) ⊢
      [∗list] m ∈ ms, memberSliceOf (GF := GF)
        (⟨γ, γk, issued, cnt, wn, fs, gen, idx, cok, rev, reg, ClusterNames.lsNone, ClusterNames.auNone⟩ : ClusterNames) (ms.map (·.id)) ps ctxs bl
        m.id := by
  rw [BigSepL.bigSepL_map]

/-- **`etcdClusterStart`: the start of a `k`-member cluster over the global ghost state** (see the file
header): for the members `ms` (their ids in `bootstrap`'s peers `ps` up to order), from the protocol
registry and every member's peer and client addresses unset, the cluster's names `c` (`clusterAllocN`'s
post, `ClusterOk`), each member's share, the client machines' share, and, in the lease mode `none`, the
client's `etcdKV`. No heap, no axiom of its own: `clusterAllocN` (proved), `S5Draft.http_addr_set` (a
hypothesis, `S5`), `etcdAddr_set` (proved over grpc's `grpc_addr_set`; the table `etcdSvc` its axiom). -/
theorem etcdClusterStart (S5 : S5Draft GF) (ms : List ClusterMember) (ps : List w64)
    (hperm : ps.Perm (ms.map (·.id))) (hne : ms ≠ [])
    (ctxs : List (List w8)) (boot : List LogEntry) (Hbc : BootCore ps ctxs boot)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hrb2 : receiptBound GF + boot.length ≤ 2 ^ 61)
    (lm : lease.Mode) (hap : lm = .revocable → leaseIdsApart (ms.map (·.id)))
    (cmp : Bool) (cret : Nat) :
    ⊢ regCtx -∗ ([∗list] m ∈ ms, addrUnset m.peer ∗ addrUnset m.client) ={⊤}=∗
      ∃ c : ClusterNames, ⌜ClusterOk c ps boot lm cmp cret (ms.map (·.id))⌝ ∗
        ([∗list] m ∈ ms, memberStartShare S5 c ms ps ctxs (LogEntry.toEntries boot 0) m) ∗
        clientStartShare c ms ∗
        (if decide (lm ≠ .none) then iprop(True) else
          etcdKV c.γk (kvModelSt c.γk (bootEntries (LogEntry.toEntries boot 0)))) := by
  obtain ⟨m0, ms', rfl⟩ : ∃ m0 ms', ms = m0 :: ms' := by
    cases ms with
    | nil => exact absurd rfl hne
    | cons m0 ms' => exact ⟨m0, ms', rfl⟩
  have hid0 : m0.id ∈ (m0 :: ms').map (·.id) := List.mem_cons_self ..
  iintro #Hreg Hs
  ihave Hs := BigSepL.bigSepL_sep_eqv.1 $$ Hs
  icases Hs with ⟨Hp, Hc⟩
  imod (peers_addr_start S5 (m0 :: ms')) $$ Hreg Hp with #Hpf
  imod (clusterAllocN (GF := GF) ((m0 :: ms').map (·.id)) ps hperm m0.id hid0 ctxs boot Hbc Hrb Hrb2
      lm hap cmp cret)
    with ⟨%γ, %γk, %issued, %cnt, %wn, %fs, %gen, %idx, %cok, %rev, %reg, %Hγ, #Hf, Hsl, Hetcd⟩
  ihave Hsl := memberSlices_of (GF := GF) (m0 :: ms') ps ctxs (LogEntry.toEntries boot 0) γ γk issued
    cnt wn fs gen idx cok rev reg $$ Hsl
  ihave Hs : [∗list] m ∈ m0 :: ms', memberSliceOf (GF := GF)
      (⟨γ, γk, issued, cnt, wn, fs, gen, idx, cok, rev, reg, ClusterNames.lsNone, ClusterNames.auNone⟩ : ClusterNames)
      ((m0 :: ms').map (·.id)) ps ctxs (LogEntry.toEntries boot 0) m.id ∗ addrUnset m.client $$ [Hsl Hc]
  · iapply BigSepL.bigSepL_sep_eqv.2
    isplitl [Hsl]
    · iexact Hsl
    · iexact Hc
  imod (members_svc_start S5 (⟨γ, γk, issued, cnt, wn, fs, gen, idx, cok, rev, reg, ClusterNames.lsNone, ClusterNames.auNone⟩ : ClusterNames)
      (m0 :: ms') ps ctxs (LogEntry.toEntries boot 0) (m0 :: ms'))
    $$ Hreg Hf Hpf Hs with ⟨Hms, #Hcs⟩
  imodintro
  iexists ⟨γ, γk, issued, cnt, wn, fs, gen, idx, cok, rev, reg, ClusterNames.lsNone, ClusterNames.auNone⟩
  isplitr
  · ipureintro
    exact Hγ
  isplitl [Hms]
  · iexact Hms
  isplitr [Hetcd]
  · iunfold clientStartShare
    iframe #
  · iexact Hetcd

end clusterK

end etcd_dist
end EtcdGrove
end Perennial

end
