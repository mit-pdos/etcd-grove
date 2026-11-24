/- Lean-first (no Rocq counterpart).

# The start of a `k`-member etcd deployment, over the interim cross-machine vocabulary (D7, step (a))

`notes/etcd-dist-plan.md`, "D7", order of work (a): `putget_start` (`dist/putget/TopLevelRobustness.lean`)
for any list of members. A member is its client address and its member id; the start allocates its
publication name `γE` with the publication invariant at its `Pub id` (`envPub_start`) and sets its client
address to serve etcd's KV calls for `(γE, id)` (`etcdAddr_set`), and hands the member its
`memberSvcShare`. Every client machine gets the same persistent `clientSvcFacts`: each member's address
fact and its publication invariant.

Over the interim vocabulary of `S2Interim.lean` (`notes/putget-dist-plan.md` §12: the address fact is
axiomatized, `etcdAddrRaw`/`etcdAddr_set`, until #24's switch defines it). The cluster's ghost state
(D7's steps (c)-(e): raft's `cluster_alloc_bootG`, the server's allocation at the global classes) joins
this start once it is stated over the global ghost state; until then it is not part of it. The peer
addresses are not set here: the raft transport across machines is phase 7 S5's.

# `etcdClusterStart`: the whole start of a `k`-member cluster (D7, step (e); `notes/putget-dist-plan.md` §13)

Over the global ghost state (no heap), from the protocol registry and every member's two addresses unset:
the cluster's allocation once over the members' ids (`etcdstart.clusterAllocN`: raft's cluster with its
bootstrap log, the server's invariants, each member's slice, the client's `etcdKV`), then per member its
peer address set to rafthttp's protocol (`S5Draft.http_addr_set`, a PLACEHOLDER field taken as a hypothesis:
`S5Draft.lean`), its publication name and invariant (`envPub_start`) and its client address set
(`etcdAddr_set`, interim, `S2Interim.lean`). It returns each member's share (`memberStartShare`: the
cluster's facts, every member's peer address fact, its slice, its address and publication facts) and the
client machines' share (`clientStartShare`: the cluster's facts, each member's address fact and publication
invariant), with the client's `etcdKV` apart, for the machine or the start that allocates the client's
invariant from it. A member's boot turns its share into `memberBoot` (`etcdstart.memberBoot_of_slice`, at
its own heap); a member publishes at `Pub c id`, a function of the cluster's names (D7 §4: the views agree
with them).
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

section start
variable {GF : BundledGFunctors} [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
  [GoGlobalContext] [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
  [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **Member `id`'s share of the start** (client address `a`, publication name `γE`): its address set to
serve etcd's KV calls for `(γE, id)`, its half of the publication token, the publication invariant at
`Pub`. -/
def memberSvcShare (a : GoString) (γE : GName) (id : w64) (Pub : EnvView → IProp GF) : IProp GF :=
  iprop(etcdAddrAt a γE id ∗ envPubHalf γE ∗ envPubInv γE Pub)

/-- **What every client machine gets of the start** (persistent): for each member (its address and id,
with its publication name), its address fact and its publication invariant. -/
def clientSvcFacts (L : List ((GoString × w64) × GName)) (Pub : w64 → EnvView → IProp GF) :
    IProp GF :=
  iprop([∗list] p ∈ L, etcdAddrAt p.1.1 p.2 p.1.2 ∗ envPubInv p.2 (Pub p.1.2))

instance clientSvcFacts_persistent (L : List ((GoString × w64) × GName))
    (Pub : w64 → EnvView → IProp GF) : Persistent (clientSvcFacts L Pub) := by
  unfold clientSvcFacts; infer_instance

/-- **The start for a list of members** (#24's §1.3 steps 1-4, for `k` members), given the protocol
registry: each member's publication name and invariant, its address set; the members' shares and the
clients' facts. -/
theorem cluster_svc_start (Pub : w64 → EnvView → IProp GF) (ms : List (GoString × w64)) :
    ⊢ regCtx -∗ ([∗list] m ∈ ms, addrUnset m.1) ={⊤}=∗
      ∃ γEs : List GName, ⌜γEs.length = ms.length⌝ ∗
        ([∗list] p ∈ ms.zip γEs, memberSvcShare p.1.1 p.2 p.1.2 (Pub p.1.2)) ∗
        clientSvcFacts (ms.zip γEs) Pub := by
  induction ms with
  | nil =>
    iintro #_ _
    imodintro
    iexists []
    iunfold clientSvcFacts
    isplitr
    · ipureintro; rfl
    isplitl
    · iempintro
    · iempintro
  | cons m ms ih =>
    iintro #Hreg Hs
    ihave Hs := BigSepL.bigSepL_cons.1 $$ Hs
    icases Hs with ⟨Ha, Hs⟩
    imod (envPub_start ⊤ (Pub m.2)) with ⟨%γE, Hhalf, #Hinv⟩
    imod (etcdAddr_set ⊤ m.1 γE m.2) $$ Hreg Ha with #Hat
    imod ih $$ Hreg Hs with ⟨%γEs, %Hlen, Hms, #Hcs⟩
    imodintro
    iexists γE :: γEs
    simp only [List.zip_cons_cons, List.length_cons, Hlen]
    iunfold clientSvcFacts
    iunfold clientSvcFacts at Hcs
    isplitr
    · ipureintro; simp [Hlen]
    isplitl [Hhalf Hms]
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hhalf]
      · unfold memberSvcShare
        iframe Hhalf
        iframe #
      · iexact Hms
    · iapply BigSepL.bigSepL_cons.2
      iframe #

end start

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

/-- **Member `m`'s share of the start** (of the cluster `ms` at the names `c`; its publication name `γE`
and what it publishes, `Pub`): the cluster's facts, every member's peer address fact, its slice, and its
client address and publication facts (`memberSvcShare`). -/
def memberStartShare (S5 : S5Draft GF) (c : ClusterNames) (ms : List ClusterMember) (ps : List w64)
    (ctxs : List (List w8)) (bl : List EntryM) (m : ClusterMember) (γE : GName)
    (Pub : EnvView → IProp GF) : IProp GF :=
  iprop(clusterFactsOf c ∗ peerAddrFacts S5 ms ∗ memberSliceOf c (ms.map (·.id)) ps ctxs bl m.id ∗
    memberSvcShare m.client γE m.id Pub)

/-- The members with their publication names, as `clientSvcFacts` takes them (client address, id). -/
def svcList (L : List (ClusterMember × GName)) : List ((GoString × w64) × GName) :=
  L.map (fun p => ((p.1.client, p.1.id), p.2))

/-- **The client machines' share of the start** (persistent): the cluster's facts, and each member's
client address fact and publication invariant (`clientSvcFacts`). -/
def clientStartShare (c : ClusterNames) (L : List (ClusterMember × GName))
    (Pub : w64 → EnvView → IProp GF) : IProp GF :=
  iprop(clusterFactsOf c ∗ clientSvcFacts (svcList L) Pub)

instance clientStartShare_persistent (c : ClusterNames) (L : List (ClusterMember × GName))
    (Pub : w64 → EnvView → IProp GF) : Persistent (clientStartShare c L Pub) := by
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
publication name and invariant (`envPub_start`), its client address set (`etcdAddr_set`), its share; and
the client machines' facts of these members. -/
theorem members_svc_start (S5 : S5Draft GF) (c : ClusterNames) (ms : List ClusterMember)
    (ps : List w64) (ctxs : List (List w8)) (bl : List EntryM) (Pub : w64 → EnvView → IProp GF)
    (ns : List ClusterMember) :
    ⊢ regCtx -∗ clusterFactsOf c -∗ peerAddrFacts S5 ms -∗
      ([∗list] m ∈ ns, memberSliceOf c (ms.map (·.id)) ps ctxs bl m.id ∗ addrUnset m.client) ={⊤}=∗
      ∃ γEs : List GName, ⌜γEs.length = ns.length⌝ ∗
        ([∗list] p ∈ ns.zip γEs, memberStartShare S5 c ms ps ctxs bl p.1 p.2 (Pub p.1.id)) ∗
        clientSvcFacts (svcList (ns.zip γEs)) Pub := by
  induction ns with
  | nil =>
    iintro #_ #_ #_ _
    imodintro
    iexists []
    simp only [svcList, List.zip_nil_left, List.map_nil]
    iunfold clientSvcFacts
    isplitr
    · ipureintro; trivial
    isplitl
    · iempintro
    · iempintro
  | cons m ns ih =>
    iintro #Hreg #Hcf #Hpf Hs
    ihave Hs := BigSepL.bigSepL_cons.1 $$ Hs
    icases Hs with ⟨⟨Hsl, Ha⟩, Hs⟩
    imod (envPub_start ⊤ (Pub m.id)) with ⟨%γE, Hhalf, #Hinv⟩
    imod (etcdAddr_set ⊤ m.client γE m.id) $$ Hreg Ha with #Hat
    imod ih $$ Hreg Hcf Hpf Hs with ⟨%γEs, %Hlen, Hms, #Hcs⟩
    imodintro
    iexists γE :: γEs
    simp only [List.zip_cons_cons, List.length_cons, Hlen, svcList, List.map_cons]
    iunfold clientSvcFacts
    iunfold clientSvcFacts at Hcs
    isplitr
    · ipureintro; trivial
    isplitl [Hsl Hhalf Hms]
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hsl Hhalf]
      · unfold memberStartShare memberSvcShare
        iframe Hsl Hhalf
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
        (⟨γ, γk, issued, cnt, wn, fs, gen, idx, cok, rev, reg⟩ : ClusterNames) (ms.map (·.id)) ps ctxs bl
        m.id := by
  rw [BigSepL.bigSepL_map]

/-- **`etcdClusterStart`: the start of a `k`-member cluster over the global ghost state** (see the file
header): for the members `ms` (their ids in `bootstrap`'s peers `ps` up to order), from the protocol
registry and every member's peer and client addresses unset, the cluster's names `c` (`clusterAllocN`'s
post, `ClusterOk`), a publication name per member, each member's share at its `Pub c id`, the client
machines' share, and, in the lease mode `none`, the client's `etcdKV`. No heap, no axiom of its own:
`clusterAllocN` (proved), `S5Draft.http_addr_set` (a hypothesis, `S5`), `envPub_start` (proved),
`etcdAddr_set` (interim axiom A2). -/
theorem etcdClusterStart (S5 : S5Draft GF) (ms : List ClusterMember) (ps : List w64)
    (hperm : ps.Perm (ms.map (·.id))) (hne : ms ≠ [])
    (ctxs : List (List w8)) (boot : List LogEntry) (Hbc : BootCore ps ctxs boot)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hrb2 : receiptBound GF + boot.length ≤ 2 ^ 61)
    (lm : lease.Mode) (hap : lm = .revocable → leaseIdsApart (ms.map (·.id)))
    (cmp : Bool) (cret : Nat) (Pub : ClusterNames → w64 → EnvView → IProp GF) :
    ⊢ regCtx -∗ ([∗list] m ∈ ms, addrUnset m.peer ∗ addrUnset m.client) ={⊤}=∗
      ∃ (c : ClusterNames) (γEs : List GName),
        ⌜ClusterOk c ps boot lm cmp cret (ms.map (·.id)) ∧ γEs.length = ms.length⌝ ∗
        ([∗list] p ∈ ms.zip γEs, memberStartShare S5 c ms ps ctxs (LogEntry.toEntries boot 0) p.1 p.2
          (Pub c p.1.id)) ∗
        clientStartShare c (ms.zip γEs) (Pub c) ∗
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
      (⟨γ, γk, issued, cnt, wn, fs, gen, idx, cok, rev, reg⟩ : ClusterNames)
      ((m0 :: ms').map (·.id)) ps ctxs (LogEntry.toEntries boot 0) m.id ∗ addrUnset m.client $$ [Hsl Hc]
  · iapply BigSepL.bigSepL_sep_eqv.2
    isplitl [Hsl]
    · iexact Hsl
    · iexact Hc
  imod (members_svc_start S5 (⟨γ, γk, issued, cnt, wn, fs, gen, idx, cok, rev, reg⟩ : ClusterNames)
      (m0 :: ms') ps ctxs (LogEntry.toEntries boot 0)
      (Pub ⟨γ, γk, issued, cnt, wn, fs, gen, idx, cok, rev, reg⟩) (m0 :: ms'))
    $$ Hreg Hf Hpf Hs with ⟨%γEs, %Hlen, Hms, #Hcs⟩
  imodintro
  iexists ⟨γ, γk, issued, cnt, wn, fs, gen, idx, cok, rev, reg⟩, γEs
  isplitr
  · ipureintro
    exact ⟨Hγ, Hlen⟩
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
