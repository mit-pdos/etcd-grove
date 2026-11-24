/- Lean-first (no Rocq counterpart).
# `raft/kvnet`: the top-level robustness theorem (2026-11-22)

`raft_kvnet_robust.spec` (`KvNet/Spec/.../kvnet/TopLevelRobustness.lean`), over the bridge
`Net.robust_of_netFsBoot_addrs` (`Net/Statement/NetFsBridge.lean`). (Until 2026-11-23 it took, as a
named hypothesis, the bridge on top of mit-pdos/perennial#683, which gave a generation the file
extension's local interpretation before its WP, for the switch to the shared view; since the file
extension's single shared view (`notes/fs-interp-state-determined.md`) a generation starts with that
view and needs no switch. It also took `errors.IsPathErrnoNotExist.spec`, proved since 2026-11-22,
`Proof/errors/IsPathErrnoNotExist.lean`.)

`raft_kvnet_robust` assembles it (`notes/kvnet-part.md`, the handoffs) at `GF := kvnetGF`:

* the start (`Hstart` of the bridge): the protocol registry (`netProto_alloc`), the store
  (`kvnet_store_alloc`: raft's cluster, the store's invariant, every replica's durable state and
  vacancy, the client's pieces), every address's protocols (`kvnet_addrs_alloc`), all global;
* a replica's generation (`kvPc`: the globals, the generation's `kvGen` at some root `J` of some roots
  `R`, the empty package state): its first (`kvPc_first`, from the file extension's start resources
  by `kvGen_first`) and every one's obligation (`kvPc_crashBoot`: the Go context substituted, a fresh
  storage registry by `kdStor_alloc`, then `kvRep_gen`);
* the client (`kvClient_stable`, from `kvcheck_wp_program`).

`raft_kvnet_robust_example` is the example's corollary, and `raft_kvnet_example_premises`
says the example's premises can all hold (with a file system as on disk, `FsInit`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopLevelRobustness
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ReplicaLinked
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopClient
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopStart
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopPure
public import Net.Statement.NetFsBridge

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Iris.Std Robustness NetFs Net go_etcd_io.raft.v3
open raft_kvreconf (bootVoters)

attribute [local instance] kvnetExts kvnetExtsSemantics kvnetExtsInterp kvnetExtsCrashInterp
  kvnetExts_hasNet kvnetExts_hasFs GooseGlobalGS.gooseInvGS

section gen
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]
variable [π : Net.NetProtoGS]

/-- **What every replica and the client share** (global, persistent): raft's cluster, its conf policy
and bootstrap configuration `vs`, the snapshots' registry, the store's invariant, `readyFits`, and
replica `i + 1`'s protocols at the `i`-th address of `rs`. -/
def kvGlobals (γ : KdNames) (vs : List w64) (rs : List GoString) : IProp GF :=
  iprop(isCluster γ.r.cluster kdRaftN ∗ confPolicy γ.r.cluster kdConfN raft_kvreconf.kvrRule ∗
    confAt γ.r.cluster 0 (Membership.simple (GMap.listToSet vs)) ∗ kdSnapInv γ ∗ rkvInv γ ∗
    readyFits γ.r.cluster kdRaftN ∗
    [∗list] i ↦ a ∈ rs, Net.addrProto a (kvP (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1)))
      (kvQG (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1))))

instance kdSnapInv_persistent' (γ : KdNames) : Persistent (kdSnapInv (GF := GF) γ) := by
  unfold kdSnapInv; infer_instance

instance rkvInv_persistent' (γ : KdNames) : Persistent (rkvInv (GF := GF) γ) := by
  unfold rkvInv; infer_instance

instance kvGlobals_persistent (γ : KdNames) (vs : List w64) (rs : List GoString) :
    Persistent (kvGlobals (GF := GF) γ vs rs) := by
  unfold kvGlobals; infer_instance

/-- **Replica `id`'s generation `L`, before its boot**: the globals, its `kvGen` at the root `J` of
`dir` among the roots `R`, and the generation's empty package state. -/
def kvPc (γ : KdNames) (vs : List w64) (rs : List GoString) (dir : GoString) (id : w64)
    (L : GooseLocalGS GF) : IProp GF :=
  letI : HeapGS .hasLC GF := ⟨G, L⟩
  iprop(kvGlobals γ vs rs ∗
    (∃ (J : Fs.Ino) (R : Fs.Roots), ⌜(dir, J) ∈ R ∧ Fs.RootsOk R⌝ ∗
      kvGen γ id (kvDFile dir J id) R) ∗
    ownGoState ∅)

/-- **The checking client's share**: the store's invariant, the client's half of its state (empty),
the counters at `0` and the replicas' protocols. -/
def kvClient (γ : KdNames) (rs : List GoString) : IProp GF :=
  iprop(rkvInv γ ∗ rkvVal γ raft_kvreconf.kvEmpty ∗ ghostVar γ.r.opn (1 : Qp).half (W64 0) ∗
    ([∗list] id ∈ bootVoters rs.length, id ↪[γ.r.rseq] W64 0) ∗
    [∗list] i ↦ a ∈ rs, Net.addrProto a (kvP (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1)))
      (kvQG (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1))))

variable [lctx : GoLocalContext] [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [os_file_sem : os.file.FieldAssumptions] [os_stat_sem : os.fileStat.FieldAssumptions]
variable [log_sem : log.NewModel] [NaInvG GF]

/-- **Every generation of replica `i + 1`** (`CrashBootWp`): the Go context substituted, a fresh
storage registry, then `kvRep_gen`; after a crash, the next generation's `kvPc`. -/
theorem kvPc_crashBoot
    (γ : KdNames) (cl : ClusterConfig) (rs : List GoString) (dir : GoString) (i : Nat)
    (hi : i < rs.length) (hnd : rs.Nodup) (hok : ∀ a ∈ rs, addrOk a = true)
    (hlen : rs.length < 2 ^ 32) (hcl : cl.Ok rs.length) (hdir : dir.length < 2 ^ 39)
    (hγ : γ.max = rs.length ∧ γ.r.cluster.dup = true ∧ γ.r.cluster.bootLen = 0 ∧
      Cluster.trace γ.r.cluster = none ∧ γ.r.cluster.snapLoc = (fun _ => none) ∧
      γ.r.cluster.maxData = none) :
    CrashBootWp (GF := GF) (kvnetReplicaProgram cl (List.intercalate go!"," rs) dir (W64 ((i : Int) + 1)))
      (kvPc γ (bootVoters (uint.nat cl.voters)) rs dir (W64 ((i : Int) + 1))) := by
  intro L hL
  subst hL
  try dsimp only
  letI hG : HeapGS .hasLC GF := ⟨G, L⟩
  have hsplit := splitAddrs_intercalate rs (List.ne_nil_of_length_pos (by omega)) hok
  obtain ⟨hid1, hid2, hid32, hget⟩ := replica_id rs i hi hlen
  unfold kvPc
  try dsimp only
  iintro ⟨#Hgl, ⟨%J, %R, ⟨%hJ, %hR⟩, Hg⟩, Hgs⟩ -
  imod kdStor_alloc (GF := GF) ⊤ with ⟨%k, #Hsi⟩
  letI : KdStor GF := k
  have Hrep := kvRep_gen (GF := GF) γ (bootVoters (uint.nat cl.voters)) cl
    (List.intercalate go!"," rs) dir (W64 ((i : Int) + 1)) (kvDFile dir J (W64 ((i : Int) + 1))) R
    (by rw [hsplit]; exact validCluster_of rs cl hnd hok hlen hcl) hid1 (by rw [hsplit]; exact hid2)
    hR hJ rfl (kvDFile_ok dir J _ (hR.2.2 _ hJ).1 hdir hid32) (kvDFile_name dir J _)
    (by rw [hγ.1]; exact hid2)
    ⟨hγ.2.1, hγ.2.2.1, hγ.2.2.2.1, hγ.2.2.2.2.1, hγ.2.2.2.2.2, by rw [hγ.1]; exact hlen⟩
    (kvOptsOk_of_clOk cl rs.length hcl hlen) rfl
  rw [hsplit] at Hrep
  unfold kvGlobals
  icases Hgl with ⟨#Hc, #Hp, #Ha, #Hsn, #Hinv, #Hrf, #Haddrs⟩
  ihave #Hkc := kvnet_kdCluster γ (bootVoters (uint.nat cl.voters)) $$ Hc Hp Ha Hsn Hinv
    %(hγ.2.2.2.1)
  imod Hrep $$ Hsi Hkc Hrf [] [] Hg Hgs with ⟨Hwp, Hcr⟩
  · imodintro
    iintro %a %ha
    rw [hget] at ha
    cases ha
    ihave H := BigSepL.bigSepL_lookup (Φ := fun i a => Net.addrProto a
      (kvP (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1)))
      (kvQG (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1))))
      (List.getElem?_eq_getElem hi) $$ Haddrs
    rw [kvFacts_eq, kvQ_eq]
    iexact H
  · imodintro
    iintro %M %hM
    iapply kvnet_peerAddrs γ rs _ M hM hok
    iexact Haddrs
  imodintro
  iframe Hwp
  iintro %L' %V' Hcd Hos' Hrest Hgs' Hlc
  imod Hcr $$ %L' %V' Hlc Hcd Hos' Hrest with Hg'
  imodintro
  iframe Hgs' Hc Hp Ha Hsn Hinv Hrf Haddrs
  iexists J, R
  iframe Hg'
  ipureintro; exact ⟨hJ, hR⟩

/-- **Replica `id`'s first generation**: from the file extension's start resources of a file system
as on disk (`FsInit`) in which `dir` is an empty root, and the id's durable state at
`RaftState.init` with its vacancy, `kvPc` (`kvGen_first`). -/
theorem kvPc_first (γ : KdNames) (vs : List w64) (rs : List GoString) (dir : GoString) (id : w64)
    (st : Fs.OsState) (hst : Fs.FsInit st) (hroot : dir ∈ st.fs.roots.map (·.1))
    (hempty : ∀ c, st.lookup (joinPath dir [c]) = none) (hdir : dir.length < 2 ^ 39)
    (hid : uint.nat id < 2 ^ 32) (L : GooseLocalGS GF) (hL : L.goose_go_local_context = lctx) :
    kvGlobals γ vs rs ∗
      (letI : HeapGS .hasLC GF := ⟨G, L⟩
       iprop(raftState γ.r.cluster id RaftState.init ∗ nodeVacant γ.r.cluster id)) ⊢
      fsStartRes L st -∗ ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗ kvPc γ vs rs dir id L := by
  subst hL
  letI hG : HeapGS .hasLC GF := ⟨G, L⟩
  obtain ⟨⟨d', J⟩, hp, hpd⟩ := List.mem_map.1 hroot
  simp only at hpd
  subst hpd
  have hf := kvDFile_ok d' J id (rootForm_of_fsInit hst hp) hdir hid
  letI : KdStor GF := ⟨0⟩
  iintro ⟨#Hgl, HrS, Hvac⟩ Hfs Hgs
  unfold fsStartRes
  icases Hfs with ⟨#Hos, -, Ht⟩
  imod kvGen_first γ id (kvDFile d' J id) st ⊤ hst
    (fsInit_entry_none hst hp hempty _ hf.2.2.2.1)
    (fsInit_entry_none hst hp hempty _ hf.2.2.2.2.1) $$ Hos Ht HrS Hvac with Hg
  imodintro
  unfold kvPc
  try dsimp only
  iframe Hgl Hgs
  iexists J, st.fs.roots
  iframe Hg
  ipureintro; exact ⟨hp, hst.2.2.2.1⟩

/-- **The checking client** (`StableBootWp`): the Go context substituted, then
`kvcheck_wp_program`. -/
theorem kvClient_stable (γ : KdNames) (cl : ClusterConfig) (rs : List GoString) (σc : state)
    (hnd : rs.Nodup) (hok : ∀ a ∈ rs, addrOk a = true) (hlen : rs.length < 2 ^ 32)
    (hcl : cl.Ok rs.length) (hrb : receiptBound GF ≤ 2 ^ 63) :
    StableBootWp (GF := GF) (kvcheckProgram cl (List.intercalate go!"," rs)) σc (kvClient γ rs) := by
  intro L hL
  subst hL
  try dsimp only
  letI hG : HeapGS .hasLC GF := ⟨G, L⟩
  have hsplit := splitAddrs_intercalate rs (by
    rintro rfl; exact absurd hcl.2.1 (by have := hcl.1; simp; omega)) hok
  letI : KdStor GF := ⟨0⟩
  have H := kvcheck_wp_program (GF := GF) γ cl (List.intercalate go!"," rs)
    (by rw [hsplit]; exact validAddrs_of rs cl hnd hok hlen hcl) hrb
  rw [hsplit] at H
  unfold kvClient
  iintro ⟨#Hinv, Hval, Hopn, Hrseq, #Haddrs⟩ - Hgs -
  imodintro
  iapply H $$ Hinv Hval [Hopn] [Hrseq] [] Hgs
  · iapply kvnet_kvCnt_op; iexact Hopn
  · iapply kvnet_kvCnt_read; iexact Hrseq
  · iapply kvnet_addrsProto γ _ rs hok; iexact Haddrs

end gen

/-- A big separating conjunction whose terms depend only on the index, moved to another list of the
same length. -/
theorem bigSepL_reindex {GF : BundledGFunctors} {A B : Type} :
    ∀ (Φ : Nat → IProp GF) (l1 : List A) (l2 : List B), l1.length = l2.length →
      ([∗list] k ↦ _x ∈ l1, Φ k) ⊢ [∗list] k ↦ _y ∈ l2, Φ k
  | _, [], [], _ => .rfl
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h
  | Φ, _ :: l1, _ :: l2, h => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H0, H⟩
    iapply BigSepL.bigSepL_cons.2
    iframe H0
    iapply bigSepL_reindex (fun k => Φ (k + 1)) l1 l2 (by simpa using h) $$ H

/-- `bootVoters n`'s big separating conjunction, indexed: the `k`-th is `k + 1`. -/
theorem bootVoters_bigSepL {GF : BundledGFunctors} {B : Type} (Φ : w64 → IProp GF) (n : Nat)
    (l : List B) (hl : l.length = n) :
    ([∗list] id ∈ bootVoters n, Φ id) ⊢ [∗list] k ↦ _x ∈ l, Φ (W64 ((k : Int) + 1)) := by
  unfold bootVoters
  rw [BigSepL.bigSepL_map]
  refine (BigSepL.bigSepL_mono (Ψ := fun k _ => Φ (W64 ((k : Int) + 1))) ?_).trans
    (bigSepL_reindex (fun k => Φ (W64 ((k : Int) + 1))) (List.range n) l (by simp [hl]))
  intro k x hk
  rw [List.getElem?_range (by simpa using (List.getElem?_eq_some_iff.1 hk).1)] at hk
  cases hk; exact .rfl

/-- Crashing machine `i`'s program and state, from the replicas'. -/
theorem replica_mem {α β γ : Type} (f : Nat → α × β → γ × β) (replicas : List (α × β)) (i : Nat)
    (m : γ × β) (hm : (replicas.mapIdx f)[i]? = some m) :
    ∃ p, replicas[i]? = some p ∧ m = f i p ∧ m ∈ replicas.mapIdx f := by
  have hmem := List.mem_of_getElem? hm
  rw [List.getElem?_mapIdx] at hm
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hm
  exact ⟨p, hp, rfl, hmem⟩

section top
variable [go_gctx : GoGlobalContext]

/-- **kvnet is robust** (`raft_kvnet_robust.spec`; see the file header). -/
theorem raft_kvnet_robust :
    raft_kvnet_robust.spec := by
  intro lctx sem package_sem field_sem os_file_sem os_stat_sem log_sem cl dir replicas σc g
    hcl hn hdir hnd hrep addrs hfresh hig hil
  have hlenrs : (replicas.map (·.1)).length = replicas.length := List.length_map _
  have hok : ∀ a ∈ replicas.map (·.1), addrOk a = true := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
    exact (hrep p.1 p.2 hp).1
  rw [← hlenrs] at hcl hn
  refine Net.robust_of_netFsBoot_addrs (GF := kvnetGF) (replicas.map (·.1)) _ _ g _ _ hnd hok ?_
    hfresh hig hil
  intro G hrb
  iintro Hs
  imod Net.netProto_alloc (GF := kvnetGF) ⊤ with ⟨%π, #Hreg⟩
  letI : Net.NetProtoGS := π
  have hv := hcl
  obtain ⟨hv1, hvn, -⟩ := hv
  imod kvnet_store_alloc (GF := kvnetGF) ⊤ (replicas.map (·.1)).length (uint.nat cl.voters) hv1 hvn
    hn (by omega)
    with ⟨%γ, %hγ, #Hc, #Hp, #Ha, #Hsn, #Hinv, #Hrf, Hnodes, Hval, Hopn, Hrseq⟩
  imod kvnet_addrs_alloc (GF := kvnetGF) (F := kvFactsG γ (fun _ => True)) ⊤ (replicas.map (·.1))
    $$ Hreg Hs with #Haddrs
  ihave #Hgl : kvGlobals γ (bootVoters (uint.nat cl.voters)) (replicas.map (·.1)) $$ []
  · unfold kvGlobals
    iframe Hc Hp Ha Hsn Hinv Hrf Haddrs
  imodintro
  iexists (fun i L => kvPc γ (bootVoters (uint.nat cl.voters)) (replicas.map (·.1)) dir
    (W64 ((i : Int) + 1)) L)
  iexists (fun _ => kvClient γ (replicas.map (·.1)))
  isplitr
  · ipureintro
    intro i m hm
    obtain ⟨p, hp, rfl, -⟩ := replica_mem _ replicas i m hm
    have hi : i < replicas.length := (List.getElem?_eq_some_iff.1 hp).1
    exact kvPc_crashBoot γ cl _ dir i (by omega) hnd hok hn hcl hdir hγ
  isplitr
  · ipureintro
    intro j m hm
    match j, hm with
    | 0, hm =>
      cases hm
      exact kvClient_stable γ cl _ σc hnd hok hn hcl (by omega)
  isplitl [Hnodes]
  · ihave Hn := bootVoters_bigSepL (fun id => iprop(raftState γ.r.cluster id RaftState.init ∗
      nodeVacant γ.r.cluster id)) _
      (replicas.mapIdx fun i p => (kvnetReplicaProgram cl addrs dir (W64 ((i : Int) + 1)), p.2))
      (by simp) $$ Hnodes
    iapply BigSepL.bigSepL_impl $$ Hn
    imodintro
    iintro %k %m %hk H %L %hL Hfs Hgs
    obtain ⟨p, hp, rfl, hmem⟩ := replica_mem _ replicas k m hk
    have hk' : k < (replicas.map (·.1)).length := by
      rw [hlenrs]; exact (List.getElem?_eq_some_iff.1 hp).1
    obtain ⟨-, hroot, hempty⟩ := hrep p.1 p.2 (List.mem_of_getElem? hp)
    have hfs : Fs.FsInit (fsOf p.2) := (hil _ (List.mem_append_left _ hmem)).2.1
    iapply kvPc_first γ _ _ dir _ (fsOf p.2) hfs hroot hempty hdir
      (replica_id _ k hk' hn).2.2.1 L hL $$ [H] Hfs Hgs
    iframe Hgl H
  · iapply BigSepL.bigSepL_cons.2
    dsimp only
    isplitl [Hval Hopn Hrseq]
    · unfold kvClient
      iframe Hinv Hval Hopn Haddrs Hrseq
    · iapply BigSepL.bigSepL_nil.2
      iempintro

#print axioms raft_kvnet_robust

/-- **The example from the theorem**: `raft_kvnet_robust_example.spec` from `raft_kvnet_robust.spec`,
its premises by computation. -/
theorem raft_kvnet_robust_example_of (H : raft_kvnet_robust.spec) :
    raft_kvnet_robust_example.spec := by
  intro lctx sem package_sem field_sem os_file_sem os_stat_sem log_sem σ₁ σ₂ σ₃ σ₄ σ₅ σc g hfs
  have h := @H lctx sem package_sem field_sem os_file_sem os_stat_sem log_sem exampleConfig
    go!"/var/lib/kvnet"
    [(go!"10.0.0.1:7001", σ₁), (go!"10.0.0.2:7001", σ₂), (go!"10.0.0.3:7001", σ₃),
     (go!"10.0.0.4:7001", σ₄), (go!"10.0.0.5:7001", σ₅)] σc g
    (by show exampleConfig.Ok 5; unfold ClusterConfig.Ok exampleConfig; decide) (by show 5 < 2 ^ 32; decide)
    (by decide)
    (by show [go!"10.0.0.1:7001", go!"10.0.0.2:7001", go!"10.0.0.3:7001", go!"10.0.0.4:7001",
      go!"10.0.0.5:7001"].Nodup; decide) ?_
  · exact h
  · intro a σ hm
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by decide, hfs _ (by simp)⟩
    · exact ⟨by decide, hfs _ (by simp)⟩
    · exact ⟨by decide, hfs _ (by simp)⟩
    · exact ⟨by decide, hfs _ (by simp)⟩
    · exact ⟨by decide, hfs _ (by simp)⟩

/-- **kvnet is robust, the example**. -/
theorem raft_kvnet_robust_example :
    raft_kvnet_robust_example.spec :=
  raft_kvnet_robust_example_of raft_kvnet_robust

#print axioms raft_kvnet_robust_example

end top

/-! ## The example's premises can hold -/

/-- A file system as on disk with one root, `/var/lib/kvnet` (inode `0`), empty. -/
def exampleFs : Fs.OsState :=
  { fs := { roots := [(go!"/var/lib/kvnet", 0)], treeDur := <[0 := (∅ : Fs.Dir)]> (∅ : Fs.Tree),
            metaLog := [], committed := fun _ => False, files := ∅, nextIno := 1, stamp := 0 }
    proc := Fs.ProcState.empty }

theorem exampleFs_entry (j : Fs.Ino) (b : GoString) : exampleFs.fs.treeDur.entry j b = none := by
  simp only [exampleFs, Fs.Tree.entry, GMap.lookup_insert_eq_iff]
  split <;> simp

theorem exampleFs_mem (j : Fs.Ino) (h : j ∈ exampleFs.fs.treeDur) : j = 0 := by
  rw [GMap.mem_iff] at h
  by_cases hj0 : j = 0
  · exact hj0
  · rw [show exampleFs.fs.treeDur = <[0 := (∅ : Fs.Dir)]> (∅ : Fs.Tree) from rfl,
      GMap.lookup_insert_ne _ _ (Ne.symm hj0)] at h
    simp at h

theorem exampleFs_rootForm : Fs.RootForm go!"/var/lib/kvnet" :=
  ⟨[go!"var", go!"lib", go!"kvnet"], by simp, by decide, by decide⟩

theorem exampleFs_init : Fs.FsInit exampleFs := by
  refine ⟨rfl, rfl, fun _ h => h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp [exampleFs], by simp [exampleFs], fun r hr => ?_⟩
    simp only [exampleFs, List.mem_singleton] at hr
    subst hr
    refine ⟨exampleFs_rootForm, fun r' hr' hne => ?_⟩
    simp only [exampleFs, List.mem_singleton] at hr'
    subst hr'
    exact absurd rfl hne
  · refine ⟨fun j hj => ?_, fun j hj => ?_, fun j b n h => ?_, fun j b j' h => ?_,
      fun j1 b1 j2 b2 n h => ?_⟩
    · induction hj with
      | root r j hr =>
        simp only [exampleFs, List.mem_singleton, Prod.mk.injEq] at hr
        obtain ⟨-, rfl⟩ := hr
        rw [GMap.mem_iff]; simp [exampleFs]
      | child j b j' _ he => rw [exampleFs_entry] at he; cases he
    · left
      rw [exampleFs_mem j hj]
      exact Fs.Reach.root go!"/var/lib/kvnet" 0 (by simp [exampleFs])
    · rw [exampleFs_entry] at h; cases h
    · rw [exampleFs_entry] at h; cases h
    · rw [exampleFs_entry] at h; cases h
  · rintro i ⟨j, b, h⟩
    rw [exampleFs_entry] at h; cases h
  · intro i f h; simp [exampleFs] at h
  · intro i h; rw [GMap.mem_iff] at h; simp [exampleFs] at h
  · intro j h; rw [exampleFs_mem j h]; simp [exampleFs]

theorem exampleFs_lookup (c : GoString) :
    exampleFs.lookup (joinPath go!"/var/lib/kvnet" [c]) = none := by
  unfold Fs.OsState.lookup
  split
  · rename_i h
    obtain ⟨hrj, -, heq⟩ := h.choose_spec.choose_spec
    have hrj' : h.choose = (go!"/var/lib/kvnet", 0) := by simpa [exampleFs] using hrj
    generalize h.choose_spec.choose = cs at heq ⊢
    rw [hrj'] at heq ⊢
    cases cs with
    | nil => simp [joinPath] at heq
    | cons c0 cs =>
      have ht : exampleFs.tree = exampleFs.fs.treeDur := rfl
      simp only [Fs.walk, ht, exampleFs_entry]
  · rfl

/-- **The example's premises can all hold**: the options are valid for five replicas, the addresses
canonical and distinct, the directory short, and a file system as on disk (`FsInit`, what `Robust`
requires of every machine) has `/var/lib/kvnet` an empty root (what the example requires). -/
theorem raft_kvnet_example_premises :
    exampleConfig.Ok 5 ∧ (go!"/var/lib/kvnet" : GoString).length < 2 ^ 39 ∧
    [go!"10.0.0.1:7001", go!"10.0.0.2:7001", go!"10.0.0.3:7001", go!"10.0.0.4:7001",
      go!"10.0.0.5:7001"].Nodup ∧
    (∀ a ∈ [go!"10.0.0.1:7001", go!"10.0.0.2:7001", go!"10.0.0.3:7001", go!"10.0.0.4:7001",
      go!"10.0.0.5:7001"], Net.addrOk a = true) ∧
    ∃ st : Fs.OsState, Fs.FsInit st ∧ go!"/var/lib/kvnet" ∈ st.fs.roots.map (·.1) ∧
      ∀ c, st.lookup (joinPath go!"/var/lib/kvnet" [c]) = none :=
  ⟨by unfold ClusterConfig.Ok exampleConfig; decide, by decide, by decide, by decide,
    exampleFs, exampleFs_init, by simp [exampleFs], exampleFs_lookup⟩

#print axioms raft_kvnet_example_premises

end raft_kvnet
end EtcdGrove
end Perennial
