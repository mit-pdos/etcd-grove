/-
# `raft/kvnet/cmd/kvudp`: the top-level robustness theorem's proof (2026-11-24)

`notes/kvudp-proof-plan.md`, "The top level". As kvnet's proof (`KvNet/Proof/.../kvnet/TopLevelRobustness.lean`)
with the UDP side added:

* **the bridge** (`robust_of_netFsUdpBoot`): `Net.robust_of_netFsBoot`'s, over `[netExt, fsExt,
  udpExt]` (`NetFsUdp.kvudpExts`): the start obligation is also given the UDP extension's start
  resources (`udpSent a []` at every valid address); a generation's resources are the same;
* **the start**: kvnet's global allocation (the store's names, the addresses' TCP protocols, raft's
  cluster), and kvudp's (`kvudp_udp_alloc`): the names' invariant `udpMsgInv γu` with `udpHi γu id 0`
  for every replica `id`, and one `udpAddrInv` per replica address, from its `udpSent a []`. These are
  stated at the global ghost state (`udpMsgInvG`, `udpAddrInvG`: `UdpDefs.lean`'s, which name a heap
  ghost state only through its global part, as kvnet's `kvFactsG`);
* **a replica's generation** (`kvudpGen`): kvnet's `kvGenAt` at the generation's first tree and the
  boot file's (`udpGenAt`: the claim on its two names, half the root's call permission, what the
  generation found there and replica `id`'s `udpHi` bounded by it). The first (`kvudpGen_first`) from
  kvnet's `kvGen_first` and its `kvDirRest`; the boot (`kvudpRep_gen`): kvnet's `kvGen_boot` and the
  boot file's `udp_gen_boot`, then `RunNodeUDP`'s WP (`kvudpReplica_wp`); a crash: kvnet's `kvGen_crash`
  (with the crash's rest after the storage file's), then the boot file's `udp_boot_crash` (whose premise
  on the files already taken holds by unique naming: they are named at the storage file's names,
  `kvBoot_names_fresh`);
* **the client**: kvnet's (`kvudpClient_stable`, as `kvClient_stable`).

The three `net` UDP functions (`ListenUDP`, `(*UDPConn).WriteToUDP`, `(*UDPConn).ReadFromUDP`) are
linked by the part's Link from their proofs (`Net/Proof/net/`, copied into the part).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.cmd.kvudp.TopLevelRobustness
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.cmd.kvudp.Link
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopLevelRobustness
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.UdpBootDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvudp

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Iris.Std Robustness NetFsUdp Net Udp
open go_etcd_io.raft.v3 raft_kvnet
open raft_kvreconf (bootVoters)

attribute [local instance] kvudpExts kvudpExtsSemantics kvudpExtsInterp kvudpExtsCrashInterp
  kvudpExts_hasNet kvudpExts_hasFs kvudpExts_hasUdp GooseGlobalGS.gooseInvGS kdStorageModel

/-! ## The bridge, over `[netExt, fsExt, udpExt]` (as `Net.robust_of_netFsBoot`) -/

section bridge
variable [GoGlobalContext] {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- `Net.fsStartRes`, over kvudp's extensions. -/
def fsStartResU [G : GooseGlobalGS .hasLC GF] (L : GooseLocalGS GF) (st : Fs.OsState) : IProp GF :=
  iprop(Fs.osInv (L := L) ∗
    ([∗map] i ↦ f ∈ st.fs.files, Fs.osFileStart (L := L) i f) ∗
    Fs.osShared (L := L) st.fs.roots (st.fs.treeDur, []))

theorem fsStartResU_of_localStart [G : GooseGlobalGS .hasLC GF] (L : GooseLocalGS GF)
    (w : ExtsLocalState exts) (h : Fs.FsInit (extLocal Fs.fsExt w)) :
    ⊢ extsLocalStart (GF := GF) (L := L) w ={⊤}=∗ fsStartResU L (extLocal Fs.fsExt w) := by
  have hdisk : ∀ i f, (extLocal Fs.fsExt w).fs.files !! i = some f →
      ∃ img sz, f = Fs.OsFile.ofDisk img sz := fun i f hf =>
    let ⟨img, sz, _, e⟩ := (h.2.2.2.2.2.2.1 i f hf).2; ⟨img, sz, e⟩
  iintro Hs
  icases kvudp_fs_localStart (L := L) w $$ Hs with Hs
  unfold Fs.osStart Fs.osStartF Fs.treeStart Fs.bytesMap Fs.metaMap
  icases Hs with ⟨⟨Hb, Hm, Hv⟩, Hd⟩
  ihave Hfs := Fs.start_files (Fs.gooseOsGS (L := L)) hdisk $$ [Hb Hm]
  · iframe
  imod Fs.osInv_alloc (L := L) ⊤ $$ Hv with #Hinv
  imod Fs.osSwitchKit_open (L := L) _ _ ⊤ $$ Hd with Hsh
  imodintro
  unfold fsStartResU
  iframe Hinv Hsh
  iapply BigSepM.bigSepM_mono (fun {i f} _ =>
    (Fs.fileStart_eq (L := L) i f).1) $$ Hfs

/-- `Net.StableBootWp`, over kvudp's extensions. -/
def StableBootWpU [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (e : Expr) (σ : state)
    (P : IProp GF) : Prop :=
  ∀ L : GooseLocalGS GF, L.goose_go_local_context = lctx →
    letI : HeapGS .hasLC GF := ⟨G, L⟩
    P ⊢ fsStartResU L (extLocal Fs.fsExt σ.world) -∗ ownGoState (hG := L.goose_go_stateGS) ∅ -∗
      threadTok ={⊤}=∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

/-- `Net.CrashBootWp`, over kvudp's extensions. -/
def CrashBootWpU [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (e : Expr)
    (P : GooseLocalGS GF → IProp GF) : Prop :=
  ∀ L : GooseLocalGS GF, L.goose_go_local_context = lctx →
    letI : HeapGS .hasLC GF := ⟨G, L⟩
    P L ⊢ threadTok ={⊤}=∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} ∗
      ∀ (L' : GooseLocalGS GF) (V' : Fs.Hist), crashed (hC := L.goose_crashGS) -∗
        Fs.osInv (L := L') -∗
        Fs.crashRest (fun _ _ => True) (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) [] false
          V' -∗
        ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ £ 1 ={⊤}=∗ P L'

/-- `Net.crashPre`, over kvudp's extensions. -/
def crashPreU [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF]
    (crashing : List (Expr × state)) (i : Nat) (L : GooseLocalGS GF) : IProp GF :=
  iprop(∃ Q : GooseLocalGS GF → IProp GF,
    ⌜∀ m : Expr × state, crashing[i]? = some m → CrashBootWpU m.1 Q⌝ ∗ Q L)

theorem nodeWp_of_stableBootU [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (e : Expr) (σ : state) (P : IProp GF) (hf : Fresh lctx σ)
    (hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)) (H : StableBootWpU e σ P) :
    P ⊢ nodeWp T e σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  unfold nodeWpBody
  rw [hf.2.1]
  iintro %_ %hL Hls Hgs Htok
  imod fsStartResU_of_localStart L σ.world hfs $$ Hls with Hr
  iapply H L (hL.trans hf.1) $$ HP Hr Hgs Htok

theorem nodeStart_of_crashBootU [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (crashing : List (Expr × state)) (i : Nat) (m : Expr × state) (hm : crashing[i]? = some m)
    (hf : Fresh lctx m.2) (hfs : Fs.FsInit (extLocal Fs.fsExt m.2.world))
    (Q : GooseLocalGS GF → IProp GF) (HQ : CrashBootWpU m.1 Q) :
    (∀ L : GooseLocalGS GF, ⌜L.goose_go_local_context = lctx⌝ -∗
        fsStartResU L (extLocal Fs.fsExt m.2.world) -∗ ownGoState (hG := L.goose_go_stateGS) ∅
        ={⊤}=∗ Q L) ⊢
      nodeStart T m.2 (crashPreU crashing i) := by
  unfold nodeStart
  rw [hf.2.1]
  iintro H %L %_ %hL Hls Hgs
  imod fsStartResU_of_localStart L m.2.world hfs $$ Hls with Hr
  imod H $$ %L %(hL.trans hf.1) Hr Hgs with HQL
  imodintro
  unfold crashPreU
  iexists Q
  iframe HQL
  ipureintro
  intro m' hm'
  rw [hm] at hm'
  cases hm'
  exact HQ

/-- **The bridge** (`Net.robust_of_netFsBoot_addrs`, over `[netExt, fsExt, udpExt]`): the start
obligation is also given the UDP extension's start resources. -/
theorem robust_of_netFsUdpBoot [lctx : GoLocalContext] (addrs : List GoString)
    (crashing stable : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (Hnd : addrs.Nodup) (Hok : ∀ a ∈ addrs, addrOk a = true)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) -∗
        Udp.udpStart (extGlobalGS Udp.udpExt) (extGlobal Udp.udpExt g.globalWorld) ={⊤}=∗
        ∃ (Pc : Nat → GooseLocalGS GF → IProp GF) (Ps : Nat → IProp GF),
          ⌜∀ (i : Nat) (m : Expr × state), crashing[i]? = some m → CrashBootWpU m.1 (Pc i)⌝ ∗
          ⌜∀ (j : Nat) (m : Expr × state), stable[j]? = some m → StableBootWpU m.1 m.2 (Ps j)⌝ ∗
          ([∗list] i ↦ m ∈ crashing, ∀ L : GooseLocalGS GF,
            ⌜L.goose_go_local_context = lctx⌝ -∗ fsStartResU L (extLocal Fs.fsExt m.2.world) -∗
            ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗ Pc i L) ∗
          [∗list] j ↦ _m ∈ stable, Ps j) :
    Robust crashing stable g threads bound := by
  intro hfresh hig hil n κs c hsteps hn i tp σ hi e he
  have hfc : ∀ (k : Nat) (m : Expr × state), crashing[k]? = some m → m ∈ crashing ++ stable :=
    fun _ m hm => List.mem_append_left _ (List.mem_of_getElem? hm)
  have hfst : ∀ (k : Nat) (m : Expr × state), stable[k]? = some m → m ∈ crashing ++ stable :=
    fun _ m hm => List.mem_append_right _ (List.mem_of_getElem? hm)
  have H := goose_dist_mixed_crash_adequacy (GF := GF) (n + 1) (n + 2) crashing stable g
    (fun _ v => v = #()) (fun _ p h => intoVal_ne_PanicV () p h.symm)
    ⟨hig.1, trivial, hig.2.2.1, trivial⟩
    (fun m hm => ⟨trivial, (hil m hm).2.1, trivial, trivial⟩) (fun i L => crashPreU crashing i L) ?_ ?_
    n κs c hsteps.nsteps (Nat.lt_succ_self n) (fun m hm => (hfresh m hm).2.2)
    (DistCrashThreadsBelow.of_single (distInit_threads hfresh)) i tp σ hi
  · exact ⟨H.2.1 e he, H.2.2 e he⟩
  · intro G HN
    iintro Hg
    icases kvudp_netUdp_globalStart g.globalWorld $$ Hg with ⟨Hnet, Hudp⟩
    ihave Hs := addrs_start (Gg := G) (extGlobal netExt g.globalWorld) addrs Hnd Hok $$ Hnet
    imod Hstart (by omega) $$ Hs Hudp with ⟨%Pc, %Ps, %HPc, %HPs, Hc, Hst⟩
    imodintro
    isplitl [Hc]
    · iapply BigSepL.bigSepL_mono ?_ $$ Hc
      intro k m hm
      exact nodeStart_of_crashBootU (n + 2) crashing k m hm (hfresh m (hfc k m hm))
        ((hil m (hfc k m hm)).2.1) (Pc k) (HPc k m hm)
    · iapply BigSepL.bigSepL_mono ?_ $$ Hst
      intro k m hm
      exact nodeWp_of_stableBootU (n + 2) m.1 m.2 (Ps k) (hfresh m (hfst k m hm))
        ((hil m (hfst k m hm)).2.1) (HPs k m hm)
  · intro hG _ _ k e' σ' Hes Hlctx
    obtain ⟨G, L⟩ := hG
    have hL : L.goose_go_local_context = lctx :=
      Hlctx.trans (hfresh (e', σ') (hfc k _ Hes)).1
    unfold crashPreU
    iintro ⟨%Q, %HQ, HQL⟩ Htok
    imod HQ (e', σ') Hes L hL $$ HQL Htok with ⟨Hwp, Hcr⟩
    imodintro
    iframe Hwp
    iintro %L' Hcrd Hcs Hgs Hlc
    icases kvudp_fs_crashStart L L' $$ Hcs with Hcs
    unfold Fs.osCrashStart
    icases Hcs with ⟨Hv, %V', Hr⟩
    imod Fs.osInv_alloc (L := L') ⊤ $$ Hv with #Hinv
    imod Hcr $$ %L' %V' Hcrd Hinv Hr Hgs Hlc with HQL'
    imodintro
    iexists Q
    iframe HQL'
    ipureintro
    exact HQ

end bridge

/-! ## kvudp's ghost state, at the global ghost state -/

section udpG
variable [GoGlobalContext] {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-- `udpMsgAt`, at the global ghost state. -/
def udpMsgAtG (γu : UdpNames) (k : MsgKey) (body : List w8) : IProp GF :=
  ghostMapElem γu.msgs k DFrac.discard body

/-- `udpBodyOk`, at the global ghost state. -/
def udpBodyOkG (F : KvFacts GF) (body : List w8) : IProp GF :=
  iprop(∃ (src : w64) (st : MsgSt), ⌜body = encMsg st ∧ body.length < 2 ^ 63⌝ ∗ F.msgOk src st)

/-- `udpFragOk`, at the global ghost state. -/
def udpFragOkG (F : KvFacts GF) (γu : UdpNames) (dg : DgM) : IProp GF :=
  iprop(∃ body, udpMsgAtG γu dg.key body ∗ udpBodyOkG F body ∗ ⌜FragOf body dg⌝)

/-- `udpDgMOk`, at the global ghost state. -/
def udpDgMOkG (F : KvFacts GF) (γu : UdpNames) (dg : DgM) : IProp GF :=
  iprop(⌜dg.kind = kindAckB⌝ ∨ (⌜dg.kind = kindFragmentB⌝ ∗ udpFragOkG F γu dg))

/-- `udpDgOk`, at the global ghost state. -/
def udpDgOkG (F : KvFacts GF) (γu : UdpNames) (d : List w8) : IProp GF :=
  iprop(∃ dg, ⌜parseDg d = some dg⌝ ∗ udpDgMOkG F γu dg)

/-- `udpAddrInv`, at the global ghost state. -/
def udpAddrInvG (F : KvFacts GF) (γu : UdpNames) (a : GoString) : IProp GF :=
  inv udpSentN iprop(∃ ms, udpSent (extGlobalGS udpExt (G := G)) a ms ∗
    [∗list] d ∈ ms, udpDgOkG F γu d)

instance udpAddrInvG_persistent F γu a : Persistent (udpAddrInvG (GF := GF) F γu a) := by
  unfold udpAddrInvG; infer_instance

/-- `udpMsgInv`, at the global ghost state. -/
def udpMsgInvG (γu : UdpNames) : IProp GF :=
  inv udpMsgN iprop(∃ (M : GMap MsgKey (List w8)) (T : GMap MsgKey Bool) (C : GMap (w64 × w64) w64)
      (H : GMap w64 w64),
    ghostMapAuth γu.msgs 1 M ∗ ghostMapAuth γu.toks 1 T ∗ ghostMapAuth γu.ctrs 1 C ∗
    ghostMapAuth γu.his 1 H ∗ ⌜UdpMsgOk M T C H⌝)

instance udpMsgInvG_persistent γu : Persistent (udpMsgInvG (GF := GF) γu) := by
  unfold udpMsgInvG; infer_instance

/-- `udpHi`, at the global ghost state. -/
def udpHiG (γu : UdpNames) (f hi : w64) : IProp GF :=
  ghostMapElem γu.his f (DFrac.own 1) hi

/-- Replica bounds at `0` for every id of `ids`, into a ghost map without them. -/
theorem his_alloc_list (γ : GName) :
    ∀ (ids : List w64) (m : GMap w64 w64), ids.Nodup → (∀ id ∈ ids, m !! id = none) →
      ⊢ ghostMapAuth (GF := GF) γ 1 m ==∗ ∃ m' : GMap w64 w64, ghostMapAuth γ 1 m' ∗
        [∗list] id ∈ ids, ghostMapElem γ id (DFrac.own 1) (W64 0)
  | [], m, _, _ => by
    iintro H
    imodintro
    iexists m
    iframe H
    iapply BigSepL.bigSepL_nil.2; iempintro
  | id :: ids, m, hnd, hm => by
    iintro H
    have h0 : m !! id = none := hm id List.mem_cons_self
    imod ghost_map_insert id (W64 0) h0 $$ H with ⟨H, Hid⟩
    have hnd' := List.nodup_cons.1 hnd
    have hm' : ∀ id' ∈ ids, (<[id := W64 0]> m) !! id' = none := by
      intro id' h'
      have hne : id ≠ id' := fun e => hnd'.1 (by subst e; exact h')
      rw [GMap.lookup_insert_ne _ _ hne]
      exact hm id' (List.mem_cons_of_mem _ h')
    imod his_alloc_list γ ids _ hnd'.2 hm' $$ H with ⟨%m', H, Hs⟩
    imodintro
    iexists m'
    iframe H
    iapply BigSepL.bigSepL_cons.2
    iframe Hid Hs

/-- **kvudp's names** (see the file header): the names' invariant, empty, with every replica's bound
at `0`. -/
theorem kvudp_names_alloc (E : CoPset) (ids : List w64) (hnd : ids.Nodup) :
    ⊢ |={E}=> ∃ γu : UdpNames, udpMsgInvG (GF := GF) γu ∗ [∗list] id ∈ ids, udpHiG γu id (W64 0) := by
  imod ghost_map_alloc_empty (GF := GF) (K := MsgKey) (V := List w8) with ⟨%γm, Hm⟩
  imod ghost_map_alloc_empty (GF := GF) (K := MsgKey) (V := Bool) with ⟨%γt, Ht⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64 × w64) (V := w64) with ⟨%γc, Hc⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := w64) with ⟨%γh, Hh⟩
  imod his_alloc_list γh ids ∅ hnd (fun _ _ => rfl) $$ Hh with ⟨%H, Hh, Hs⟩
  imod inv_alloc udpMsgN E iprop(∃ (M : GMap MsgKey (List w8)) (T : GMap MsgKey Bool)
      (C : GMap (w64 × w64) w64) (H : GMap w64 w64),
    ghostMapAuth γm 1 M ∗ ghostMapAuth γt 1 T ∗ ghostMapAuth γc 1 C ∗
    ghostMapAuth γh 1 H ∗ ⌜UdpMsgOk M T C H⌝) $$ [Hm Ht Hc Hh] with #Hinv
  · inext
    iexists ∅, ∅, ∅, H
    iframe Hm Ht Hc Hh
    ipureintro
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun fb c hc => ?_⟩
    · simp at hk
    · simp at hk
    · simp at hc
  imodintro
  iexists ⟨γm, γt, γc, γh⟩
  unfold udpMsgInvG udpHiG
  iframe Hinv Hs

/-- **The replicas' addresses' invariants** (see the file header): one per address of `rs`, from its
datagrams, none. -/
theorem kvudp_addrs_alloc (F : KvFacts GF) (γu : UdpNames) (E : CoPset) :
    ∀ rs : List GoString,
      ⊢ ([∗list] a ∈ rs, udpSent (extGlobalGS udpExt (G := G)) a []) ={E}=∗
        [∗list] a ∈ rs, udpAddrInvG F γu a
  | [] => by
    iintro -
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | a :: rs => by
    iintro Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Ha, Hs⟩
    imod inv_alloc udpSentN E iprop(∃ ms, udpSent (extGlobalGS udpExt (G := G)) a ms ∗
      [∗list] d ∈ ms, udpDgOkG F γu d) $$ [Ha] with #Hi
    · inext
      iexists []
      iframe Ha
      iapply BigSepL.bigSepL_nil.2; iempintro
    imod kvudp_addrs_alloc F γu E rs $$ Hs with Hs
    imodintro
    iapply BigSepL.bigSepL_cons.2
    unfold udpAddrInvG
    iframe Hi Hs

/-- kvudp's start: the names, and the replicas' addresses' invariants, from the UDP extension's start
resources. -/
theorem kvudp_udp_alloc (F : KvFacts GF) (E : CoPset) (rs : List GoString) (ids : List w64)
    (hnd : rs.Nodup) (hok : ∀ a ∈ rs, addrOk a = true) (hids : ids.Nodup) (g : UdpGlobal) :
    ⊢ Udp.udpStart (extGlobalGS udpExt (G := G)) g ={E}=∗
      ∃ γu : UdpNames, udpMsgInvG (GF := GF) γu ∗ ([∗list] a ∈ rs, udpAddrInvG F γu a) ∗
        [∗list] id ∈ ids, udpHiG γu id (W64 0) := by
  iintro Hs
  unfold Udp.udpStart
  ihave Hs := bigSepM_take_list (fun a ms => udpSent (extGlobalGS udpExt (G := G)) a ms)
    (fun _ => ([] : List (List w8))) (addrSpace ([] : List (List w8))) rs hnd
    (fun a ha => addrSpace_lookup_ok _ (hok a ha)) $$ Hs
  imod kvudp_names_alloc E ids hids with ⟨%γu, #Hm, Hh⟩
  imod kvudp_addrs_alloc F γu E rs $$ Hs with Ha
  imodintro
  iexists γu
  iframe Hm Ha Hh

end udpG

/-! ## A replica's generation -/

section gen
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [π : Net.NetProtoGS]
variable [go.IntoValInj GoString]

theorem udpAddrInv_eqG (F : KvFacts GF) (γu : UdpNames) (a : GoString) :
    udpAddrInv (GF := GF) F γu a = udpAddrInvG (G := hG.goose_globalGS) F γu a := rfl

theorem udpMsgInv_eqG (γu : UdpNames) :
    udpMsgInv (GF := GF) γu = udpMsgInvG (G := hG.goose_globalGS) γu := rfl

theorem udpHi_eqG (γu : UdpNames) (f hi : w64) :
    udpHi (GF := GF) γu f hi = udpHiG (G := hG.goose_globalGS) γu f hi := rfl

/-- The address invariants at every address map of the replicas' addresses. -/
theorem kvudp_addrsInv (F : KvFacts GF) (γu : UdpNames) (rs : List GoString)
    (M : GMap w64 GoString) (hM : addrMapOk rs M) :
    udpMsgInvG (G := hG.goose_globalGS) γu ∗
      □ ([∗list] a ∈ rs, udpAddrInvG (G := hG.goose_globalGS) F γu a) ⊢ udpAddrsInv F γu M := by
  unfold udpAddrsInv
  iintro ⟨#Hm, #Ha⟩
  rw [udpMsgInv_eqG]
  iframe Hm
  imodintro
  iintro %pid %a ⟨%hpa, -⟩
  have hl := hM pid
  rw [hpa] at hl
  split at hl
  · rw [udpAddrInv_eqG]
    iapply BigSepL.bigSepL_lookup (Φ := fun _ a => udpAddrInvG (G := hG.goose_globalGS) F γu a)
      hl.symm $$ Ha
  · cases hl

/-- **The boot file's part of a generation, at its first tree `V`** (see the file header). -/
def udpGenAt (γu : UdpNames) (id : w64) (f : DurFs.DFile) (R : Fs.Roots) (V : Fs.Hist) :
    IProp GF :=
  iprop(∃ (v : Option GoString) (hi n : w64), ⌜bootVal v n ∧ uint.nat hi ≤ uint.nat n⌝ ∗
    Fs.osInv ∗ Fs.osSharedInv R ∗ Fs.osCallPerm (Fs.callKey R f.d) (1 : Qp).half ∗
    Fs.osNames f.J (.only [f.b, f.tb]) (DFrac.own 1) (Fs.namesOf V f.J (.only [f.b, f.tb])) ∗
    DurFs.durFound f V.now v ∗ DurFs.durFoundTmp f V.now ∗ udpHi γu id hi)

variable [KdStor GF]

/-- `kvGenAt` holds its tree's empty log. -/
theorem kvGenAt_nil (γ : KdNames) (id : w64) (f : DurFs.DFile) (R : Fs.Roots) (V : Fs.Hist) :
    kvGenAt (GF := GF) γ id f R V ⊢ ⌜V.2 = []⌝ ∗ kvGenAt γ id f R V := by
  iintro H
  iunfold kvGenAt at H
  icases H with ⟨%S, %v, %hV, H⟩
  isplitr
  · ipureintro; exact hV
  iunfold kvGenAt
  iexists S, v
  isplitr
  · ipureintro; exact hV
  iexact H

/-- **Replica `id`'s generation before its boot**, for its directory `dir` at the root `J` of the
roots `R` (see the file header). -/
def kvudpGen (γ : KdNames) (γu : UdpNames) (id : w64) (dir : GoString) (J : Fs.Ino) (R : Fs.Roots) :
    IProp GF :=
  iprop(∃ V : Fs.Hist, kvGenAt γ id (kvDFile dir J id) R V ∗
    udpGenAt γu id (kvBootDFile dir J id) R V)

/-- The boot file's part, from the rest of the directory (`kvDirRest`) and what the generation found
at the boot file's names. -/
theorem udpGen_of_rest (γu : UdpNames) (id : w64) (dir : GoString) (J : Fs.Ino) (R : Fs.Roots)
    (V : Fs.Hist) (v : Option GoString) (hi n : w64) (hv : bootVal v n)
    (hn : uint.nat hi ≤ uint.nat n) :
    ⊢ Fs.osInv (GF := GF) -∗ kvDirRest (kvDFile dir J id) R V -∗
      DurFs.durFound (kvBootDFile dir J id) V.now v -∗ DurFs.durFoundTmp (kvBootDFile dir J id) V.now -∗
      udpHi γu id hi ={⊤}=∗ udpGenAt γu id (kvBootDFile dir J id) R V := by
  iintro #Hos Hdr Hf Ht Hhi
  unfold kvDirRest
  icases Hdr with ⟨#Hsh, Hcp, Hj⟩
  have hfr := kvBoot_names_fresh (kvDFile dir J id) (kvBootDFile dir J id) (decimalB (uint.nat id))
    (decimalB (uint.nat id)) rfl rfl
  have e1 : (kvDFile dir J id).J = (kvBootDFile dir J id).J := rfl
  have e2 : (kvDFile dir J id).d = (kvBootDFile dir J id).d := rfl
  rw [e1, e2]
  imod osNames_take2 R V (kvBootDFile dir J id).J [(kvDFile dir J id).b, (kvDFile dir J id).tb]
    (kvBootDFile dir J id).b (kvBootDFile dir J id).tb hfr.1 hfr.2 ⊤ (fun _ _ => CoPset.mem_full)
    $$ Hsh Hj with ⟨Hj, -⟩
  imodintro
  unfold udpGenAt
  iexists v, hi, n
  isplitr
  · ipureintro; exact ⟨hv, hn⟩
  isplitr
  · iexact Hos
  isplitr
  · iexact Hsh
  isplitl [Hcp]
  · iexact Hcp
  isplitl [Hj]
  · iexact Hj
  iframe Hf Ht Hhi

end gen

/-! ## The boot file's `durable` file -/

theorem udpboot_lit : ∀ x ∈ (go!"udp-boot-" : GoString), x ≠ (47 : w8) ∧ x ≠ (0 : w8) := by
  decide

theorem durable_udpboot_lit :
    ∀ x ∈ (go!".durable-" ++ go!"udp-boot-" : GoString), x ≠ (47 : w8) ∧ x ≠ (0 : w8) := by
  decide

/-- **`durable` manages the boot file** (`kvDFile_ok`'s): `dir` a root, short enough, the id below
`2^32`. -/
theorem kvBootDFile_ok (dir : GoString) (J : Fs.Ino) (id : w64) (hr : Fs.RootForm dir)
    (hd : dir.length < 2 ^ 39) (hid : uint.nat id < 2 ^ 32) : (kvBootDFile dir J id).Ok := by
  have hlen := decimalB_length (uint.nat id) hid
  have hb := name_of_long (go!"udp-boot-" ++ decimalB (uint.nat id)) (by simp)
    (noSlashNul _ _ udpboot_lit)
  have htb := name_of_long (go!".durable-" ++ go!"udp-boot-" ++ decimalB (uint.nat id)) (by simp)
    (noSlashNul _ _ durable_udpboot_lit)
  have htb' : (kvBootDFile dir J id).tb = go!".durable-" ++ go!"udp-boot-" ++ decimalB (uint.nat id) := by
    simp [kvBootDFile, DurFs.DFile.tb]
  refine ⟨cleanAbs_of_rootForm dir hr, hb.2, ?_, hb.1, ?_, ?_⟩
  · rw [htb']; exact htb.2
  · rw [htb']; exact htb.1
  · rw [htb', show (kvBootDFile dir J id).d = dir from rfl]
    simp only [List.length_append]
    have : (go!".durable-" : GoString).length = 9 := by decide
    have : (go!"udp-boot-" : GoString).length = 9 := by decide
    omega

/-- **The boot file's path is the program's** (`BootFileOf`'s, `kvBootFileName`). -/
theorem kvBootDFile_name (dir : GoString) (J : Fs.Ino) (id : w64) :
    (kvBootDFile dir J id).name = kvBootFileName dir id := by
  have : (go!"/udp-boot-" : GoString) = slashB :: go!"udp-boot-" := by decide
  simp [kvBootDFile, DurFs.DFile.name, kvBootFileName, this]

/-! ## A replica's program and generations -/

section replica
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [Net.NetProtoGS] [KdStor GF]
variable [sem : go.Semantics]
variable [github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
variable [net.Assumptions]
variable [net.FieldAssumptions] [net.UdpFieldAssumptions]
variable [go_etcd_io.raft.v3.Assumptions]
variable [github_com.mit_pdos.gokv.trusted_proph.Assumptions]
variable [github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]
variable [time.Assumptions]
variable [github_com.mit_pdos.etcd_grove.examples.lib.lintest.Assumptions]
variable [NaInvG GF]
variable [_root_.Perennial.internal.filepathlite.Assumptions]
variable [_root_.Perennial.path.filepath.Assumptions]
variable [os.Assumptions]
variable [os.fileStat.FieldAssumptions]
variable [os.file.FieldAssumptions]
variable [syscall.Assumptions]
variable [_root_.Perennial.errors.Assumptions]
variable [_root_.Perennial.log.NewModel]

/-- **A replica's program** (`ReplicaLinked.lean`'s `kvReplica_wp`, with `RunNodeUDP`): from the
generation's empty package state, the replica's address protocols and, at every address map, the
start resource and the UDP side's (`udpProcStart`). -/
theorem kvudpReplica_wp (γ : KdNames) (vs : List w64) (cl : ClusterConfig) (addrs dir : GoString) (id : w64)
    (γu : UdpNames)
    (hvc : validCluster (splitAddrs addrs) (uint.nat cl.voters) (uint.nat cl.maxSizePerMsg)
      (uint.nat cl.maxCommittedSizePerReady) (uint.nat cl.maxInflightMsgs) = true)
    (hid1 : 1 ≤ uint.nat id) (hid2 : uint.nat id ≤ (splitAddrs addrs).length) :
    ⊢ ownGoState (GF := GF) ∅ -∗
      (∀ a, ⌜(splitAddrs addrs)[uint.nat id - 1]? = some a⌝ -∗
        addrProto a (kvP (kvFacts γ (fun _ => True)) id) (kvQ (kvFacts γ (fun _ => True)) id)) -∗
      (raft_kvcheck.connGlobals -∗ context.isClosedchanInit -∗ ∀ M, ⌜addrMapOk (splitAddrs addrs) M⌝ -∗
        kvNodeStart γ vs dir id dir ⟨cl.voters, cl.preVote, cl.checkQuorum, cl.stepDownOnRemoval,
          cl.maxSizePerMsg, cl.maxCommittedSizePerReady, cl.maxInflightMsgs⟩ M ∗
        udpProcStart (kvFacts γ (fun _ => True)) γu id dir M) -∗
      WP (kvudpReplicaProgram cl addrs dir id) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro Hgs Hproto HS
  unfold kvudpReplicaProgram
  wp_apply (github_com.mit_pdos.etcd_grove.examples.raft.kvnet.wp_initialize' _
      github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getIsPkgInit_wf) $$ [Hgs] as ⟨-, #Hpkg⟩
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  ihave ⟨#Hnet, #Hctx⟩ := kvnet_pkg_deps $$ Hpkg
  ihave #Hcg := connGlobals_of_net $$ Hnet
  ihave #Hcc := context.isClosedchanInit_of_init $$ Hctx
  ispecialize HS $$ Hcg Hcc
  unfold raft_kvcheck.connGlobals
  icases Hcg with ⟨%eof, %ed, %et, #Heof, #Hed, -⟩
  wp_pures
  wp_apply (kvudpLink.raft_kvnet.wp_RunNodeUDP γ vs dir γu id addrs dir
      cl.voters cl.preVote cl.checkQuorum cl.stepDownOnRemoval cl.maxSizePerMsg
      cl.maxCommittedSizePerReady cl.maxInflightMsgs eof ed hvc hid1 hid2) $$ [Hproto HS]
  · iframe Hproto HS Heof Hed Hcc
  ipureintro; rfl

/-- **A replica's generation** (the body of `CrashBootWpU` for replica `id`, at the generation's
storage registry): kvnet's boot and the boot file's (`udp_gen_boot`), the program's WP
(`kvudpReplica_wp`), and the crash obligation: kvnet's `kvGen_crash` (with the one later credit),
then the boot file's `udp_boot_crash` on the crash's rest, which give the next generation's
`kvudpGen` at the same directory. -/
theorem kvudpRep_gen (γ : KdNames) (γu : UdpNames) (vs : List w64) (cl : ClusterConfig) (addrs dir : GoString)
    (id : w64) (J : Fs.Ino) (R : Fs.Roots)
    (hvc : validCluster (splitAddrs addrs) (uint.nat cl.voters) (uint.nat cl.maxSizePerMsg)
      (uint.nat cl.maxCommittedSizePerReady) (uint.nat cl.maxInflightMsgs) = true)
    (hid1 : 1 ≤ uint.nat id) (hid2 : uint.nat id ≤ (splitAddrs addrs).length)
    (hid32 : uint.nat id < 2 ^ 32)
    (hR : Fs.RootsOk R) (hr : (dir, J) ∈ R) (hdir : dir.length < 2 ^ 39)
    (hmax : uint.nat id ≤ γ.max)
    (hγ : γ.r.cluster.dup = true ∧ γ.r.cluster.bootLen = 0 ∧ Cluster.trace γ.r.cluster = none ∧
      γ.r.cluster.snapLoc = (fun _ => none) ∧ γ.r.cluster.maxData = none ∧ γ.max < 2 ^ 32)
    (hopts : kvOptsOk ⟨cl.voters, cl.preVote, cl.checkQuorum, cl.stepDownOnRemoval,
      cl.maxSizePerMsg, cl.maxCommittedSizePerReady, cl.maxInflightMsgs⟩)
    (hvs : vs = raft_kvreconf.bootVoters (uint.nat cl.voters)) :
    ⊢ kdStorInv (GF := GF) -∗ kdCluster γ vs -∗ readyFits γ.r.cluster kdRaftN -∗
      □ (∀ a, ⌜(splitAddrs addrs)[uint.nat id - 1]? = some a⌝ -∗
        addrProto a (kvP (kvFacts γ (fun _ => True)) id) (kvQ (kvFacts γ (fun _ => True)) id)) -∗
      □ (∀ M, ⌜addrMapOk (splitAddrs addrs) M⌝ -∗ kvPeerAddrs γ id M) -∗
      udpMsgInvG (G := hG.goose_globalGS) γu -∗
      □ ([∗list] a ∈ splitAddrs addrs, udpAddrInvG (G := hG.goose_globalGS)
        (kvFactsG γ (fun _ => True)) γu a) -∗
      kvudpGen γ γu id dir J R -∗ ownGoState ∅ ={⊤}=∗
      (WP (kvudpReplicaProgram cl addrs dir id) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} ∗
        ∀ (L' : GooseLocalGS GF) (V' : Fs.Hist), £ 1 -∗
          crashed (hC := hG.goose_localGS.goose_crashGS) -∗ Fs.osInv (L := L') -∗
          Fs.crashRest (fun _ _ => True) (Fs.gooseOsGS (L := hG.goose_localGS))
            (Fs.gooseOsGS (L := L')) [] false V' ={⊤}=∗
          kvudpGen (hG := ⟨hG.goose_globalGS, L'⟩) γ γu id dir J R) := by
  iintro #Hsi #Hcl #Hrf #Hpr #Hpeer #Hum #Hua Hg Hgs
  have hroot := (hR.2.2 _ hr).1
  have hf := kvDFile_ok dir J id hroot hdir hid32
  have hbf := kvBootDFile_ok dir J id hroot hdir hid32
  iunfold kvudpGen at Hg
  icases Hg with ⟨%V, Hk, Hu⟩
  icases kvGenAt_nil γ id (kvDFile dir J id) R V $$ Hk with ⟨%hV, Hk⟩
  ihave Hk := kvGen_of γ id (kvDFile dir J id) R V $$ Hk
  imod kvGen_boot γ vs dir id (kvDFile dir J id) R hR hr rfl hf (kvDFile_name dir J id)
    ⟨hid1, hmax⟩ $$ Hcl Hk with ⟨%fl, ⟨%hfl1, %hfl2⟩, Hst, Hck⟩
  iunfold udpGenAt at Hu
  icases Hu with ⟨%v, %hi, %n, ⟨%hv, %hn⟩, #Hos, #Hsh, Hcp, Hj, Hf, Ht, Hhi⟩
  imod udp_gen_boot γu id dir (kvBootDFile dir J id) R V v hi n (1 : Qp).half hV hr hbf
    (kvBootDFile_name dir J id) hv hn $$ Hos Hsh Hcp Hj Hf Ht Hhi
    with ⟨%bn, ⟨%hbn1, %hbn2⟩, Hbs, Hbk⟩
  imodintro
  isplitl [Hgs Hst Hbs]
  · iapply kvudpReplica_wp γ vs cl addrs dir id γu hvc hid1 hid2 $$ Hgs Hpr
    iintro #Hcg #Hcc %M %hM
    isplitl [Hst]
    · unfold kvNodeStart
      isplitr
      · ipureintro; rfl
      iexists fl, (1 : Qp).half
      iframe Hst
      isplitr
      · unfold kvStartGlobals
        unfold raft_kvcheck.connGlobals
        icases Hcg with ⟨%eof, %ed, %et, -, #Hed, #Het⟩
        iframe Hrf Hsi Hcc
        isplitr
        · ipureintro; exact hγ
        isplitr
        · iexists et; iexact Het
        · iexists ed; iexact Hed
      isplitr
      · iapply Hpeer; ipureintro; exact hM
      ipureintro; exact ⟨hopts, hvs⟩
    · unfold udpProcStart
      isplitr
      · rw [kvFacts_eq]
        iapply kvudp_addrsInv (kvFactsG γ (fun _ => True)) γu (splitAddrs addrs) M hM
        iframe Hum Hua
      iexists bn, (1 : Qp).half
      iexact Hbs
  · iintro %L' %V' Hlc #Hcr #Hos' Hrest
    iunfold udpBootKeep at Hbk
    icases Hbk with ⟨#Hbi, Htk, #Hdi, Hdc, #Hsh0⟩
    imod kvGen_crash γ vs id fl L' V' $$ Hcl Hck Hlc Hcr Hrest Hos' with ⟨Hg', Hdr, %D, %hD, Hrest⟩
    rw [hfl1] at hD
    rw [hfl1, hfl2]
    imod Fs.crashRest_treeWf (fun _ _ => True) hG.goose_localGS L' D true V' bn.fR ⊤
      (fun _ _ => CoPset.mem_full) $$ Hsh0 Hrest with ⟨%hwf, Hrest⟩
    have hfr := kvBoot_names_fresh (kvDFile dir J id) (kvBootDFile dir J id) (decimalB (uint.nat id))
      (decimalB (uint.nat id)) rfl rfl
    have hD' : ∀ i ∈ D, V'.now.entry bn.df.J bn.df.b ≠ some (.file i) ∧
        V'.now.entry bn.df.J bn.df.tb ≠ some (.file i) := by
      rw [hbn1]
      intro i hi
      have hu := hwf.2.2.2.2
      have hne : ∀ b, b ∉ [(kvDFile dir J id).b, (kvDFile dir J id).tb] →
          V'.now.entry J b ≠ some (.file i) := by
        intro b hb he
        rcases hD i hi with h | h
        · exact hb ((hu _ _ _ _ _ he h).2 ▸ List.mem_cons_self ..)
        · exact hb ((hu _ _ _ _ _ he h).2 ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
      exact ⟨hne _ hfr.1, hne _ hfr.2⟩
    imod udp_boot_crash γu id bn L' D true V' hD' $$ [Hbi Htk Hdi Hdc Hsh0] Hcr Hrest
      with ⟨%v', %hi', %n', %D'', ⟨%hv', %hn'⟩, Hhi, Hf, Ht, -⟩
    · unfold udpBootKeep
      iframe Hbi Htk Hdi Hdc Hsh0
    rw [hbn1]
    imod udpGen_of_rest (hG := ⟨hG.goose_globalGS, L'⟩) γu id dir J R V' v' hi' n' hv' hn'
      $$ Hos' Hdr Hf Ht [Hhi] with Hu
    · unfold udpHi
      iexact Hhi
    imodintro
    iunfold kvudpGen
    iexists V'
    iframe Hg' Hu

/-- **The checking client's program returns** (kvnet's `kvcheck_wp_program`, over kvudp's
extensions). -/
theorem kvudpCheck_wp_program (γ : KdNames) (cl : ClusterConfig) (addrs : GoString)
    (hv : validAddrs (splitAddrs addrs) (uint.nat cl.voters) = true)
    (hrb : receiptBound GF ≤ 2 ^ 63) :
    ⊢ rkvInv γ -∗ rkvVal γ raft_kvreconf.kvEmpty -∗
      raft_kvcheck.kvCnt γ (splitAddrs addrs).length false (W64 0) -∗
      raft_kvcheck.kvCnt γ (splitAddrs addrs).length true (W64 0) -∗
      raft_kvcheck.addrsProto (kvFacts γ (fun _ => True)) (splitAddrs addrs) -∗
      ownGoState ∅ -∗
      WP (kvudpCheckProgram cl addrs) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro #Hinv Hval Hc1 Hc2 #Haddrs Hgs
  unfold kvudpCheckProgram
  wp_apply (github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.wp_initialize' _
      github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.getIsPkgInit_wf) $$ [Hgs]
    as ⟨-, #Hpkg⟩
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  ihave ⟨#Hnet, #Hctx⟩ := kvcheck_pkg_deps $$ Hpkg
  ihave #Hcg := connGlobals_of_net $$ Hnet
  ihave #Hcc := context.isClosedchanInit_of_init $$ Hctx
  wp_pures
  wp_apply (kvnetLink.raft_kvcheck.wp_Check γ addrs cl.voters hv hrb) $$ [Hval Hc1 Hc2]
  · iframe Hcc Hcg Hinv Hval Hc1 Hc2 Haddrs
  ipureintro; rfl

end replica

/-! ## The deployment -/

section deploy
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]
variable [π : Net.NetProtoGS]

instance kdSnapInv_persistentU (γ : KdNames) : Persistent (kdSnapInv (GF := GF) γ) := by
  unfold kdSnapInv; infer_instance

instance rkvInv_persistentU (γ : KdNames) : Persistent (rkvInv (GF := GF) γ) := by
  unfold rkvInv; infer_instance

/-- **What every replica and the client share** (kvnet's `kvGlobals`, over kvudp's extensions), and
kvudp's: the names' invariant and the replicas' addresses' invariants. -/
def kvudpGlobals (γ : KdNames) (vs : List w64) (rs : List GoString) (γu : UdpNames) : IProp GF :=
  iprop(isCluster γ.r.cluster kdRaftN ∗ confPolicy γ.r.cluster kdConfN raft_kvreconf.kvrRule ∗
    confAt γ.r.cluster 0 (Membership.simple (GMap.listToSet vs)) ∗ kdSnapInv γ ∗ rkvInv γ ∗
    readyFits γ.r.cluster kdRaftN ∗
    ([∗list] i ↦ a ∈ rs, Net.addrProto a (kvP (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1)))
      (kvQG (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1)))) ∗
    udpMsgInvG γu ∗ [∗list] a ∈ rs, udpAddrInvG (kvFactsG γ (fun _ => True)) γu a)

instance kvudpGlobals_persistent (γ : KdNames) (vs : List w64) (rs : List GoString) (γu : UdpNames) :
    Persistent (kvudpGlobals (GF := GF) γ vs rs γu) := by
  unfold kvudpGlobals; infer_instance

/-- **Replica `id`'s generation `L`, before its boot**: the globals, its `kvudpGen` at the root `J` of
`dir` among the roots `R`, and the generation's empty package state. -/
def kvudpPc (γ : KdNames) (vs : List w64) (rs : List GoString) (γu : UdpNames) (dir : GoString)
    (id : w64) (L : GooseLocalGS GF) : IProp GF :=
  letI : HeapGS .hasLC GF := ⟨G, L⟩
  letI : KdStor GF := ⟨0⟩
  iprop(kvudpGlobals γ vs rs γu ∗
    (∃ (J : Fs.Ino) (R : Fs.Roots), ⌜(dir, J) ∈ R ∧ Fs.RootsOk R⌝ ∗ kvudpGen γ γu id dir J R) ∗
    ownGoState ∅)

/-- **The checking client's share** (kvnet's `kvClient`). -/
def kvudpClient (γ : KdNames) (rs : List GoString) : IProp GF :=
  iprop(rkvInv γ ∗ rkvVal γ raft_kvreconf.kvEmpty ∗ ghostVar γ.r.opn (1 : Qp).half (W64 0) ∗
    ([∗list] id ∈ bootVoters rs.length, id ↪[γ.r.rseq] W64 0) ∗
    [∗list] i ↦ a ∈ rs, Net.addrProto a (kvP (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1)))
      (kvQG (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1))))

variable [lctx : GoLocalContext] [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
variable [field_sem : net.FieldAssumptions] [udp_field_sem : net.UdpFieldAssumptions]
variable [os_file_sem : os.file.FieldAssumptions] [os_stat_sem : os.fileStat.FieldAssumptions]
variable [log_sem : log.NewModel] [NaInvG GF]

/-- **Every generation of replica `i + 1`** (`CrashBootWpU`, as kvnet's `kvPc_crashBoot`). -/
theorem kvudpPc_crashBoot (γ : KdNames) (γu : UdpNames) (cl : ClusterConfig) (rs : List GoString)
    (dir : GoString) (i : Nat)
    (hi : i < rs.length) (hnd : rs.Nodup) (hok : ∀ a ∈ rs, addrOk a = true)
    (hlen : rs.length < 2 ^ 32) (hcl : cl.Ok rs.length) (hdir : dir.length < 2 ^ 39)
    (hγ : γ.max = rs.length ∧ γ.r.cluster.dup = true ∧ γ.r.cluster.bootLen = 0 ∧
      Cluster.trace γ.r.cluster = none ∧ γ.r.cluster.snapLoc = (fun _ => none) ∧
      γ.r.cluster.maxData = none) :
    CrashBootWpU (GF := GF) (kvudpReplicaProgram cl (List.intercalate go!"," rs) dir (W64 ((i : Int) + 1)))
      (kvudpPc γ (bootVoters (uint.nat cl.voters)) rs γu dir (W64 ((i : Int) + 1))) := by
  intro L hL
  subst hL
  try dsimp only
  letI hG : HeapGS .hasLC GF := ⟨G, L⟩
  have hsplit := splitAddrs_intercalate rs (List.ne_nil_of_length_pos (by omega)) hok
  obtain ⟨hid1, hid2, hid32, hget⟩ := replica_id rs i hi hlen
  unfold kvudpPc
  try dsimp only
  iintro ⟨#Hgl, ⟨%J, %R, ⟨%hJ, %hR⟩, Hg⟩, Hgs⟩ -
  imod kdStor_alloc (GF := GF) ⊤ with ⟨%k, #Hsi⟩
  letI : KdStor GF := k
  have Hrep := kvudpRep_gen (GF := GF) γ γu (bootVoters (uint.nat cl.voters)) cl
    (List.intercalate go!"," rs) dir (W64 ((i : Int) + 1)) J R
    (by rw [hsplit]; exact validCluster_of rs cl hnd hok hlen hcl) hid1 (by rw [hsplit]; exact hid2)
    hid32 hR hJ hdir (by rw [hγ.1]; exact hid2)
    ⟨hγ.2.1, hγ.2.2.1, hγ.2.2.2.1, hγ.2.2.2.2.1, hγ.2.2.2.2.2, by rw [hγ.1]; exact hlen⟩
    (kvOptsOk_of_clOk cl rs.length hcl hlen) rfl
  rw [hsplit] at Hrep
  unfold kvudpGlobals
  icases Hgl with ⟨#Hc, #Hp, #Ha, #Hsn, #Hinv, #Hrf, #Haddrs, #Hum, #Hua⟩
  ihave #Hkc := kvnet_kdCluster γ (bootVoters (uint.nat cl.voters)) $$ Hc Hp Ha Hsn Hinv
    %(hγ.2.2.2.1)
  imod Hrep $$ Hsi Hkc Hrf [] [] Hum Hua Hg Hgs with ⟨Hwp, Hcr⟩
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
  iframe Hgs' Hc Hp Ha Hsn Hinv Hrf Haddrs Hum Hua
  iexists J, R
  iframe Hg'
  ipureintro; exact ⟨hJ, hR⟩

/-- **Replica `id`'s first generation**: from the file extension's start resources of a file system
as on disk in which `dir` is an empty root, the id's durable state at `RaftState.init` with its
vacancy, and its boot bound at `0`: `kvudpPc` (kvnet's `kvGen_first`, then the boot file's part from
the rest of the directory: no file at its names). -/
theorem kvudpPc_first (γ : KdNames) (vs : List w64) (rs : List GoString) (γu : UdpNames)
    (dir : GoString) (id : w64)
    (st : Fs.OsState) (hst : Fs.FsInit st) (hroot : dir ∈ st.fs.roots.map (·.1))
    (hempty : ∀ c, st.lookup (joinPath dir [c]) = none) (hdir : dir.length < 2 ^ 39)
    (hid : uint.nat id < 2 ^ 32) (L : GooseLocalGS GF) (hL : L.goose_go_local_context = lctx) :
    kvudpGlobals γ vs rs γu ∗
      (letI : HeapGS .hasLC GF := ⟨G, L⟩
       iprop(raftState γ.r.cluster id RaftState.init ∗ nodeVacant γ.r.cluster id ∗
        udpHiG γu id (W64 0))) ⊢
      fsStartResU L st -∗ ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗
        kvudpPc γ vs rs γu dir id L := by
  subst hL
  letI hG : HeapGS .hasLC GF := ⟨G, L⟩
  obtain ⟨⟨d', J⟩, hp, hpd⟩ := List.mem_map.1 hroot
  simp only at hpd
  subst hpd
  have hrf := rootForm_of_fsInit hst hp
  have hf := kvDFile_ok d' J id hrf hdir hid
  have hbf := kvBootDFile_ok d' J id hrf hdir hid
  letI : KdStor GF := ⟨0⟩
  iintro ⟨#Hgl, HrS, Hvac, Hhi⟩ Hfs Hgs
  unfold fsStartResU
  icases Hfs with ⟨#Hos, -, Ht⟩
  imod kvGen_first γ id (kvDFile d' J id) st ⊤ hst
    (fsInit_entry_none hst hp hempty _ hf.2.2.2.1)
    (fsInit_entry_none hst hp hempty _ hf.2.2.2.2.1) hp (fun _ _ => CoPset.mem_full)
    $$ Hos Ht HrS Hvac with ⟨Hg, Hdr⟩
  have hnow : Fs.Hist.now (st.fs.treeDur, ([] : List Fs.LogEntry)) = st.fs.treeDur := rfl
  imod udpGen_of_rest γu id d' J st.fs.roots (st.fs.treeDur, []) none (W64 0) (W64 0)
    (Or.inl ⟨rfl, rfl⟩) (Nat.le_refl _) $$ Hos Hdr [] [] [Hhi] with Hu
  · have hb0 : st.fs.treeDur.entry (kvBootDFile d' J id).J (kvBootDFile d' J id).b = none :=
      fsInit_entry_none hst hp hempty _ hbf.2.2.2.1
    unfold DurFs.durFound
    rw [hnow, hb0]
    ipureintro; rfl
  · have ht0 : st.fs.treeDur.entry (kvBootDFile d' J id).J (kvBootDFile d' J id).tb = none :=
      fsInit_entry_none hst hp hempty _ hbf.2.2.2.2.1
    unfold DurFs.durFoundTmp
    rw [hnow, ht0]
    iempintro
  · unfold udpHi udpHiG
    iexact Hhi
  imodintro
  unfold kvudpPc
  try dsimp only
  iframe Hgl Hgs
  iexists J, st.fs.roots
  isplitr
  · ipureintro; exact ⟨hp, hst.2.2.2.1⟩
  iunfold kvudpGen
  iexists (st.fs.treeDur, [])
  iframe Hg Hu

/-- **The checking client** (`StableBootWpU`, as kvnet's `kvClient_stable`). -/
theorem kvudpClient_stable (γ : KdNames) (cl : ClusterConfig) (rs : List GoString) (σc : state)
    (hnd : rs.Nodup) (hok : ∀ a ∈ rs, addrOk a = true) (hlen : rs.length < 2 ^ 32)
    (hcl : cl.Ok rs.length) (hrb : receiptBound GF ≤ 2 ^ 63) :
    StableBootWpU (GF := GF) (kvudpCheckProgram cl (List.intercalate go!"," rs)) σc
      (kvudpClient γ rs) := by
  intro L hL
  subst hL
  try dsimp only
  letI hG : HeapGS .hasLC GF := ⟨G, L⟩
  have hsplit := splitAddrs_intercalate rs (by
    rintro rfl; exact absurd hcl.2.1 (by have := hcl.1; simp; omega)) hok
  letI : KdStor GF := ⟨0⟩
  have H := kvudpCheck_wp_program (GF := GF) γ cl (List.intercalate go!"," rs)
    (by rw [hsplit]; exact validAddrs_of rs cl hnd hok hlen hcl) hrb
  rw [hsplit] at H
  unfold kvudpClient
  iintro ⟨#Hinv, Hval, Hopn, Hrseq, #Haddrs⟩ - Hgs -
  imodintro
  iapply H $$ Hinv Hval [Hopn] [Hrseq] [] Hgs
  · iapply kvnet_kvCnt_op; iexact Hopn
  · iapply kvnet_kvCnt_read; iexact Hrseq
  · iapply kvnet_addrsProto γ _ rs hok; iexact Haddrs

end deploy

/-! ## The theorem -/

section top
variable [go_gctx : GoGlobalContext]

/-- **kvudp is robust** (the statement: `raft_kvudp_robust.spec`). -/
theorem raft_kvudp_robust : raft_kvudp_robust.spec := by
  intro lctx sem package_sem field_sem udp_field_sem os_file_sem os_stat_sem log_sem cl dir replicas
    σc g hcl hn hdir hnd hrep addrs hfresh hig hil
  have hlenrs : (replicas.map (·.1)).length = replicas.length := List.length_map _
  have hok : ∀ a ∈ replicas.map (·.1), addrOk a = true := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
    exact (hrep p.1 p.2 hp).1
  rw [← hlenrs] at hcl hn
  refine robust_of_netFsUdpBoot (GF := kvudpGF) (replicas.map (·.1)) _ _ g _ _ hnd hok ?_
    hfresh hig hil
  intro G hrb
  iintro Hs Hu
  imod Net.netProto_alloc (GF := kvudpGF) ⊤ with ⟨%π, #Hreg⟩
  letI : Net.NetProtoGS := π
  have hv := hcl
  obtain ⟨hv1, hvn, -⟩ := hv
  imod kvnet_store_alloc (GF := kvudpGF) ⊤ (replicas.map (·.1)).length (uint.nat cl.voters) hv1 hvn
    hn (by omega)
    with ⟨%γ, %hγ, #Hc, #Hp, #Ha, #Hsn, #Hinv, #Hrf, Hnodes, Hval, Hopn, Hrseq⟩
  imod kvnet_addrs_alloc (GF := kvudpGF) (F := kvFactsG γ (fun _ => True)) ⊤ (replicas.map (·.1))
    $$ Hreg Hs with #Haddrs
  imod kvudp_udp_alloc (GF := kvudpGF) (kvFactsG γ (fun _ => True)) ⊤ (replicas.map (·.1))
    (bootVoters (replicas.map (·.1)).length) hnd hok
    (raft_kvreconf.bootVoters_nodup _ (by omega)) _ $$ Hu with ⟨%γu, #Hum, #Hua, Hhis⟩
  ihave #Hgl : kvudpGlobals γ (bootVoters (uint.nat cl.voters)) (replicas.map (·.1)) γu $$ []
  · unfold kvudpGlobals
    iframe Hc Hp Ha Hsn Hinv Hrf Haddrs Hum Hua
  imodintro
  iexists (fun i L => kvudpPc γ (bootVoters (uint.nat cl.voters)) (replicas.map (·.1)) γu dir
    (W64 ((i : Int) + 1)) L)
  iexists (fun _ => kvudpClient γ (replicas.map (·.1)))
  isplitr
  · ipureintro
    intro i m hm
    obtain ⟨p, hp, rfl, -⟩ := replica_mem _ replicas i m hm
    have hi : i < replicas.length := (List.getElem?_eq_some_iff.1 hp).1
    exact kvudpPc_crashBoot γ γu cl _ dir i (by omega) hnd hok hn hcl hdir hγ
  isplitr
  · ipureintro
    intro j m hm
    match j, hm with
    | 0, hm =>
      cases hm
      exact kvudpClient_stable γ cl _ σc hnd hok hn hcl (by omega)
  isplitl [Hnodes Hhis]
  · ihave Hn := bootVoters_bigSepL (fun id => iprop(raftState γ.r.cluster id RaftState.init ∗
      nodeVacant γ.r.cluster id)) _
      (replicas.mapIdx fun i p => (kvudpReplicaProgram cl addrs dir (W64 ((i : Int) + 1)), p.2))
      (by simp) $$ Hnodes
    ihave Hh := bootVoters_bigSepL (fun id => udpHiG (G := G) γu id (W64 0)) _
      (replicas.mapIdx fun i p => (kvudpReplicaProgram cl addrs dir (W64 ((i : Int) + 1)), p.2))
      (by simp) $$ Hhis
    ihave Hn := BigSepL.bigSepL_sep_eqv_symm.1 $$ [$Hn $Hh]
    iapply BigSepL.bigSepL_impl $$ Hn
    imodintro
    iintro %k %m %hk ⟨⟨HrS, Hvac⟩, Hhi⟩ %L %hL Hfs Hgs
    obtain ⟨p, hp, rfl, hmem⟩ := replica_mem _ replicas k m hk
    have hk' : k < (replicas.map (·.1)).length := by
      rw [hlenrs]; exact (List.getElem?_eq_some_iff.1 hp).1
    obtain ⟨-, hroot, hempty⟩ := hrep p.1 p.2 (List.mem_of_getElem? hp)
    have hfs : Fs.FsInit (fsOf p.2) := (hil _ (List.mem_append_left _ hmem)).2.1
    iapply kvudpPc_first γ _ _ γu dir _ (fsOf p.2) hfs hroot hempty hdir
      (replica_id _ k hk' hn).2.2.1 L hL $$ [HrS Hvac Hhi] Hfs Hgs
    iframe Hgl HrS Hvac Hhi
  · iapply BigSepL.bigSepL_cons.2
    dsimp only
    isplitl [Hval Hopn Hrseq]
    · unfold kvudpClient
      iframe Hinv Hval Hopn Haddrs Hrseq
    · iapply BigSepL.bigSepL_nil.2
      iempintro

/-- **The example from the theorem**: `raft_kvudp_robust_example.spec` from `raft_kvudp_robust.spec`,
its premises by computation (as kvnet's). -/
theorem raft_kvudp_robust_example_of (H : raft_kvudp_robust.spec) :
    raft_kvudp_robust_example.spec := by
  intro lctx sem package_sem field_sem udp_field_sem os_file_sem os_stat_sem log_sem σ₁ σ₂ σ₃ σ₄ σ₅
    σc g hfs
  have h := @H lctx sem package_sem field_sem udp_field_sem os_file_sem os_stat_sem log_sem
    exampleConfig go!"/var/lib/kvnet"
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


/-- **kvudp is robust, an example**: from `raft_kvudp_robust`. -/
theorem raft_kvudp_robust_example : raft_kvudp_robust_example.spec :=
  raft_kvudp_robust_example_of raft_kvudp_robust

end top

end raft_kvudp
end EtcdGrove
end Perennial
