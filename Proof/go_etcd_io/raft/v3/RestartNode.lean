/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.RestartNode
public import Spec.go_etcd_io.raft.v3.newNode
public import Spec.go_etcd_io.raft.v3.node__run
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.InvAdvance
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Proof.go_etcd_io.raft.v3.ApiVocab
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiView
import Proof.go_etcd_io.raft.v3.InvApiDec
import Proof.go_etcd_io.raft.v3.InvApiJoin
import all Proof.go_etcd_io.raft.v3.InvNodeRule
import Proof.go_etcd_io.raft.v3.SnapValidCert
import Proof.go_etcd_io.raft.v3.StepGhostMode
import Proof.go_etcd_io.raft.v3.InvStorageRead
import Proof.go_etcd_io.raft.v3.ConfchangeApiImpl
import Proof.go_etcd_io.raft.v3.ConfchangeApi
import Proof.go_etcd_io.raft.v3.Protocol.Enter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! Lean-first (no Rocq counterpart).

## `RestartNode(c)` (node.go:281)

(2026-11-02, durability stage II (p)) One triple, as `StartNode`'s: until then a private raw triple
over raft's internals (from an empty storage, the ghost state's names allocated by the caller) and
a wrapper. The client's update fires after the first step (a later credit strips the later of its
`raftState`), inside the id's slot (`raft_restart`), which gives the restarted follower's volatile
half, the slot's whole generation with its free queue, and the restarted log's full-log and I1
facts; raft names the storage at the attach (`restartStorage`'s continuation, inside
`InitialState`'s post: fresh storage names recording the stored committed log's terms up to the
stored commit, `AttachRec`); `NewRawNode` builds the node at the restored state (`rawNodeAt`),
closed here with the restarted ghost state in the cluster's dynamic mode; its table entry is
inserted while the struct is owned whole; then `run`'s ghost state and `go n.run()`. -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Raft's log namespace is in the cluster's. -/
private theorem raftLogN_sub (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (HNs : γ.raft.reNs = N .@ "raft") : (↑(raftLogN γ.raft) : CoPset) ⊆ E := by
  intro p hp
  unfold raftLogN raftN at hp; rw [HNs] at hp
  exact HE p (nclose_subseteq N "raft" p (nclose_subseteq (N .@ "raft") "log" p hp))

/-- **A valid snapshot's certificates** (the API's `snapshotValid` read back at raft's level). -/
private theorem snapValid_raftCert (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (_HU : UniNames γ N) (sv : SnapshotM) :
    ⊢ clusterInv (GF := GF) γ N -∗ EtcdGrove.snapshotValid (GF := GF) γ sv ={E}=∗
      raftSnapCertD γ.raft (snapTrip sv sv.Metadata'.ConfState'.lists) := by
  iintro #Hci Hv
  unfold EtcdGrove.snapshotValid EtcdGrove.isCommittedLogLb EtcdGrove.confAt EtcdGrove.snapMade
  icases Hv with ⟨%l, %m, #Hlb, #Ha, #Hm, %Hp⟩
  obtain ⟨Hlen, -, Hlast, Hcs, H61, Hsz⟩ := Hp
  ihave %Hval := confAt_valid_impl γ l.length m $$ Ha
  ihave %Hres := confAtU_restorable γ l.length m $$ Ha
  iunfold confAtU at Ha
  icases Ha with ⟨%l2, %M, #Hlb2, #HM, %P2⟩
  obtain ⟨hk, c0, g, hm, hf⟩ := P2
  icases isCommittedLogLb_agree_impl γ l l2 $$ [Hlb Hlb2] with %Hcm
  · iframe Hlb Hlb2
  have Hfold : decFold M c0 l = some m := by
    rw [← List.take_length (l := l), take_eq_of_cmp l l2 l.length Hcm (Nat.le_refl _) hk]
    exact hf
  iunfold snapMadeU at Hm
  icases Hm with ⟨%gr, %K, %key, %Hk, #HK, -⟩
  obtain ⟨Hreg, HkK, Hmat⟩ := Hk
  have hm' := hm
  obtain ⟨⟨h0, -, hd, -, Hsok, -, -⟩, -⟩ := hm'
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, -, -⟩
  imod api_lb_committed γ N E HE l $$ Hci Hlb with ⟨%L, %HL, #HLc⟩
  have HD : (DynCfg.ofFold noDec (stOf c0) h0).fold M L = some (cfgOf m) := by
    rw [hm.fold _ hd M L, HL, Hfold]; rfl
  have HLlen : L.length = uint.nat sv.Metadata'.Index' := by rw [← Hlen, ← HL, strip_length]
  have HLlast : L.getLast?.map EntryM.Term' = some sv.Metadata'.Term' := by
    rw [← Hlast, ← HL]; unfold strip; rw [List.getLast?_map, Option.map_map]; rfl
  obtain ⟨hcv, hco, hcl, hcn, hal⟩ := Hcs
  unfold EtcdGrove.Membership.Valid memValid at Hval
  obtain ⟨Hz, Hni⟩ := Hres
  iapply raftSnapCertD_snapTrip γ.raft E L sv (cfgOf m) _ M gr K key
    (raftLogN_sub γ N E HE HNs) hd Hreg Hsok HLlen (by rw [HLlen, ← Hlen]; exact H61) HLlast
    hcv hco hcl hcn hal Hval.1
    (fun x hx h0x => Hz (by
      subst h0x
      simp only [Membership.ids, GMap.elem_of_union]
      rcases hx with h | h | h | h
      · exact .inl (.inl (.inl h))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
      · exact .inr h))
    (fun x hx => Hni x hx) Hsz HD HkK (by rw [HLlen, ← Hlen]; exact Hmat.1) Hmat.2
    $$ Hcinv HLc HM HK

/-- Raft's reading of the contract's `Bnd`: compacting up to it is safe, of the storage's key's
names. (2026-11-01, durability stage I-4: keyed by the storage's key.) -/
private theorem storBnd_raftBnd (γ : Cluster) (K : GName) (sn : StorNames) (c : Nat) :
    ⊢ storKeyNames (GF := GF) K sn -∗ monoNatLbOwn sn.ga 0 -∗ EtcdGrove.storBnd γ K c -∗
      raftBnd sn c := by
  iintro #Hsn #H0 Hb
  unfold EtcdGrove.storBnd EtcdGrove.nodeAppliedLb nodeAppliedLbU raftBnd
  icases Hb with ⟨%k, %Hk, (%Hk0 | ⟨%sn', #Hsn', (#Hl | #Hl | %Hl)⟩)⟩
  · ileft
    iexists 0
    isplitr; · ipureintro; omega
    ileft; iexact H0
  · ihave %He := storKeyNames_agree K sn' sn $$ Hsn' Hsn
    subst He
    ileft
    iexists k
    isplitr; · ipureintro; exact Hk
    ileft; iexact Hl
  · ihave %He := storKeyNames_agree K sn' sn $$ Hsn' Hsn
    subst He
    ileft
    iexists k
    isplitr; · ipureintro; exact Hk
    iright; iexact Hl
  · ihave %He := storKeyNames_agree K sn' sn $$ Hsn' Hsn
    subst He
    iright
    ipureintro; omega

/-- Raft's reading of the contract's `DL` for a valid snapshot: the node on the storage committed
up to its index, so raft certified the term there (or handed out a snapshot past it, or the attach
recorded it). (2026-11-01, durability stage I-4: `nodeCommitLb`, keyed by the storage's key.) -/
private theorem storDL_raftDL (γ : Cluster) (K : GName) (sn : StorNames) (sv : SnapshotM) :
    ⊢ storKeyNames (GF := GF) K sn -∗ EtcdGrove.snapshotValid γ sv -∗
      EtcdGrove.nodeCommitLb γ K (uint.nat sv.Metadata'.Index') -∗
      raftDL sn (uint.nat sv.Metadata'.Index') sv.Metadata'.Term' := by
  iintro #Hsn Hv Hdl
  unfold EtcdGrove.snapshotValid EtcdGrove.isCommittedLogLb EtcdGrove.nodeCommitLb nodeCommitLbU
  icases Hv with ⟨%l1, %m, #Hlb1, -, -, %Hp⟩
  obtain ⟨Hlen, Hpos, Hlast, -⟩ := Hp
  icases Hdl with (%H0 | ⟨%sn', %l, #Hsn', #Hlb, %Hi, #Hdk⟩)
  · exfalso; omega
  ihave %He := storKeyNames_agree K sn' sn $$ Hsn' Hsn
  subst He
  icases isCommittedLogLb_agree_impl γ l1 l $$ [Hlb1 Hlb] with %Hcm
  · iframe Hlb1 Hlb
  have Hpre : l1 <+: l := by
    rcases Hcm with h | h
    · exact h
    · have e := h.eq_of_length (by have := h.length_le; omega)
      rw [e]
      exact ⟨[], List.append_nil _⟩
  obtain ⟨t, Ht⟩ := Hpre
  have Hj : l1.length - 1 < l1.length := by omega
  have Hl1j : l1[l1.length - 1]?.map LogEntry.term = some sv.Metadata'.Term' := by
    rw [← List.getLast?_eq_getElem?]; exact Hlast
  have Hlj : l[l1.length - 1]? = l1[l1.length - 1]? := by
    rw [← Ht, List.getElem?_append_left Hj]
  rw [← Hlj] at Hl1j
  cases hde : l[l1.length - 1]? with
  | none => rw [hde] at Hl1j; cases Hl1j
  | some e =>
    rw [hde] at Hl1j
    simp only [Option.map_some, Option.some.injEq] at Hl1j
    have hte : (LogEntry.toEntries l 0)[l1.length - 1]? =
        some (e.toEntryM (W64 ((0 + (l1.length - 1) + 1 : Nat) : Int))) := by
      rw [toEntries_getElem?, hde]; rfl
    ihave #Hke := (BigSepL.bigSepL_lookup (Φ := fun j (e : EntryM) =>
      raftDL (GF := GF) sn' (j + 1) e.Term') hte) $$ Hdk
    rw [show uint.nat sv.Metadata'.Index' = l1.length - 1 + 1 by omega, ← Hl1j]
    iExactEq Hke; rfl

/-- **The certificate link of fresh storage names** (`certLink`): their `SV` pin the API's
`snapshotValid`, their snapshot pin raft's certificate. -/
private theorem certLink_make (γ : Cluster) (N : Namespace) (HU : UniNames γ N) (sn : StorNames) :
    ⊢ clusterInv (GF := GF) γ N -∗
      savedPredOwn sn.gsv DFrac.discard (EtcdGrove.snapshotValid (GF := GF) γ) -∗
      savedPredOwn sn.gk DFrac.discard (raftSnapCertD (GF := GF) γ.raft) -∗
      ctCommitted γ.raft sn -∗ certLink γ.raft sn := by
  iintro #Hci #Hsv #Hgk #Hct
  have HcN : raftCertN γ.raft = N := HU.2.2.1
  unfold certLink
  iframe Hct
  unfold storCertOk
  isplitr
  · iintro !> %sv %E %HE Hc
    rw [HcN] at HE
    unfold svCert
    icases Hc with ⟨%SV, #Hp, #HSV⟩
    ihave #Heq := saved_pred_agree sn.gsv DFrac.discard DFrac.discard SV
      (EtcdGrove.snapshotValid (GF := GF) γ) sv $$ Hp Hsv
    ihave Hv : ▷ EtcdGrove.snapshotValid (GF := GF) γ sv $$ []
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨Hiff, -⟩
      iapply Hiff $$ HSV
    have : Timeless (EtcdGrove.snapshotValid (GF := GF) γ sv) := by
      have : ∀ s, Timeless (snapMadeU (GF := GF) γ s) := fun s => by
        unfold snapMadeU; infer_instance
      have : ∀ l, Timeless (isCommittedLogLb (GF := GF) γ l) := fun l => by
        unfold isCommittedLogLb; infer_instance
      unfold EtcdGrove.snapshotValid EtcdGrove.isCommittedLogLb EtcdGrove.confAt EtcdGrove.snapMade
      infer_instance
    icases Hv with >Hv
    iapply snapValid_raftCert γ N E HE HU sv $$ Hci Hv
  isplitr
  · iintro !> %k %E %HE Hc
    unfold ksnCert
    icases Hc with ⟨%P, #Hp, #HP⟩
    ihave #Heq := saved_pred_agree sn.gk DFrac.discard DFrac.discard P
      (raftSnapCertD (GF := GF) γ.raft) k $$ Hp Hgk
    ihave Hv : ▷ raftSnapCertD (GF := GF) γ.raft k $$ []
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨Hiff, -⟩
      iapply Hiff $$ HP
    icases Hv with >#Hv
    imodintro; iexact Hv
  · iintro !> %k %E %HE #Hc
    unfold ksnCert
    imodintro
    iexists raftSnapCertD γ.raft
    iframe Hgk
    imodintro; iexact Hc

/-- (2026-11-02, stage II (o)) A location owned whole is not also held read-only. -/
private theorem loc_pts_excl (l a b : Loc) :
    ⊢ (l ↦ a : IProp GF) -∗ l ↦□ b -∗ False := by
  iintro H1 H2
  rw [typedPointsto_unseal_eq l a, typedPointsto_unseal_eq l b]
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  ihave H1 := (show typedPointstoDef (GF := GF) l a (DFrac.own 1) ⊢ heapPointsto l (DFrac.own 1) #a
    from .rfl) $$ H1
  ihave H2 := (show typedPointstoDef (GF := GF) l b DFrac.discard ⊢ heapPointsto l DFrac.discard #b
    from .rfl) $$ H2
  icombine H1 H2 gives %Hv
  obtain ⟨Hv, -⟩ := Hv
  exfalso
  have := DFrac.valid_own_op_discard.1 Hv
  simp at this

/-- (2026-11-02, stage II (o)) A node struct owned whole is not also held read-only (its `rn`
field). -/
private theorem node_pts_excl (n : Loc) (nv nv' : node) :
    ⊢ (n ↦ nv : IProp GF) -∗ n ↦□ nv' -∗ False := by
  iintro H1 H2
  rw [typedPointsto_unseal_eq n nv, typedPointsto_unseal_eq n nv']
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H1
  icases H2 with ⟨-, -, -, -, -, -, -, -, -, -, ⟨H2, -⟩⟩
  iapply loc_pts_excl _ nv.rn' nv'.rn' $$ rn H2

/-- (2026-11-02, stage II (o)) **Registering a node in the cluster's table**, while its struct is
owned whole (so it is not in the table yet): its entry, and the struct read-only from then on. -/
private theorem nodeTab_insert (γ : Cluster) (N : Namespace) (n : Loc) (nv : node) (x : CfgNames) :
    ⊢ nodeTabInv (GF := GF) γ N -∗ n ↦ nv ={⊤}=∗ n ↦□ nv ∗ n ↪[γ.nodeTab]□ x := by
  iintro #Hinv Hn
  unfold nodeTabInv
  iinv Hinv with ⟨%M, >Hauth, >Hm⟩ Hclose
  cases hM : M !! n with
  | some y =>
    ihave Hy := (BigSepM.bigSepM_lookup (Φ := fun (k : Loc) (_ : CfgNames) =>
      iprop(∃ nv : node, k ↦□ nv : IProp GF)) hM) $$ Hm
    icases Hy with ⟨%nv', Hy⟩
    iexfalso
    iapply node_pts_excl n nv nv' $$ Hn Hy
  | none =>
    imod ghost_map_insert_persist n x hM $$ Hauth with ⟨Hauth, #He⟩
    ipersist Hn
    imod Hclose $$ [Hauth Hm] with -
    · inext
      iexists (<[n := x]> M)
      iframe Hauth
      iapply (BigSepM.bigSepM_insert (Φ := fun (k : Loc) (_ : CfgNames) =>
        iprop(∃ nv : node, k ↦□ nv : IProp GF)) hM).2
      iframe Hm
      iexists nv; iexact Hn
    imodintro
    iframe Hn He

/-- (2026-11-02, stage II (p)) The log's shape, read out of the ghost state. -/
private theorem ownRaftGhost_logOk (γ : RaftNames) (id : w64) (s : PState) (md : Bool) :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ ⌜LogOk s⌝ := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  icases ownLogGhost_recs γ id s kl _ $$ Hlg with ⟨%Hl, -⟩
  ipureintro; exact Hl

/-- (2026-11-02, stage II (p)) The commit `loadState` restores from a stored hard state whose commit
is at least the base: the stored one (an empty hard state's is the base, `0`). -/
private theorem committedAfter_restart (σ : StorContents) (h : σ.b ≤ σ.commit) :
    committedAfter σ.base σ.hs = σ.hs.Commit' := by
  unfold committedAfter
  split
  · rename_i he
    obtain ⟨-, -, hc⟩ := he
    simp only [StorContents.b, StorContents.commit, hc] at h
    rw [hc]
    apply BitVec.eq_of_toNat_eq
    have : uint.nat (W64 0) = 0 := rfl
    have h' : uint.nat σ.base.index' = 0 := by omega
    exact h'
  · rfl

/-- (2026-11-02, stage II (p)) **The attach record of a restart**: the terms of the committed log
`F` at the indices `1, …, c`. -/
def restartCt (F : List EntryM) (c : Nat) : List (Nat × w64) :=
  (List.range c).map (fun k => (k + 1, ((F[k]?).map EntryM.Term').getD (W64 0)))

private theorem restartCt_mem {F : List EntryM} {c i : Nat} {t : w64} (hc : c ≤ F.length)
    (h : (i, t) ∈ restartCt F c) : 1 ≤ i ∧ i ≤ c ∧ (F[i - 1]?).map EntryM.Term' = some t := by
  unfold restartCt at h
  rw [List.mem_map] at h
  obtain ⟨k, hk, he⟩ := h
  rw [List.mem_range] at hk
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel, List.getElem?_eq_getElem (show k < F.length by omega)]
  rfl

private theorem restartCt_complete {F : List EntryM} {c i : Nat} (hc : c ≤ F.length) (h1 : 1 ≤ i)
    (h2 : i ≤ c) : ∃ t, (i, t) ∈ restartCt F c ∧ ∀ t', (i, t') ∈ restartCt F c → t' = t := by
  refine ⟨((F[i - 1]?).map EntryM.Term').getD (W64 0), ?_, fun t' ht' => ?_⟩
  · unfold restartCt
    rw [List.mem_map]
    exact ⟨i - 1, by rw [List.mem_range]; omega, Prod.ext (by simp only; omega) rfl⟩
  · obtain ⟨-, -, h⟩ := restartCt_mem hc ht'
    rw [h]; rfl

/-- (2026-11-02, stage II (p)) The stored log's term at an index from its base, from the full log
`fp ++ ents` (`fp` the compacted prefix of the base `b`). -/
private theorem termAt_of_full {b : entryID} {fp ents : List EntryM} {i : Nat} {t : w64}
    (Hf : FullOk b fp) (hb : uint.nat b.index' ≤ i) (h1 : 1 ≤ i) (hi : (i : Int) < 2 ^ 64)
    (ht : ((fp ++ ents)[i - 1]?).map EntryM.Term' = some t) :
    termAt b ents (W64 (i : Int)) = some t := by
  obtain ⟨Hlen, -, Hlast⟩ := Hf
  have hbn := uint_nat_eq b.index'
  have hW : uint.Z (W64 (i : Int)) = i := uint_Z_W64 _ (by omega) hi
  unfold termAt
  by_cases he : i = uint.nat b.index'
  · rw [if_pos (by rw [hW]; omega)]
    have hfl : fp.length = i := by omega
    rw [List.getElem?_append_left (by omega)] at ht
    unfold plogLast at Hlast
    have hgl : fp.getLast? = fp[i - 1]? := by rw [List.getLast?_eq_getElem?, hfl]
    cases hx : fp[i - 1]? with
    | none => rw [hx] at ht; cases ht
    | some x =>
      rw [hgl, hx] at Hlast
      rw [hx] at ht
      simp only [Option.map_some, Option.some.injEq] at ht
      rw [← ht, ← Hlast]; rfl
  · rw [if_neg (by rw [hW]; omega)]
    rw [List.getElem?_append_right (by omega)] at ht
    rw [show (uint.Z (W64 (i : Int)) - uint.Z b.index' - 1).toNat = i - 1 - fp.length by omega]
    simpa using ht

/-- A follower has no pre-candidate campaign to guard. -/
private theorem preGuardF_fol {fp : List EntryM} {s : NState} (h : s.role = .follower) :
    PreGuardF fp s :=
  fun _ hr => absurd (h.symm.trans hr) (by decide)

/-- See the header. -/
private theorem wp_RestartNode_impl
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG))
    (wp_newNode : newNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    EtcdGrove.RestartNode.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.RestartNode.spec
  intro γ N c cv lok si σ csm m Q F H1 H2 H3 H4 H5 H6 H7 H8 H9 Happ Hboot Hcs Hcsl
  -- the configuration point `a`, the applied index the node starts at (named until the post)
  generalize Hae : max σ.b (uint.nat cv.Applied') = a
  have Ha1 : max σ.b (uint.nat cv.Applied') ≤ a := Hae ▸ Nat.le_refl _
  wp_start as ⟨Hc, #Hlg, #Hcl, Hvac, #Hfits, HAU, #Hconf, Hrs⟩
  iunfold EtcdGrove.isCluster at Hcl
  ihave #Hcl' := Hcl
  iunfold isClusterU at Hcl'
  icases Hcl' with ⟨%HU, #Hci, #Hpool, #Htab⟩
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, -, -⟩
  have Hsl := HU.2.1
  -- the configuration point: the cluster's mode, a valid restorable membership
  iunfold EtcdGrove.confAt at Hconf
  ihave %Hval := confAt_valid_impl γ a m $$ Hconf
  ihave %Hres := confAtU_restorable γ a m $$ Hconf
  ihave #Hconf' := Hconf
  iunfold confAtU at Hconf'
  icases Hconf' with ⟨%lA, %MA, #HlbA, #HMA, %HPA⟩
  obtain ⟨HkA, c0m, gA, HmA, HfA⟩ := HPA
  obtain ⟨h0, h1, Hmd⟩ := HmA.mode
  have HD : γ.raft.dyn = some (DynCfg.ofFold noDec (stOf c0m) h0) := HmA.1.2.2.1
  have Hmdb : γ.raft.reDyn.isSome = true := by
    have := reDyn_of HD
    cases h : γ.raft.reDyn with
    | none => exact absurd h this
    | some _ => rfl
  -- the restored hard state's commit, as a word
  have HbootZ : (γ.raft.reBoot.length : Int) ≤ uint.Z σ.hs.Commit' := by
    unfold Cluster.bootLen StorContents.commit at Hboot; have := uint_nat_eq σ.hs.Commit'; omega
  have HsN : (↑(slotN γ.raft cv.ID') : CoPset) ⊆ ↑N := by
    intro p hp
    have := slotN_raftN γ.raft cv.ID' p hp
    unfold raftN at this; rw [HNs] at this
    exact nclose_subseteq N "raft" p this
  -- a later credit, for the update's `▷ raftState`
  wp_auto_lc 1
  -- the client's update, inside the id's slot: the restarted follower's volatile half
  iunfold EtcdGrove.nodeVacant at Hvac
  iunfold nodeVacantU at Hvac
  imod raft_restart ⊤ γ.raft cv.ID' (md := true) σ.base σ.hs.Commit'
    (fun S => StorageHolds S σ)
    (fun S => iprop(Q S ∗ termLB γ.bud S.term ∗ inv budgetN (budgetInv γ.bud)))
    CoPset.subseteq_top Hmdb
    (fun S HS => by
      obtain ⟨Hb1, Hb2, Hb3, -, -, Hbc, Hwc, Hcc, -, -⟩ := HS
      simp only [StorContents.b, StorContents.commit] at Hbc Hwc Hcc
      have := uint_nat_eq σ.hs.Commit'; have := uint_nat_eq σ.base.index'
      have := uint_nat_eq S.commit
      exact ⟨Hb1, by omega, by omega, Hb2, Hwc⟩) HbootZ
    $$ Hvac [HAU Hlc1]
    with ⟨%S, %HS, ⟨HQ, #HtS, #Hbinv⟩, Hg, %gen, Hgen, Hfree, #HI1r⟩
  · have HEo : (⊤ \ ↑N : CoPset) ⊆ ⊤ \ ↑(slotN γ.raft cv.ID') := by
      intro p hp
      rw [Iris.Std.LawfulSet.mem_diff] at hp ⊢
      exact ⟨hp.1, fun h => hp.2 (HsN p h)⟩
    ihave HAU := atomic_update_mask_weaken HEo $$ HAU
    ihave HAU := aupd_aacc $$ HAU
    iunfold atomic_acc at HAU
    imod HAU with ⟨%S, HS, HC⟩
    rcases S with ⟨S, ⟨⟩⟩
    irevert HS
    dsimp only [Std.Tele.app]
    iintro HS
    icases HS with ⟨HS, %HSh⟩
    imod lc_fupd_elim_later $$ Hlc1 HS with HS
    icases HC with ⟨-, Hcomm⟩
    ihave Hcomm := Hcomm $$ %PUnit.unit
    iunfold EtcdGrove.raftState at HS
    iunfold raftStateU at HS
    icases HS with ⟨Hdur, #Htlb0, #Hbi0⟩
    imodintro
    iexists S
    iframe Hdur
    isplitr; · ipureintro; exact HSh
    iintro Hdur
    imod Hcomm $$ [Hdur] with HQ
    · iunfold EtcdGrove.raftState
      unfold raftStateU
      iframe Hdur Htlb0 Hbi0
    imodintro
    iframe HQ Htlb0 Hbi0
  -- the restarted log: its full prefix with records, its committed prefix, its commit's witness,
  -- its last index's record
  icases (entails_wand (persistent_entails_left (ownRaftGhost_cmt γ.raft cv.ID' _))) $$ Hg
    with ⟨Hg, %fp, %Hfp, #Hfr, #Hcmt⟩
  icases (entails_wand (persistent_entails_left (wand_entails
    (ownRaftGhost_commitWit γ.raft cv.ID' _)))) $$ Hg with ⟨Hg, #Hcw⟩
  icases (entails_wand (persistent_entails_left (wand_entails
    (ownRaftGhost_logRecs γ.raft cv.ID' _ true)))) $$ Hg with ⟨Hg, %Hwf, #Hrl⟩
  icases (entails_wand (persistent_entails_left (wand_entails
    (ownRaftGhost_logOk γ.raft cv.ID' _ true)))) $$ Hg with ⟨Hg, %HlogOk⟩
  icases (entails_wand (persistent_entails_left (wand_entails
    (ownRaftGhost_lastRec γ.raft cv.ID' _)))) $$ Hg with ⟨Hg, #Hlr, %Hl64⟩
  ihave %HFI := HI1r $$ %fp %Hfp Hfr
  obtain ⟨HDF, HI1⟩ := HFI
  have HS' := HS
  obtain ⟨Hsb, Hst, Hse, HsT, HsV, Hbc, Hwc, Hcc, Hsnap, Hsb2⟩ := HS'
  -- the last index fits a word with room: its receipt (`readyFits`)
  imod lastRec_receipt γ.raft _ $$ Hlr with Hrc
  ihave %Hrcl := preceipt_lt _ $$ Hrc
  iunfold EtcdGrove.readyFits at Hfits
  icases Hfits with %Hfit
  have HlenFp : (fp.length : Int) = uint.Z σ.base.index' := Hfp.1
  have Hlast : uint.Z σ.base.index' + (σ.ents.length : Int) + 1 < 2 ^ 64 := by
    unfold Cluster.bootLen at Hfit Hboot
    simp only [restartP, plogLastIndexZ] at Hrcl
    rw [← Hse] at Hrcl
    have := uint_nat_eq σ.hs.Commit'
    unfold StorContents.commit at Hboot
    omega
  have Hca : committedAfter σ.base σ.hs = σ.hs.Commit' := committedAfter_restart σ Hbc
  -- the stored commit within the stored log
  have HcL : uint.Z σ.hs.Commit' ≤ uint.Z σ.base.index' + (σ.ents.length : Int) := by
    have := HlogOk.2.2
    simp only [restartP, plogLastIndexZ] at this
    rw [← Hse] at this; exact this
  -- the committed log up to the stored commit, and its terms (the attach record)
  have HFlen : (fp ++ σ.ents).length = σ.b + σ.ents.length := by
    rw [List.length_append]; unfold StorContents.b; have := uint_nat_eq σ.base.index'; omega
  have HcF : σ.commit ≤ (fp ++ σ.ents).length := by
    rw [HFlen]; unfold StorContents.commit StorContents.b
    have := uint_nat_eq σ.base.index'; have := uint_nat_eq σ.hs.Commit'; omega
  ihave #HcmtF : isCommitted γ.raft ((fp ++ σ.ents).take σ.commit) $$ []
  · iExactEq Hcmt
    unfold cprefix; simp only [restartP]; rw [← Hse, toNat_uZ]; rfl
  -- the storage's frame and reads
  iunfold restartStorage at Hrs
  icases Hrs with ⟨%i, %Rb, %f, %Hi, %Hf, HRb, #HFI, #HLI, #HIS⟩
  cases Hi
  -- raft's storage names: the floor and the snapshot hand-out at the base, no term certified yet,
  -- the contract's `SV` and the received snapshots' certificate; the attach record: the applied
  -- bound `max b A`, the stored commit and the committed log's terms up to it
  imod mono_nat_own_alloc (GF := GF) (uint.nat σ.base.index') with ⟨%ga, Hga, #Hgalb⟩
  imod mono_nat_own_alloc (GF := GF) σ.b with ⟨%gg, Hgg, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := w64) with ⟨%gdd, Hgd⟩
  imod saved_pred_alloc (EtcdGrove.snapshotValid (GF := GF) γ) DFrac.discard trivial
    with ⟨%gsv, #Hsv⟩
  imod saved_pred_alloc (raftSnapCertD (GF := GF) γ.raft) DFrac.discard trivial with ⟨%gk, #Hgk⟩
  let sn : StorNames :=
    { ga := ga, gg := gg, gsv := gsv, gd := gdd, gk := gk, a0 := max σ.b (uint.nat cv.Applied'),
      c0 := σ.commit, ct := restartCt (fp ++ σ.ents) σ.commit }
  let σv : StorState :=
    { prev := σ.base, ents := σ.ents, pend := [], fl := σ.base.index', fr := f,
      sg := σ.b, dt := ∅ }
  ihave #Hct : ctCommitted (GF := GF) γ.raft sn $$ []
  · unfold ctCommitted
    iexists (fp ++ σ.ents).take σ.commit
    iframe HcmtF
    ipureintro
    intro i t hm hi
    obtain ⟨h1, h2, h3⟩ := restartCt_mem HcF hm
    refine ⟨h1, ?_⟩
    rw [List.getElem?_take, ite_eq_left (by omega)]; exact h3
  ihave #Hlink := certLink_make γ N HU sn $$ Hci Hsv Hgk Hct
  ihave HA : storAuths (GF := GF) sn.unrec σv $$ [Hga Hgg Hgd]
  · ihave #Hcu := storCaught_unrec (GF := GF) sn 1 _ $$ Hga
    unfold storAuths
    iframe Hcu
    isplitl [Hga]
    · iExactEq Hga; rfl
    isplitl [Hgg]
    · iExactEq Hgg; rfl
    iExactEq Hgd; rfl
  ihave #Hga0 := monoNatLbOwn_le (GF := GF) (γ := ga) 0 (Nat.zero_le _) $$ Hgalb
  -- `NewRawNode`'s premises
  have HAR : AttachRec sn σ.base σ.ents (uint.nat (committedAfter σ.base σ.hs))
      (max (uint.nat σ.base.index') (uint.nat cv.Applied')) := by
    rw [Hca]
    refine ⟨rfl, rfl, fun i t hm _ => ?_, fun i h1 h2 => restartCt_complete HcF h1 h2⟩
    obtain ⟨h1, h2, h3⟩ := restartCt_mem HcF hm
    refine ⟨h1, fun hb => termAt_of_full Hfp hb h1 ?_ h3⟩
    unfold StorContents.commit at h2
    have := uint_nat_eq σ.hs.Commit'; omega
  have Hvalm : memValid m := by
    unfold EtcdGrove.Membership.Valid memValid at Hval; exact Hval
  obtain ⟨HcsWf, Hrestore⟩ := restore_of_confStateIs csm m Hcs Hvalm Hres
  have HcsOk : ConfStateOk csm := by
    obtain ⟨hV, hVO, hL, hLN, hAL⟩ := Hcs
    refine ⟨.inl HcsWf, hV.nodup_iff.2 (GMap.NoDup_elements _),
      hVO.nodup_iff.2 (GMap.NoDup_elements _), hL.nodup_iff.2 (GMap.NoDup_elements _),
      hLN.nodup_iff.2 (GMap.NoDup_elements _), fun h => ?_⟩
    rw [hAL]
    have hO : m.votersOutgoing = ∅ := by rw [← cc_listToSet_of_perm hVO, h]; rfl
    exact (Hvalm.1.1.2.2.2 hO).2
  have HbcZ : uint.Z σ.base.index' ≤ uint.Z σ.hs.Commit' := by
    unfold StorContents.b StorContents.commit at Hbc
    have := uint_nat_eq σ.base.index'; have := uint_nat_eq σ.hs.Commit'; omega
  have Happ' : cv.Applied' = W64 0 ∨ uint.Z σ.base.index' ≤ uint.Z cv.Applied' ∧
      uint.Z cv.Applied' ≤ uint.Z (committedAfter σ.base σ.hs) := by
    rw [Hca]
    rcases Happ with h | ⟨h1, h2⟩
    · left; apply BitVec.eq_of_toNat_eq; exact h
    · right
      simp only [StorContents.b, StorContents.commit] at h1 h2
      have := uint_nat_eq σ.base.index'; have := uint_nat_eq σ.hs.Commit'
      have := uint_nat_eq cv.Applied'; omega
  wp_apply wp_NewRawNode c cv lok si sn σv σ.hs csm iprop(Rb ∗ storAuths sn.unrec σv)
    iprop(∃ K, storKeyNames K sn ∗ F K) (stOf m) H1 H2 H3 H4 H5 H6 H7 H8 H9
    (by show LogIndicesOk σ.base σ.ents; rw [Hse]; exact Hwf) rfl Hf.1 (by rw [Hca]; exact Hf.2) (Int.le_refl _) (Nat.le_refl _)
    rfl Hlast HAR (.inr ⟨HbcZ, HcL⟩) Happ' Hrestore Hcsl HcsOk
    $$ [Hc HRb HA]
    as %rn %err ⟨⟨%K, #HKn, HFK⟩, %s, Hrn, %Herr, %Hsn2⟩
  · iframe Hc Hlg
    isplitl [HRb HA]
    · iframe HRb HA
    isplitr
    · iintro !> %Φ' !> ⟨HRb, HA⟩ HΦ'
      iapply HFI $$ HRb [HA HΦ']
      inext; iintro HRb
      ihave H := HΦ' $$ [HRb HA]
      · iframe HRb HA
      iExactEq H; rfl
    isplitr
    · iintro !> %Φ' !> ⟨HRb, HA⟩ HΦ'
      iapply HLI $$ HRb [HA HΦ']
      inext; iintro HRb
      ihave H := HΦ' $$ [HRb HA]
      · iframe HRb HA
      iExactEq H; rfl
    iintro !> %Φ' !> ⟨HRb, HA⟩ HΦ'
    iapply HIS $$ HRb [HA HΦ']
    inext
    iintro %hp %cs %al ⟨Hhs, Hcs, Hk⟩
    iapply HΦ'
    iframe Hhs Hcs
    -- the attach: a fresh key recording raft's storage names
    imod dghostVar_alloc (GF := GF)
      ((sn.ga, sn.gg, sn.gsv, sn.gd, sn.gk, sn.a0, sn.c0, sn.ct) :
        Nat × Nat × Nat × Nat × Nat × Nat × Nat × List (Nat × w64)) with ⟨%K, HK⟩
    imod dghostVar_persist K 1 _ $$ HK with #HK
    ihave #HKn : storKeyNames (GF := GF) K sn $$ []
    · unfold storKeyNames; iexact HK
    imod api_committed_lb γ N ⊤ CoPset.subseteq_top ((fp ++ σ.ents).take σ.commit) $$ Hci HcmtF
      with ⟨HlbC, %HidxC⟩
    imod Hk $$ %K [] [HlbC] with ⟨Hst, Hsh, HFK⟩
    · iunfold EtcdGrove.nodeAppliedLb
      unfold nodeAppliedLbU
      iright
      iexists sn
      iframe HKn
      iright; iright
      ipureintro; exact Nat.le_refl _
    · iunfold EtcdGrove.nodeCommitLb
      unfold nodeCommitLbU
      iright
      iexists sn, strip ((fp ++ σ.ents).take σ.commit)
      iframe HKn HlbC
      isplitr
      · ipureintro; rw [strip, List.length_map, List.length_take]; omega
      rw [toEntries_strip _ 0 (fun k e h => by rw [HidxC k e h]; push_cast; omega)]
      iapply BigSepL.bigSepL_forall_elim
      iintro %j %e %Hj
      unfold raftDL
      iright; iright
      ipureintro
      have hj := (List.getElem?_eq_some_iff.1 Hj).1
      rw [List.length_take] at hj
      refine ⟨by show j + 1 ≤ σ.commit; omega, ?_⟩
      show (j + 1, e.Term') ∈ restartCt (fp ++ σ.ents) σ.commit
      unfold restartCt
      rw [List.mem_map]
      refine ⟨j, by rw [List.mem_range]; omega, ?_⟩
      rw [List.getElem?_take, ite_eq_left (by omega)] at Hj
      rw [Hj]; rfl
    imodintro
    isplitl [Hst]
    · iapply isStorage_of_V
      unfold isStorageV
      iexists EtcdGrove.snapshotValid (GF := GF) γ, EtcdGrove.storBnd (GF := GF) γ K,
        EtcdGrove.nodeCommitLb (GF := GF) γ K
      isplitl [Hst]
      · iunfold EtcdGrove.isStorage at Hst
        iexact Hst
      isplitr; · iexact Hsv
      isplitr
      · iintro !> %sv #H
        imodintro; iexact H
      isplitr
      · iintro !> %c' Hb
        iapply storBnd_raftBnd γ K sn c' $$ HKn Hga0 Hb
      · iintro !> %sv Hv Hd
        imodintro
        iapply storDL_raftDL γ K sn sv $$ HKn Hv Hd
    isplitl [Hsh HA]
    · iunfold storHolds at Hsh
      icases Hsh with ⟨%e0, %He0, #Hc0, #Hl0, #Hlf, Hown, Hend⟩
      unfold ownStorage
      iexists e0
      isplitr
      · iExactEq Hc0; rfl
      isplitr
      · ihave H := (StorageModel.storLog_app (GF := GF) (interface.ok si) σ.b DFrac.discard [e0]
          (σ.ents.take (f - σ.b))).2 $$ [Hl0 Hlf]
        · iframe Hl0; iExactEq Hlf; rfl
        iExactEq H; rfl
      isplitl [Hown]
      · iExactEq Hown
        simp only [σv, StorState.kOut, List.head?_nil, StorContents.b]
        rw [show uint.nat σ.base.index' + 1 + σ.ents.length - uint.nat σ.base.index' - 1 =
          σ.ents.length by omega, List.take_length]
      isplitl [Hend]
      · iright; iExactEq Hend; simp only [σv, StorContents.last, StorContents.b]; congr 1; omega
      iframe HA
      ipureintro
      refine ⟨He0, Hf.1, ?_, by simp [σv, StorState.kOut], Nat.le_refl _⟩
      simp only [σv, StorState.kOut, List.head?_nil]
      unfold StorContents.commit StorContents.b at Hf
      have := uint_nat_eq σ.base.index'; have := uint_nat_eq σ.hs.Commit'
      omega
    iexists K
    iframe HKn HFK
  subst Herr
  obtain ⟨Hlsn, Hgsn⟩ := Hsn2
  -- the committed log handed out at the start: up to `max b A`
  have Ha0c : max σ.b (uint.nat cv.Applied') ≤ σ.commit := by omega
  have Ha2 : a ≤ σ.commit := Hae ▸ Ha0c
  have HDlen : ((fp ++ σ.ents).take (max σ.b (uint.nat cv.Applied'))).length =
      max σ.b (uint.nat cv.Applied') := by
    rw [List.length_take]; omega
  ihave #HcD : isCommitted γ.raft ((fp ++ σ.ents).take (max σ.b (uint.nat cv.Applied'))) $$ []
  · iapply isCommitted_mono γ.raft _ _ (List.take_prefix_take_left Ha0c) $$ HcmtF
  -- the restarted protocol state is the state `newRaft` restored
  have HrP : restartPState σ.hs σv = restartP S σ.base σ.hs.Commit' := by
    unfold restartPState restartP; simp only [σv]; rw [HsT, HsV, Hca, ← Hse]
  -- the configuration point's fold, over the restarted full log
  imod api_lb_committed γ N ⊤ CoPset.subseteq_top lA $$ Hci HlbA with ⟨%DA, %HDA, #HcDA⟩
  icases isCommitted_agree γ.raft DA ((fp ++ σ.ents).take σ.commit) $$ HcDA HcmtF with %HpA
  have HtakeA : strip ((fp ++ σ.ents).take a) = lA.take a := by
    rw [← HDA]
    have hDAl : a ≤ DA.length := by rw [← HDA, strip, List.length_map] at HkA; exact HkA
    have hFl : a ≤ ((fp ++ σ.ents).take σ.commit).length := by rw [List.length_take]; omega
    have : (fp ++ σ.ents).take a = DA.take a := by
      rw [show (fp ++ σ.ents).take a = ((fp ++ σ.ents).take σ.commit).take a by
        rw [List.take_take, Nat.min_eq_left Ha2]]
      rcases HpA with ⟨t, ht⟩ | ⟨t, ht⟩
      · rw [← ht, List.take_append_of_le_length hDAl]
      · rw [← ht, List.take_append_of_le_length hFl]
    rw [this, strip, strip, List.map_take]
  -- the node, closed: `rawNodeAt` with the restarted ghost state in the cluster's dynamic mode
  iunfold rawNodeAt at Hrn
  icases Hrn with ⟨%rnv, %sv, %hprev, Hrn⟩
  iNamed Hrn
  obtain ⟨Ht, Hv, Hr, Ho, Hst0, Hpd⟩ := Hterm
  obtain ⟨Hlp, Hse0, Hue, Hsd, Hcm, Hap, Hapg, Hun, Hsn0, Hsg, Hdtk⟩ := Hlog
  -- the term ceiling raised to the term, which the budget covers (`termLB`)
  have Htc0 : uint.Z s.gh.tc ≤ uint.Z S.term := by
    rw [Hgh]; exact uint_Z_nonneg _
  ihave Hphys := ownRaftPhysC_raise_tc _ rnv.raft' cv.ID' s S.term Htc0 $$ Hphys
  icases ownRaftPhysC_sdr _ rnv.raft' cv.ID' _ $$ Hphys with ⟨#Hsd0, Hphys⟩
  icases ownRaftPhysC_log_same _ rnv.raft' cv.ID' _ $$ Hphys with ⟨HL, Hback0⟩
  icases ownRaftLog_fl _ _ $$ HL with ⟨%Hflk, HL⟩
  icases ownRaftLog_caught _ _ $$ HL with ⟨#Hcu, HL⟩
  ihave Hphys := Hback0 $$ HL
  ihave #Hcu2 : storCaught (GF := GF) sn $$ []
  · rw [← Hlsn]; iexact Hcu
  -- the applied index the node starts at: `max b A`
  have Happn : uint.nat s.logst.applying = max σ.b (uint.nat cv.Applied') := by
    rw [Hapg]; unfold w64Max StorContents.b
    simp only [σv]
    by_cases hA : cv.Applied' = W64 0
    · rw [if_pos hA, hA]
      have : uint.nat (W64 0) = 0 := rfl
      simp
    · rw [if_neg hA]
      have := uint_nat_eq σ.base.index'; have := uint_nat_eq cv.Applied'
      split <;> omega
  have HtoP : toPState s = restartP S σ.base σ.hs.Commit' := by rw [← HrP]; exact Hrel.1
  have Hfp' : FullOk σ.base fp := Hfp
  -- the restarted node's dynamic invariant (`RInv`), at the configuration point `a`
  have HfoldA : cfgFold (effDec noDec MA) (stOf c0m) ((fp ++ σ.ents).take a) = some (stOf m) := by
    rw [cfgFold_decs MA c0m HmA.valid, HtakeA, HfA]; rfl
  let s1 : NState := { s with gh := { s.gh with tc := S.term } }
  let g : RGh := ⟨a, stOf m, fp, MA⟩
  have HtoP1 : toPState s1 = restartP S σ.base σ.hs.Commit' := HtoP
  have Hrole1 : (restartP S σ.base σ.hs.Commit').role = .follower := rfl
  have HRI : RInv (effDec noDec MA) (stOf c0m) (rOf s1 g) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show FullOk (toPState s1).base fp; rw [HtoP1]; exact Hfp'
    · show uint.Z (toPState s1).base.index' ≤ uint.Z (toPState s1).commit; rw [HtoP1]; exact HbcZ
    · show uint.Z (toPState s1).commit ≤ plogLastIndexZ (toPState s1).base (toPState s1).log
      rw [HtoP1]; simp only [restartP, plogLastIndexZ]; rw [← Hse]; exact HcL
    · show uint.nat s.logst.applied ≤ a; rw [Hap, Happn]; omega
    · show a ≤ uint.nat (toPState s1).commit; rw [HtoP1]; exact Ha2
    · intro _
      show uint.Z (toPState s1).base.index' ≤ uint.Z s.logst.applied
      rw [HtoP1, Hap]
      have := uint_nat_eq s.logst.applying; have := uint_nat_eq σ.base.index'
      simp only [restartP]; unfold StorContents.b at Happn; omega
    · intro h; change (toPState s1).role = .leader at h; rw [HtoP1, Hrole1] at h; cases h
    · show cfgFold (effDec noDec MA) (stOf c0m) ((fp ++ (toPState s1).log).take a) = some (stOf m)
      rw [HtoP1]; simp only [restartP]; rw [← Hse]; exact HfoldA
    · show ConfI1 (fp ++ (toPState s1).log) (uint.nat (toPState s1).commit)
      rw [HtoP1]; simp only [restartP]; exact HI1 rfl
    · intro h; change (toPState s1).role = .leader at h; rw [HtoP1, Hrole1] at h; cases h
    · intro h; change (toPState s1).role = .candidate at h; rw [HtoP1, Hrole1] at h; cases h
  have Hns : γ.raft.reNoSnap = false := HmA.1.2.2.2.1
  ihave Hghost : ownStepGhost γ.raft (RNMode.toG (γ.mode inferInstance) g) (stOf m).cfg cv.ID' s1
      $$ [Hg]
  · rw [Hmd]
    simp only [RNMode.toG]
    iapply (ownStepGhost_dyn γ.raft noDec (stOf c0m) h0 g (stOf m).cfg cv.ID' s1).2
    isplitr
    · ipureintro
      refine ⟨HD, rfl, ?_⟩
      unfold NsLink
      show s.gh.ns = _
      rw [Hgh, Hns]
    isplitr; · iexact HMA
    isplitl [Hg]
    · unfold ownRaftGhostR
      simp only [rOf.proj_p, rOf.proj_fp]
      rw [HtoP1]
      iframe Hg Hfr
      ipureintro; exact HRI
    isplitr
    · rw [show s1.gh.sn = sn from Hgsn]; iexact Hlink
    isplitr
    · iapply leadW_none γ.raft cv.ID' _ (by rw [HtoP1]; rfl)
    unfold xfW
    rw [show s1.gh.xw = ∅ by show s.gh.xw = ∅; rw [Hgh]]
    iapply BigSepM.bigSepM_empty.2; iempintro
  -- the node's record: the committed log up to `max b A` handed out, the stored hard state, the
  -- durable state `S`, a follower; the term ceiling at the term; at the configuration point
  let rs0 : RNState :=
    { delivered := (fp ++ σ.ents).take (max σ.b (uint.nat cv.Applied')), unpersisted := [],
      steps := [], term := σ.hs.Term', storage := interface.ok si, sn := sn, tc := S.term,
      mode := γ.mode inferInstance, cfg := stOf m, capplied := a, phs := hprev, dur := S,
      role := StateFollower }
  have Hdtk1 : s.logst.dtk = σ.commit := by rw [Hdtk, Hca]; rfl
  ihave #Hphw : phsWit γ.raft hprev $$ []
  · unfold phsWit
    iright
    rw [Hhz, Hca]
    iExactEq Hcw
    simp only [restartP]; rw [HsT]
  ihave #Hph : prevHS γ.raft rnv.prevHardSt' hprev rs0.phs $$ []
  · iapply prevHS_intro γ.raft _ hprev $$ Hhard Hphw
  ihave #Hdurt : durTie γ.raft rs0 s1 $$ []
  · unfold durTie
    iintro !> %_ %fp' %Hfp2 #Hr2
    have Hfp2' : FullOk σ.base fp' := by
      have : s1.logst.prev = σ.base := Hlp
      rw [this] at Hfp2; exact Hfp2
    ihave %H := HI1r $$ %fp' %Hfp2' Hr2
    ipureintro
    refine ⟨?_, ?_⟩
    · show DurFull S (fp' ++ s.logst.stored)
      rw [Hsd]; show DurFull S (fp' ++ σ.ents); rw [Hse]; exact H.1
    · show uint.Z S.base.index' ≤ uint.Z s.logst.prev.index'
      rw [Hlp]; exact Hsb
  -- (2026-11-02, stage II (t): stage II (m)'s `PhsOk`) `prevHardSt`'s record the node's hard state
  -- (the stored one), the lower bound zero, the commit below the unstable entries' start, no snapshot
  have HphsR : PhsOk rs0 s1 := by
    have Hh : hsOf s1 = hprev := by
      show HardStateM.mk s.term s.vote s.logst.committed = hprev
      rw [Hhz, Ht, Hv, Hcm]
    refine ⟨by show HsLe hprev (hsOf s1); rw [Hh]; exact HsLe.refl _, HsLe.zero _, fun _ => ?_,
      fun sid hs _ => by change s.logst.snap = some sid at hs; rw [Hsn0] at hs; cases hs⟩
    show uint.Z hprev.Commit' < uint.Z s.logst.inprogress
    rw [Hhz]
    show uint.Z (committedAfter σ.base σ.hs) < _
    rw [Hca, Hsvr.2]
    simp only [σv]
    omega
  ihave Hrn : ownRawNode γ.raft rn cv.ID' rs0 $$ [Hrn Hphys Hghost Hsteps Hsteps_cap]
  · iapply ownRawNode_intro γ.raft rn cv.ID' rs0 s1 (stOf m).cfg fp (ds := MA) rnv sv hprev []
      Hrel.2 (fun h => by simp only [rs0] at h; rw [Hmd] at h; cases h) Hasync
      (by show ((fp ++ σ.ents).take _).length = _; rw [HDlen, toNat_uZ]; exact Happn.symm)
      Hun.symm (fun _ => Hsn0) trivial Ht.symm ⟨Hsg.symm, Hlsn.symm⟩
      ⟨fun _ => preGuardF_fol Hr, rfl, by show uint.Z s.term ≤ uint.Z S.term; rw [Ht, HsT]; exact Int.le_refl _,
        fun h => absurd (Hr.symm.trans h) (by decide), fun _ => Hr⟩
      (by show 0 = s.gh.outlb; rw [Hgh]) (by show false = s.gh.unst; rw [Hgh])
      (uint_Z_nonneg _)
      ⟨fun _ => by rw [Hap]; exact Hflk.1, fun h => absurd h (by rw [Hap]; exact Int.lt_irrefl _)⟩
      ⟨by show s.gh.slent = false; rw [Hgh],
        fun _ => ⟨by show s.gh.snp = none; rw [Hgh], fun _ _ _ _ h => by cases h⟩,
        fun l h => by cases h⟩
      ⟨by show ((fp ++ σ.ents).take _).length ≤ s.logst.dtk; rw [HDlen, Hdtk1]; exact Ha0c,
        fun i hi1 hi2 => by
          change ((fp ++ σ.ents).take _).length < i at hi1
          change i ≤ s.logst.dtk at hi2
          rw [HDlen] at hi1; rw [Hdtk1] at hi2
          obtain ⟨t, ht, -⟩ := restartCt_complete HcF (by omega) hi2
          exact ⟨hi2, t, ht⟩⟩
      Hsvr.1.symm HphsR
      $$ Hrn Hphys Hghost [] Hsoft Hph Hsteps Hsteps_cap [] HcD [] [] [] Hdurt
    · iunfold sdrOk; iexists _; iexact Hsd0
    · iapply pendList_nil
    · iapply ackInv_none; intro _ _ _ _ h; cases h
    · iapply loanCom_none γ.raft rfl
    · rw [show s1.logst.snap = none from Hsn0]; iapply snapLocOk_none
  -- the driver's view of the configuration is the node's: from the applied index it starts at
  subst Hae
  have Hhp : hprev = σ.hs := by rw [Hhz, Hca]
  -- raft's certified terms of the committed log handed out (the attach record's)
  ihave #HdK : dlvKeys (GF := GF) sn ((fp ++ σ.ents).take (max σ.b (uint.nat cv.Applied'))) $$ []
  · unfold dlvKeys dlvKeysAt
    iapply BigSepL.bigSepL_forall_elim
    iintro %j %e %Hj
    iunfold storCaught at Hcu2
    icases Hcu2 with ⟨-, #Hcu'⟩
    have hj := (List.getElem?_eq_some_iff.1 Hj).1
    rw [HDlen] at hj
    iapply Hcu' $$ %_ %_ %(And.intro (show 0 + j + 1 ≤ σ.commit by omega) (by
      show (0 + j + 1, e.Term') ∈ restartCt (fp ++ σ.ents) σ.commit
      unfold restartCt
      rw [List.mem_map]
      refine ⟨j, by rw [List.mem_range]; omega, ?_⟩
      rw [List.getElem?_take, ite_eq_left (by omega)] at Hj
      rw [Hj]; simp))
  -- the API's committed log handed out (two copies: `isCommittedLogLb`'s persistence is internal)
  imod api_committed_lb γ N ⊤ CoPset.subseteq_top
    ((fp ++ σ.ents).take (max σ.b (uint.nat cv.Applied'))) $$ Hci HcD with ⟨HlbD, %HidxD⟩
  imod api_committed_lb γ N ⊤ CoPset.subseteq_top
    ((fp ++ σ.ents).take (max σ.b (uint.nat cv.Applied'))) $$ Hci HcD with ⟨HlbD2, -⟩
  have Hlen' : (((strip ((fp ++ σ.ents).take (max σ.b (uint.nat cv.Applied')))).length : Nat) : Int)
      ≤ uint.Z σ.hs.Commit' := by
    simp only [strip, List.length_map]; rw [HDlen]
    unfold StorContents.commit at Ha0c; have := uint_nat_eq σ.hs.Commit'; omega
  ihave #Hphw2 : phsWit (GF := GF) γ.raft σ.hs $$ []
  · rw [← Hhp]; iexact Hphw
  ihave #Hhw := hsWit_of_phsWit γ.raft σ.hs _ Hlen' $$ Hphw2
  imod hsCommitted_of_raft γ N ⊤ CoPset.subseteq_top σ.hs _ $$ Hci Hhw with HhsC
  have HdynOk : ∀ γn : NodeNames, NodeOk γ γn → γn.mode.isDyn = true := fun γn h => by
    rw [h.2.2.2, Hmd]; rfl
  wp_auto
  wp_apply wp_newNode rn as %nv ⟨%Hnvrn, Hchans⟩
  -- the node's configuration names, `live`, the durable state and role, the last batch's maps
  imod mono_list_own_alloc (GF := GF) ((fp ++ σ.ents).take (max σ.b (uint.nat cv.Applied')))
    with ⟨%gdlm, Hdlm, #Hdlb⟩
  imod dghostVar_alloc (GF := GF) ((max σ.b (uint.nat cv.Applied')), stOf m) with ⟨%gcap, Hcap⟩
  imod dghostVar_alloc (GF := GF) ((max σ.b (uint.nat cv.Applied')), stOf m) with ⟨%gccq, Hccq⟩
  imod mono_nat_own_alloc (GF := GF) (max σ.b (uint.nat cv.Applied')) with ⟨%gcam, Hcam, #Hcamlb⟩
  imod dghostVar_alloc (GF := GF) false with ⟨%glive, Hlive⟩
  imod dghostVar_alloc (GF := GF) ((S, StateFollower) : RaftState × StateType) with ⟨%gdur, Hdur⟩
  imod dghostVar_alloc (GF := GF)
    ((DurMaps.empty, (S, StateFollower)) : DurMaps × (RaftState × StateType)) with ⟨%gbw, Hbw⟩
  -- the node's ghost state
  imod dghostVar_alloc (((fp ++ σ.ents).take (max σ.b (uint.nat cv.Applied')), σ.hs) :
    List EntryM × HardStateM) with ⟨%γdlv, Hdlv⟩
  icases dghostVar_halves _ _ $$ Hdlv with ⟨Hdlv1, Hdlv2⟩
  imod dghostVar_alloc (([], [], [], hsZero, none) : List EntryM × List EntryM ×
    List EntryM × HardStateM × Option SnapLoan) with ⟨%γrof, Hrof⟩
  icases dghostVar_halves _ _ $$ Hrof with ⟨Hrof1, Hrof2⟩
  icases dghostVar_halves _ _ $$ Hcap with ⟨Hcap1, Hcap2⟩
  icases dghostVar_halves _ _ $$ Hccq with ⟨Hccq1, Hccq2⟩
  imod dghostVar_alloc (((none, none) : AdvReq)) with ⟨%γreq, Hreq⟩
  icases dghostVar_halves _ _ $$ Hreq with ⟨Hreq1, Hreq2⟩
  icases dghostVar_halves _ _ $$ Hlive with ⟨Hlive1, Hlive2⟩
  icases dghostVar_halves _ _ $$ Hdur with ⟨Hdur1, Hdur2⟩
  ihave Hgen : slotLive (GF := GF) γ.raft cv.ID' ((1 : Qp).half + (1 : Qp).half) gen $$ [Hgen]
  · rw [Qp.half_add_half]; iexact Hgen
  icases ((slotLive_fractional (GF := GF) γ.raft cv.ID' gen).fractional (1 : Qp).half
    (1 : Qp).half).1 $$ Hgen with ⟨Hgen1, Hgen2⟩
  unfold newNodeChans
  icases Hchans with ⟨%γp, %γr, %γc, %γcs, %γrd, %γa, %γt, %γd, %γs, %γst, #Hcp, Hop, #Hcr, Hor,
    #Hcc, Hoc, #Hccs, Hocs, #Hcrd, Hord, #Hca, Hoa, #Hct, Hot, #Hcd, Hod, #Hcs, Hos, #Hcst, Host⟩
  let γn : NodeNames := {
                          raft := γ.raft
                          id := cv.ID'
                          bud := γ.bud
                          stor := interface.ok si
                          propc := γp
                          recvc := γr
                          confc := γc
                          confstatec := γcs
                          readyc := γrd
                          advancec := γa
                          tick := γt
                          done := γd
                          stop := γs
                          status := γst
                          dlv := γdlv
                          rof := γrof
                          mode := γ.mode inferInstance
                          dlm := gdlm
                          cap := gcap
                          ccq := gccq
                          cam := gcam
                          req := γreq
                          sn := sn
                          live := glive
                          gen := gen
                          dur := gdur
                          bw := gbw }
  have Hnok : NodeOk γ γn := ⟨rfl, rfl, Hsl, rfl⟩
  have Hdy : γn.mode.isDyn = true := HdynOk γn Hnok
  -- the node's table entry, while its struct is owned whole
  imod nodeTab_insert γ N n_ptr nv (cfgNamesOf γn) $$ Htab n with ⟨#Hnp, #Hte⟩
  haveI := nodeTabOk_persistent (GF := GF) γ n_ptr γn
  ihave #Htb : nodeTabOk (GF := GF) γ n_ptr γn $$ []
  · unfold nodeTabOk; iexact Hte
  ihave Hlive1 : nodeLiveRaw (GF := GF) γn 1 $$ [Hlive1 Hgen1]
  · unfold nodeLiveRaw; iframe Hlive1 Hgen1
  ihave Hlive2 : nodeLiveRaw (GF := GF) γn 1 $$ [Hlive2 Hgen2]
  · unfold nodeLiveRaw; iframe Hlive2 Hgen2
  imod start_handshake nv.propc' (propP γn) iprop(True) γp $$ Hcp Hop with #Hhp
  imod start_handshake nv.recvc' (netP γn cv.ID') iprop(True) γr $$ Hcr Hor with #Hhr
  imod start_handshake nv.confc' (confcP γn) iprop(True) γc $$ Hcc Hoc with #Hhc
  imod start_handshake nv.confstatec' (confstateP γn) iprop(True) γcs $$ Hccs Hocs with #Hhcs
  imod start_handshake nv.readyc' (readyP γn) iprop(True) γrd $$ Hcrd Hord with #Hhrd
  imod adv_start γn nv.rn' cv.ID' nv.advancec' $$ Hca Hoa with #Hha
  imod alloc_broadcast_chan (nodeStoppedRaw γn) γd nv.done' $$ Hcd Hod with Hpend
  icases ownBroadcastChan_pending_unknown nv.done' γd (nodeStoppedRaw γn) $$ Hpend with ⟨Hpend, #Hhd⟩
  imod start_handshake nv.stop' (fun (_ : Unit) => dghostVar γn.live (DFrac.own (1 : Qp).half) false)
    (stopAns γn cv.ID') γs $$ Hcs Hos with #Hhs
  imod start_handshake nv.status' statusChP iprop(True) γst $$ Hcst Host with #Hhst
  imod tickCred_zero γ.bud with Hcr0
  imod inv_alloc tickN ⊤ (tickInv γn) $$ [Hot Hcr0] with #Htickinv
  · inext
    unfold tickInv
    iexists []
    iframe
  icases ownRawNode_shared γ.raft rn cv.ID' _ $$ Hrn with ⟨%r, %lok', #Hrr, #Hrid, #Hrlg, #Hlg', Hrn⟩
  ihave #Hnode : isNodeChan γn cv.ID' n_ptr $$ []
  · unfold isNodeChan
    iexists nv, r, lok'
    simp only [named]
    rw [Hnvrn]
    iframe #
    ipureintro; rfl
  -- `go n.run()`
  wp_apply wp_fork $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam Hpend Hlive1 Hdur1 Hbw Hfree]
  · wp_apply wp_node_run γn cv.ID' n_ptr $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam Hpend Hlive1
      Hdur1 Hbw Hfree]
    · iframe Hnode
      unfold runPre
      iexists nv, _, (([], [], [], hsZero, none) : List EntryM × List EntryM × List EntryM ×
        HardStateM × Option SnapLoan)
      rw [Hnvrn]
      iframe Hnp Hrn Hrof1 Hrof2
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      isplitl [Hdlv1]
      · iExactEq Hdlv1; rw [show rs0.phs = σ.hs from Hhp]
      iframe HtS
      iframe Hpend Hlive1 Hdur1 Hfree
      isplitr [Hbw]
      · unfold runCfg
        isplitr
        · ipureintro
          refine ⟨rfl, ?_, rfl, fun _ h => absurd h (by simp [rs0]), rfl⟩
          show (max σ.b (uint.nat cv.Applied')) ≤ ((fp ++ σ.ents).take _).length
          rw [HDlen]; omega
        isplitl [Hdlm]
        · iExactEq Hdlm; rfl
        isplitr
        · iExactEq HdK; rfl
        iexists (max σ.b (uint.nat cv.Applied'))
        iframe Hcap1 Hcam
        isplitr
        · ipureintro; exact Nat.le_refl _
        iapply undecFree_empty
      iexists _; iexact Hbw
    itrivial
  iapply HΦ
  iexists n_ptr, S, strip ((fp ++ σ.ents).take (max σ.b (uint.nat cv.Applied'))), K
  isplitr
  · ipureintro; rfl
  iframe HQ HFK
  isplitr
  · iunfold EtcdGrove.isNode
    unfold isNode
    iexists γn
    iframe Hnode Htb Hci Hpool
    ipureintro; exact ⟨Hnok, HU⟩
  isplitl [HlbD]
  · iunfold EtcdGrove.isCommittedLogLb; iexact HlbD
  isplitr
  · ipureintro; simp only [strip, List.length_map]; exact HDlen
  isplitr
  · ipureintro
    rw [toEntries_strip _ 0 (fun k e h => by rw [HidxD k e h]; simp)]
    simp only [strip, List.length_map, HDlen]
    have hfl : fp.length = σ.b := by
      unfold StorContents.b; have := uint_nat_eq σ.base.index'; omega
    rw [List.drop_take, ← hfl, List.drop_left]
  isplitl [Hdlv2 Hreq1 Hreq2 Hdur2 HlbD2 HhsC]
  · iunfold EtcdGrove.nodeDriver
    unfold nodeDriver
    iexists γn, cv.ID', (fp ++ σ.ents).take (max σ.b (uint.nat cv.Applied'))
    isplitr
    · ipureintro; exact ⟨Hnok, rfl, rfl⟩
    isplitr; · iexact Hci
    isplitl [HlbD2]; · iexact HlbD2
    isplitr; · ipureintro; exact Hdy
    isplitr; · iexact Htb
    isplitl [HhsC]; · iexact HhsC
    isplitr; · iexact HKn
    ileft
    isplitr
    · ipureintro; rfl
    iframe Hdur2
    unfold nodeDriverChan dlvLb
    iframe Hnode Hdlv2 Hdlb HdK
    iexists _
    iframe Hreq1 Hreq2
  isplitl [Hcap2 Hccq1 Hccq2]
  · iunfold EtcdGrove.nodeConfig
    isplitl [Hcap2 Hccq1 Hccq2]
    · unfold nodeConfig
      iexists γn, cv.ID'
      iframe Hnode Htb
      isplitr
      · ipureintro
        exact ⟨Hnok, Hdy, Hvalm.2⟩
      unfold nodeCfg
      iframe Hcap2 Hcamlb
      iexists _
      iframe Hccq1 Hccq2
    iexact Hconf
  iunfold EtcdGrove.nodeRunning
  unfold nodeRunning
  iexists γn, cv.ID'
  iframe Hnode Htb Hlive2
  ipureintro; exact ⟨Hnok, Hdy⟩

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem RestartNode.wp_proof
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG))
    (wp_newNode : newNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    RestartNode.spec (GF := GF) (hG := hG) :=
  ApiImpl.wp_RestartNode_impl wp_NewRawNode wp_newNode wp_node_run

end proof

end EtcdGrove
end Perennial
