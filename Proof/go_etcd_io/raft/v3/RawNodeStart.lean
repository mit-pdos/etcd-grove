/- Lean-first (no Rocq counterpart).

## `NewRawNode.restartSpec`, proved (2026-11-23, #33 S3a)

`RestartNode`'s closing step, factored out of its proof (`RestartNode.lean`, from its `wp_start` to
the `ownRawNode` it hands to `node.run`), over `NewRawNode.spec` alone: the id's slot opened by
`raft_restart` (the durable state owned, not behind an atomic update), raft's storage names
allocated and the storage attached at a fresh key inside `InitialState`'s post, `NewRawNode`'s
open node closed (`ownRawNode_intro`). The private helpers are `RestartNode.lean`'s, copied: that
file is under edit for the crash law (#22), so it is left alone; once #22 lands, `RestartNode`'s
proof can be rewritten over `NewRawNode.wp_proofRestart` and the copies dropped.

`rawNodeEmptyStart`: the instance for a node of a new cluster without a bootstrap log, on an empty
storage whose `ConfState` names the voters (Antithesis's `EtcdBindingEmpty.cfg`).

(#33 S4, P-raft-4) The closing step proves `NewRawNode.restartAtSpec sc` (below): the node closed at
its protocol state (`ownRawNodeAt`, `RawNodeAt.lean`: the restarted state `restartP`, nothing queued,
the in-progress boundary at the stored log's end) and, at the scope flag `sc = true`, in the
Antithesis harness's scope (`RnScopeBasic`: pre-vote and check-quorum off, the static mode, the log's
boundary `base0`; `storCapF … 0` from the pre). `NewRawNode.restartSpec` is its corollary at
`sc = false` (`ownRawNodeAt_ownRawNode`), and `NewRawNode.emptyStartAbsSpec` (`RawNodeAbsSpecs.lean`)
its instance at an empty storage and `sc = true` (`NewRawNode.wp_proofEmptyStartAbs`).
-/
module

public import Proof.go_etcd_io.raft.v3.RawNodeStartSpec
import all Proof.go_etcd_io.raft.v3.RawNodeStartSpec
public import Proof.go_etcd_io.raft.v3.SnapshotHistory
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvBoot
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
public import Proof.go_etcd_io.raft.v3.Protocol.Enter
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.InvAdvance
public import Proof.go_etcd_io.raft.v3.InvApplyConf
import Proof.go_etcd_io.raft.v3.ConfchangeApiImpl
import Proof.go_etcd_io.raft.v3.ConfchangeApi
public import Proof.go_etcd_io.raft.v3.RawNodeAtLemmas
public import Proof.go_etcd_io.raft.v3.RawNodeAbsSpecs
public import Proof.go_etcd_io.raft.v3.RawNodeStartApi

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section spec_at
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`NewRawNode.restartSpec` at the node's protocol state** (#33 S4): its text, the post's node
`ownRawNodeAt` at the restarted state `restartR` (antithesis parity B1: an `RState`, at the applied
index `max b A`, the configuration point `a` and a ghost prefix `fp` below the log's boundary, empty at
`base0`; the node constant the `Config`'s flags, `cfgK cv`), nothing queued, the in-progress boundary
at the stored log's end (`offsetInProgress = σ.b + |σ.ents| + 1`), at the scope `sc`; at `sc = some md`
the scope's premises per flag (`RestartScopeOk`) and its resource (`storCapF … 0`, without
`snapshots`). (Until antithesis parity B1 a flag `sc : Bool`, `true` the scope `some {}`.) -/
abbrev NewRawNode.restartAtSpec (sc : Option RnMode) : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorContents) (csm : ConfStateM) (a : Nat) (m : Membership) (S : RaftState)
    (F : GName → IProp GF),
  ∀ (SV : SnapshotM → IProp GF) [∀ sv, Persistent (SV sv)],
  (∀ sv, SV sv ⊢ snapshotValid γ sv) →
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  (γ.maxData ≠ none → uint.Z cv.MaxSizePerMsg' ≤ entsCutMax) →
  (uint.nat cv.Applied' = 0 ∨ σ.b ≤ uint.nat cv.Applied' ∧ uint.nat cv.Applied' ≤ σ.commit) →
  max σ.b (uint.nat cv.Applied') ≤ a → a ≤ σ.commit →
  γ.bootLen ≤ σ.last →
  confStateIs csm m →
  ¬ clusterNoSnap γ →
  TraceLoggerOk cv.TraceLogger' →
  Cluster.trace γ = none →
  StorageHolds S σ →
  -- (2026-11-24) the configuration simple over the names' voters, the node one of them (until then
  -- `γ.rnMode = .static`, which `isCluster` contradicts: the scope was empty)
  (∀ md, sc = some md → RestartScopeOk γ cv σ m md) →
  ∀ (x : CrashNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isCluster γ N ∗ nodeVacantA γ cv.ID' x ∗ readyFits γ N ∗
      raftState γ cv.ID' S ∗
      confAt γ a m ∗
      restartStorage γ (interface.ok si) σ csm (uint.nat cv.Applied') F SV ∗
      □ (∀ md, ⌜sc = some md⌝ -∗ ⌜md.snapshots = false⌝ -∗ storCapF (interface.ok si) 0) }}
    (App (Val #(functions NewRawNode [])) (Val #c))
  {{ (rn : Loc) (err : GoInterface), RET (PairV #rn #err);
      ⌜err = interface.nil⌝ ∗
      ∃ (l : List EntryM) (sn : StorNames) (g : Nat) (K : GName) (fp : List EntryM),
        ownRawNodeAt γ.raftNames rn cv.ID'
          { rawNodeRestarted γ l (interface.ok si) sn σ.hs S m a with k := cfgK cv }
          (restartR S σ (max σ.b (uint.nat cv.Applied')) a (ApiImpl.stOf m) fp) []
          (σ.b + σ.ents.length) sc ∗
        ⌜σ.base = base0 → fp = []⌝ ∗
        isCommitted γ.raftNames l ∗
        ⌜l.length = max σ.b (uint.nat cv.Applied') ∧ l.drop σ.b = σ.ents.take (l.length - σ.b)⌝ ∗
        genView γ.raftNames cv.ID' x 1 g ∗ slotFree γ.raftNames cv.ID' g ∗
        raftState γ cv.ID' S ∗ F K }}

end spec_at

namespace ApiImpl
namespace RawNodeStart

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
  obtain ⟨⟨h0, -, hd, Hsok, -, -⟩, -⟩ := hm'
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
  -- (2026-11-12, Q39 (a)) the gate: traced, `c = 0`
  cases htr : Cluster.trace γ <;> dsimp only
  case some =>
    icases Hb with %Hc0
    ileft
    iexists 0
    isplitr; · ipureintro; omega
    ileft; iexact H0
  icases Hb with ⟨%k, %Hk, (%Hk0 | ⟨%sn', #Hsn', (#Hl | #Hl | %Hl)⟩), -⟩
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
private theorem certLink_make (γ : Cluster) (N : Namespace) (HU : UniNames γ N) (sn : StorNames)
    (Cert : SnapshotM → IProp GF) (hCert : ∀ sv, Cert sv ⊢ EtcdGrove.snapshotValid γ sv)
    (hsz : sn.sz = γ.raft.maxData.isSome) :
    ⊢ clusterInv (GF := GF) γ N -∗
      savedPredOwn sn.gsv DFrac.discard Cert -∗
      savedPredOwn sn.gk DFrac.discard (raftSnapCertD (GF := GF) γ.raft) -∗
      ctCommitted γ.raft sn -∗ certLink γ.raft sn := by
  iintro #Hci #Hsv #Hgk #Hct
  have HcN : raftCertN γ.raft = N := HU.2.1
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨-, -, -, -, %Hmb⟩
  unfold certLink
  iframe Hct
  isplitr
  rotate_left
  · isplitr
    · ipureintro; exact hsz
    ipureintro; exact Hmb
  unfold storCertOk
  isplitr
  · iintro !> %sv %E %HE Hc
    rw [HcN] at HE
    unfold svCert
    icases Hc with ⟨%SV, #Hp, #HSV⟩
    ihave #Heq := saved_pred_agree sn.gsv DFrac.discard DFrac.discard SV
      Cert sv $$ Hp Hsv
    ihave Hv : ▷ EtcdGrove.snapshotValid (GF := GF) γ sv $$ []
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨Hiff, -⟩
      iapply hCert sv
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
private def restartCt (F : List EntryM) (c : Nat) : List (Nat × w64) :=
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

/-- An empty queue, its states named. -/
private theorem pendAt_nil (γ : RaftNames) (id : w64) (W : DurMaps) :
    ⊢ pendAt (GF := GF) γ id W none [] [] [] := by
  simp only [pendAt]
  iexists []
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  · simp only [List.zip_nil_left]
    iapply (BigSepL2.bigSepL2_nil (Φ := fun _ (l : Loc) (x : MsgSt × Pending) =>
      iprop(msgIn (GF := GF) l DFrac.discard x.1 ∗ pendingRel γ id W x.1 x.2))).2
    iempintro

/-- The basic scope's owned part at the start: its facts, the storage's cap from the pre. -/
private theorem rnScopeAt_start {γ : RaftNames} {id : w64} (sc : Option RnMode) (rs : RNState)
    (s : NState) (st : Storage) (Hst : s.logst.storage = st)
    (H : ∀ md, sc = some md → RnScope md id rs s ∧ RnCfgIn md γ id rs ∧ KTie rs s ∧
      (md.transfer = true → XScopeOk γ md s)) :
    □ (∀ md, ⌜sc = some md⌝ -∗ ⌜md.snapshots = false⌝ -∗ storCapF (GF := GF) st 0) ⊢
      rnScopeAt γ id sc rs s := by
  cases sc with
  | none => iintro -; iapply rnScopeAt_none
  | some md =>
    unfold rnScopeAt
    iintro #Hc
    rw [Hst]
    isplitr
    · ipureintro; exact H md rfl
    · imodintro; iintro %h; iapply Hc $$ %md; ipureintro; rfl; ipureintro; exact h

theorem NewRawNode_restartAt_impl (sc : Option RnMode)
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG)) :
    NewRawNode.restartAtSpec (GF := GF) (hG := hG) sc := by
  unfold NewRawNode.restartAtSpec
  unfold Cluster.raftNames
  intro γ N c cv lok si σ csm a m S F Cert hpCert hCert H1 H2 H3 H4 H5 H6 H7 H8 H9 Hmx Happ Ha1 Ha2
    Hboot Hcs Hnsm Htlk HtrC HSh Hsc x
  have HtrG : γ.raft.reTrace = none := HtrC
  wp_start_folded as ⟨Hc, #Hlg, #Hcl, Hvac, #Hfits, HrS, #Hconf, Hrs, #Hscp⟩
  iunfold EtcdGrove.isCluster at Hcl
  ihave #Hcl' := Hcl
  iunfold isClusterU at Hcl'
  icases Hcl' with ⟨%HU, #Hci, #Hpool⟩
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, -, -⟩
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
  have HsN : (↑(slotN γ.raft cv.ID') : CoPset) ⊆ ↑N := by
    intro p hp
    have := slotN_raftN γ.raft cv.ID' p hp
    unfold raftN at this; rw [HNs] at this
    exact nclose_subseteq N "raft" p this
  -- the id's slot opened (`raft_restart`) over the client's durable half, owned
  iunfold EtcdGrove.nodeVacantA at Hvac
  iunfold nodeVacantAU at Hvac
  iunfold EtcdGrove.raftState at HrS
  iunfold raftStateU at HrS
  icases HrS with ⟨Hdur, #HtS, #Hbinv⟩
  -- (2026-11-21, the crash invariant) the restart is a ghost step: at a step, with the token
  iapply (wp_ncfupd _ _ (by rfl))
  unfold ncfupd
  iintro Hnc
  imod raft_restart ⊤ γ.raft cv.ID' (md := true) x σ.base σ.hs.Commit'
    (fun S' => S' = S) (fun S' => ownDurGhost γ.raft cv.ID' S')
    CoPset.subseteq_top Hmdb
    (fun S' HS' => by
      subst HS'
      obtain ⟨Hb1, Hb2, Hb3, -, -, Hbc, Hwc, Hcc, -, -⟩ := HSh
      simp only [StorContents.b, StorContents.commit] at Hbc Hwc Hcc
      have := uint_nat_eq σ.hs.Commit'; have := uint_nat_eq σ.base.index'
      have := uint_nat_eq S'.commit
      -- (2026-11-26, #33 parity B1) the durable log is the stored one, past the bootstrap log
      have HbL : γ.raft.reBoot.length ≤ S'.last := by
        have Hr := (plogTermAt_some_range _ _ _ _ Hb2).2
        have Hd : σ.ents.length =
            S'.ents.length - (uint.Z σ.base.index' - uint.Z S'.base.index').toNat := by
          rw [Hb3]; unfold RaftState.entsFrom; rw [List.length_drop]
        unfold plogLastIndexZ at Hr
        unfold Cluster.bootLen StorContents.last StorContents.b at Hboot
        unfold RaftState.last
        have := uint_nat_eq S'.base.index'
        omega
      exact ⟨Hb1, by omega, by omega, Hb2, Hwc, Or.inr HbL⟩) (fun h => absurd HtrG h)
    $$ Hnc Hvac [Hdur]
    with ⟨Hnc, %S', %HSS, Hdur, Hg, %gen, Hgen, Hfree, #HI1r⟩
  · iintro Hnc1
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists S
    iframe Hdur
    isplitr; · ipureintro; rfl
    iintro Hdur
    imod Hmask with -
    imodintro
    iframe Hnc1 Hdur
  subst S'
  have HS : StorageHolds S σ := HSh
  imodintro
  iframe Hnc
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
    unfold StorContents.last StorContents.b at Hboot
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
  imod saved_pred_alloc Cert DFrac.discard trivial
    with ⟨%gsv, #Hsv⟩
  imod saved_pred_alloc (raftSnapCertD (GF := GF) γ.raft) DFrac.discard trivial with ⟨%gk, #Hgk⟩
  imod snapHistory_alloc (GF := GF) with ⟨%history, Hclock⟩
  imod installHistory_alloc (GF := GF) with ⟨%installs, Hinst⟩
  ihave Hhistory : iprop(snapHistoryOwn history 0 0 ∗ installHistoryOwn installs 0 []) $$ [Hclock Hinst]
  · iframe Hclock Hinst
  let sn : StorNames :=
    { ga := ga, gg := gg, gsv := gsv, gd := gdd, gk := gk, history := history, installs := installs, a0 := max σ.b (uint.nat cv.Applied'),
      c0 := σ.commit, ct := restartCt (fp ++ σ.ents) σ.commit, sz := γ.raft.maxData.isSome }
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
  ihave #Hlink := certLink_make γ N HU sn Cert hCert rfl $$ Hci Hsv Hgk Hct
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
  -- (2026-11-02, stage II (u)) fewer than `2^62` ids listed: the membership's (`CfgOk`)
  have Hcsl : (GMap.size (GMap.listToSet csm.Voters' ∪ GMap.listToSet csm.VotersOutgoing' ∪
      GMap.listToSet csm.Learners' ∪ GMap.listToSet csm.LearnersNext') : Int) ≤ 2 ^ 62 := by
    obtain ⟨hV, hVO, hL, hLN, -⟩ := Hcs
    rw [cc_listToSet_of_perm hV, cc_listToSet_of_perm hVO, cc_listToSet_of_perm hL,
      cc_listToSet_of_perm hLN]
    have h2 := memOf_ids_of_inv Hvalm.1.1
    rw [stOf_cfg, memOf_cfgOf] at h2
    have h1 : GMap.size (cfgOf m).ids < 2 ^ 62 := Hvalm.1.2.2
    show (GMap.size m.ids : Int) ≤ _
    rw [h2]; omega
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
  iapply wp_fupd
  wp_apply wp_NewRawNode c cv lok si sn σv σ.hs csm iprop(Rb ∗ storAuths sn.unrec σv)
    iprop(∃ K, storKeyNames K sn ∗ F K) (stOf m) γ.raft [] H1 H2 H3 H4 H5 H6 H7 H8
    (fun h => by
      change γ.raft.maxData.isSome = true at h
      have h2 := Hmx (by intro hn; change γ.raft.maxData = none at hn; rw [hn] at h; cases h)
      word) H9
    (by show LogIndicesOk σ.base σ.ents; rw [Hse]; exact Hwf) rfl Hf.1 (by rw [Hca]; exact Hf.2) (Int.le_refl _) (Nat.le_refl _)
    rfl Hlast HAR (.inr ⟨HbcZ, HcL⟩) Happ' Hrestore Hcsl HcsOk (fun h => absurd HtrG h)
    $$ [Hc HRb HA]
    as %rn %err ⟨⟨%K, #HKn, HFK⟩, -, %s, %r, Hrn, %Herr, %Hsn2, -⟩
  · -- (2026-11-12, trace-check step 5) untraced: the capability's start is the nil logger
    ihave Htc : trCapStart (GF := GF) γ.raft.reTrace γ.raft cv.ID' cv.TraceLogger' (bootCfg [])
        (bootPhase [] cv.ID') bootNone $$ []
    · rw [HtrG]; unfold trCapStart; ipureintro; exact Htlk
    iframe Hc Hlg Htc
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
    -- (2026-11-12, trace-check step 5) untraced: no compaction to refute
    ihave #Hnc := trNoCut_none (GF := GF) (interface.ok si)
    rw [HtrG]; iframe Hnc
    -- the attach: a fresh key recording raft's storage names
    imod dghostVar_alloc (GF := GF)
      ((sn.ga, sn.gg, sn.gsv, sn.gd, sn.gk, sn.a0, sn.c0, sn.ct, sn.sz, sn.history, sn.installs) :
        Nat × Nat × Nat × Nat × Nat × Nat × Nat × List (Nat × w64) × Bool × Nat × Nat) with ⟨%K, HK⟩
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
      iexists Cert, EtcdGrove.storBnd (GF := GF) γ K,
        EtcdGrove.nodeCommitLb (GF := GF) γ K
      isplitl [Hst]
      · iunfold EtcdGrove.isStorage at Hst
        iExactEq Hst; rfl
      isplitr; · iexact Hsv
      isplitr
      · iintro !> %sv #H
        imodintro; iexact H
      isplitr
      · iintro !> %c' Hb
        iapply storBnd_raftBnd γ K sn c' $$ HKn Hga0 Hb
      · iintro !> %sv Hv Hd
        imodintro
        ihave Hvalid := hCert sv $$ Hv
        iapply storDL_raftDL γ K sn sv $$ HKn Hvalid Hd
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
  obtain ⟨Hlsn, Hgsn, Hgtr0, Hcq⟩ := Hsn2
  -- the committed log handed out at the start: up to `max b A`
  have Ha0c : max σ.b (uint.nat cv.Applied') ≤ σ.commit := by omega
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
  -- (2026-11-12, trace-check step 5) the trace mode, untraced
  have Hgh : s.gh = { sn := s.gh.sn } := by
    have h := Hgh; rw [Hgtr0, HtrG] at h; exact h
  obtain ⟨Ht, Hv, Hr, Ho, Hst0, Hpd⟩ := Hterm
  obtain ⟨Hlp, Hse0, Hue, Hsd, Hcm, Hap, Hapg, Hun, Hsn0, Hsg, Hdtk, Hksn⟩ := Hlog
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
  have Hns : γ.raft.reNoSnap = false := by
    unfold clusterNoSnap at Hnsm; cases h : γ.raft.reNoSnap
    · rfl
    · exact absurd h Hnsm
  ihave Hghost : ownStepGhost γ.raft (RNMode.toG (γ.mode inferInstance) g) (stOf m).cfg cv.ID' s1
      $$ [Hg]
  · rw [Hmd]
    simp only [RNMode.toG]
    iapply (ownStepGhost_dyn γ.raft noDec (stOf c0m) h0 g (stOf m).cfg cv.ID' s1).2
    isplitr
    · ipureintro
      refine ⟨HD, rfl, ⟨by show s.gh.ns = _; rw [Hgh, Hns], by show s.gh.tr = _; rw [Hgh, HtrG],
        fun m _ => MsgTrOk.of_none HtrG m⟩⟩
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
    unfold xfW xtW
    rw [show s1.gh.xw = ∅ by show s.gh.xw = ∅; rw [Hgh], show s1.gh.xt = ∅ by show s.gh.xt = ∅; rw [Hgh]]
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; iempintro
    · iapply BigSepM.bigSepM_empty.2; iempintro
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
  -- (2026-11-02, stage II (u)) the configuration point within the stored commit, no snapshot
  have HcapR : CapOk rs0 s1 := by
    refine ⟨?_, fun l (h : (none : Option SnapLoan) = some l) => by simp at h, fun _ p hp => ?_⟩
    · show (a : Int) ≤ uint.Z s.logst.committed
      rw [Hcm, Hca]; unfold StorContents.commit at Ha2; have := uint_nat_eq σ.hs.Commit'; omega
    · change s.logst.snap = some p at hp; rw [Hsn0] at hp; cases hp
  -- (#33 S4) the protocol reading, the in-progress boundary, the scope
  have HipR : uint.nat s1.logst.inprogress = σ.b + σ.ents.length + 1 := by
    show uint.nat s.logst.inprogress = _
    have h1 := Hsvr.2
    simp only [σv] at h1
    unfold StorContents.b
    have := uint_nat_eq σ.base.index'; have := uint_nat_eq s.logst.inprogress
    omega
  let rsK : RNState := { rs0 with k := cfgK cv }
  have HscR : ∀ md, sc = some md → RnScope md cv.ID' rsK s1 := by
    intro md hsc
    obtain ⟨Hpv0, Hcq0, -, Hmo, Hb0⟩ := Hsc md hsc
    refine ⟨fun h _ => (Hmo h).2.1, fun h => ?_, fun h => ?_, fun _ => ⟨Hpd, ?_⟩,
      fun h => ⟨rfl, ?_, Hsn0, ?_⟩, fun _ => ?_, fun _ _ hp => absurd (Hr.symm.trans hp) (by decide),
      fun _ hp => absurd (Hr.symm.trans hp) (by decide), fun _ _ hp => absurd Hr hp⟩
    · show s.prevote = false; rw [Hpvoff, Hpv0 h]
    · show s.cq = false; rw [Hcq, Hcq0 h]
    · intro hl; exact absurd (Hr.symm.trans hl) (by decide)
    · show s.logst.prev = base0; rw [Hlp, ← Hb0 h]
    · intro m' hm; change m' ∈ s.outbox at hm; rw [Ho] at hm; cases hm
    · show s.gh.xs = false; rw [Hgh]
  have HcinR : ∀ md, sc = some md → RnCfgIn md γ.raft cv.ID' rsK := by
    intro md hsc
    obtain ⟨-, -, Hid, Hmv, -⟩ := Hsc md hsc
    exact ⟨Hid, fun h => ⟨fun _ => (Hmv h).1, (Hmv h).2.2⟩, HtrG,
      by show (γ.mode inferInstance).isDyn = true; rw [Hmd]; rfl⟩
  have HkR : KTie rsK s1 := by
    show NodeK.mk s.prevote s.cq s.sdr = cfgK cv
    rw [Hpvoff, Hcq, Hsdr]; rfl
  -- (antithesis parity B1, Q3 item 2) the transfer scope's facts: no leader known, none stamped
  have HxR : ∀ md : RnMode, XScopeOk γ.raft md s1 := by
    intro md
    have Hl : (toPState s1).lead = W64 0 := by rw [HtoP1]; rfl
    refine ⟨fun _ => .inl Hl, fun p hp => ?_, fun h => absurd Hl h⟩
    change (s.gh.xw !! p).isSome = true at hp
    rw [Hgh] at hp; simp at hp
  ihave Hrn : ownRawNodeAt γ.raft rn cv.ID' rsK (toRState rsK fp s1) []
      (σ.b + σ.ents.length) sc $$ [Hrn Hphys Hghost Hsteps Hsteps_cap Hhistory]
  · iapply ownRawNodeAt_intro γ.raft rn cv.ID' rsK (toRState rsK fp s1) []
      (σ.b + σ.ents.length) sc s1 (stOf m).cfg fp (ds := MA) rnv sv hprev []
      (Hglq := by show s.gh.lq = []; rw [Hgh])
      Hrel.2 (fun h => by simp only [rsK, rs0] at h; rw [Hmd] at h; cases h) Hasync
      (by show ((fp ++ σ.ents).take _).length = _; rw [HDlen, toNat_uZ]; exact Happn.symm)
      Hun.symm (fun _ => Hsn0) trivial Ht.symm ⟨Hsg.symm, Hlsn.symm⟩
      ⟨fun _ => preGuardF_fol Hr, rfl, by show uint.Z s.term ≤ uint.Z S.term; rw [Ht, HsT]; exact Int.le_refl _,
        fun h => absurd (Hr.symm.trans h) (by decide), fun _ => Hr⟩
      (by show 0 = s.gh.outlb; rw [Hgh]) (by show false = s.gh.unst; rw [Hgh])
      (uint_Z_nonneg _)
      ⟨fun _ => by rw [Hap]; exact Hflk.1, fun h => absurd h (by rw [Hap]; exact Int.lt_irrefl _)⟩
      ⟨by show s.gh.slent = false; rw [Hgh],
        fun _ => ⟨by show s.gh.snp = none; rw [Hgh], fun _ _ _ _ h => by cases h⟩,
        fun l h => (by cases h), HcapR⟩
      ⟨by show ((fp ++ σ.ents).take _).length ≤ s.logst.dtk; rw [HDlen, Hdtk1]; exact Ha0c,
        fun i hi1 hi2 => by
          change ((fp ++ σ.ents).take _).length < i at hi1
          change i ≤ s.logst.dtk at hi2
          rw [HDlen] at hi1; rw [Hdtk1] at hi2
          obtain ⟨t, ht, -⟩ := restartCt_complete HcF (by omega) hi2
          exact ⟨hi2, t, ht⟩⟩
      Hsvr.1.symm HphsR rfl HipR
      (show s.gh.tr = γ.raft.reTrace by rw [Hgh, HtrG])
      $$ Hrn Hphys Hghost [] Hsoft Hph Hsteps Hsteps_cap [] HcD [] [] [] [] [Hhistory] [Hdurt] [] []
    · iunfold sdrOk; iexists _; iexact Hsd0
    · iapply pendAt_nil
    · iapply ackInv_none; intro _ _ _ _ h; cases h
    · iapply loanCom_none γ.raft rfl
    · rw [show s1.logst.snap = none from Hsn0]; iapply snapLocOk_none
    · rw [show s1.logst.ksn = [] from Hksn]; iapply restoredSnapHistory_nil
    · iapply restoreLedger_fresh γ.raft cv.ID' sn s1 (show s1.logst.ksn = [] from Hksn) Ho $$ Hhistory
    · iapply durTie_congr γ.raft (rs := rs0) (s := s1) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) $$ Hdurt
    · iapply rnTrace_none (GF := GF) γ.raft rnv.raft' cv.ID' _ _ s1 (by show s.gh.tr = none; rw [Hgh])
    · iapply rnScopeAt_start sc rsK s1 (interface.ok si) Hsg
        (fun md h => ⟨HscR md h, HcinR md h, HkR, fun _ => HxR md⟩) $$ Hscp
  -- the driver's view of the configuration is the node's: at the configuration point `a`
  have Hhp : hprev = σ.hs := by rw [Hhz, Hca]
  -- the post: the node at `rawNodeRestarted`, its committed log, the slot's generation, the
  -- durable state back, the storage's frame
  imodintro
  iapply HΦ
  isplitr; · ipureintro; rfl
  iexists (fp ++ σ.ents).take (max σ.b (uint.nat cv.Applied')), sn, gen, K, fp
  have HrR : toRState rsK fp s1 =
      restartR S σ (max σ.b (uint.nat cv.Applied')) a (stOf m) fp := by
    have hap : s.logst.applied = W64 ((max σ.b (uint.nat cv.Applied') : Nat) : Int) := by
      rw [Hap, ← Happn, w64_to_nat_id]
    have hpci : pciR s1 = W64 0 := by
      show (if s.role = .leader then s.pci else W64 0) = W64 0; rw [Hr]; rfl
    have hsn : s1.logst.snap.isSome = false := by
      show s.logst.snap.isSome = false; rw [Hsn0]; rfl
    simp only [toRState, restartR, RState.mk.injEq]
    refine ⟨HtoP1, hap, hpci, hsn, ?_⟩
    simp [rsK, rs0]
  isplitl [Hrn]
  · rw [← HrR]
    iExactEq Hrn
    simp only [rsK, rs0, rawNodeRestarted, Hhp, Cluster.rnMode]
  isplitr
  · ipureintro
    intro hb
    have h1 := Hfp'.1
    rw [hb, base0_index] at h1
    exact List.eq_nil_of_length_eq_zero (by omega)
  isplitr; · iexact HcD
  isplitr
  · ipureintro
    refine ⟨HDlen, ?_⟩
    have Hfl : fp.length = σ.b := by
      unfold StorContents.b; have := uint_nat_eq σ.base.index'; omega
    rw [HDlen, List.drop_take, show (fp ++ σ.ents).drop σ.b = σ.ents by rw [← Hfl, List.drop_left]]
  iframe Hgen Hfree HFK
  iunfold EtcdGrove.raftState
  unfold raftStateU
  iframe Hdur HtS Hbinv

/-- `NewRawNode.restartSpec`: `restartAtSpec` outside the scope, the protocol state forgotten. -/
theorem NewRawNode_restart_impl
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG)) :
    NewRawNode.restartSpec (GF := GF) (hG := hG) := by
  unfold NewRawNode.restartSpec
  intro γ N c cv lok si σ csm a m S F Cert hpCert hCert H1 H2 H3 H4 H5 H6 H7 H8 H9 Hmx Happ Ha1 Ha2
    Hboot Hcs Hnsm Htlk HtrC HSh x
  wp_start_folded as ⟨Hc, Hlg, Hcl, Hvac, Hfits, HrS, Hconf, Hrs⟩
  wp_apply (NewRawNode_restartAt_impl none wp_NewRawNode γ N c cv lok si σ csm a m S F Cert hCert
      H1 H2 H3 H4 H5 H6 H7 H8 H9 Hmx Happ Ha1 Ha2 Hboot Hcs Hnsm Htlk HtrC HSh
      (fun _ h => by cases h) x)
    $$ [Hc Hlg Hcl Hvac Hfits HrS Hconf Hrs]
    as %rn %err ⟨%Herr, %l, %sn, %g, %K, %fp, Hrn, -, #Hcm, %Hl, Hgen, Hfree, HrS, HF⟩
  · iframe Hc Hlg Hcl Hvac Hfits HrS Hconf Hrs
    iintro !> %md %h; cases h
  iapply HΦ
  isplitr; · ipureintro; exact Herr
  iexists l, sn, g, K
  ihave Hrn := ownRawNodeAt_ownRawNode (GF := GF) _ _ _ _ _ _ _ _ $$ Hrn
  rw [ownRawNode_with_k]
  iframe Hrn Hcm Hgen Hfree HrS HF
  ipureintro; exact Hl

end wrap

end RawNodeStart
end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`NewRawNode`, started in a cluster, closed** (`NewRawNode.restartSpec`), over `NewRawNode`'s
spec. -/
theorem NewRawNode.wp_proofRestart
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG)) :
    NewRawNode.restartSpec (GF := GF) (hG := hG) :=
  ApiImpl.RawNodeStart.NewRawNode_restart_impl wp_NewRawNode

end proof

section pure
variable [GooseExts]

/-- An empty storage holds the initial durable state. -/
theorem emptyStorContents_holds : StorageHolds RaftState.init emptyStorContents := by
  unfold StorageHolds
  refine ⟨Int.le_refl _, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [plogTermAt, RaftState.init]
  · rfl
  · simp [StorContents.b, StorContents.commit]
  · simp [StorContents.commit, RaftState.init]
  · simp [StorContents.commit, RaftState.init]
  · intro sv h; cases h
  · intro h; exact absurd rfl h

/-- The voters' conf state reports their simple membership. -/
theorem votersConfState_is (vs : List w64) (h : vs.Nodup) :
    confStateIs (votersConfState vs) (Membership.simple (GMap.listToSet vs)) := by
  have hE : ([] : List w64) ≡ₚ GMap.elements (∅ : GSet w64) := by
    refine (List.perm_ext_iff_of_nodup List.nodup_nil (GMap.NoDup_elements _)).2 ?_
    intro k
    rw [GMap.elem_of_elements]
    simp only [List.not_mem_nil, false_iff]
    exact GMap.not_elem_of_empty _
  refine ⟨?_, hE, hE, hE, rfl⟩
  show vs ≡ₚ GMap.elements (GMap.listToSet vs)
  refine (List.perm_ext_iff_of_nodup h (GMap.NoDup_elements _)).2 ?_
  intro k; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]

end pure

section proof2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`NewRawNode` for a node of a new cluster without a bootstrap log** (`NewRawNode.emptyStartSpec`):
`NewRawNode.restartSpec` at the empty storage and the voters' conf state. -/
theorem NewRawNode.wp_proofEmptyStart
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG)) :
    NewRawNode.emptyStartSpec (GF := GF) (hG := hG) := by
  unfold NewRawNode.emptyStartSpec
  intro γ N c cv lok si vs F SV hpSV hSV H1 H2 H3 H4 H5 H6 H7 H8 H9 Hmx HA0 Hb0 Hnd Hnsm Htlk HtrC x
  have HAn : uint.nat cv.Applied' = 0 := by rw [HA0]; rfl
  have Hb : emptyStorContents.b = 0 := rfl
  have Hcm : emptyStorContents.commit = 0 := rfl
  wp_start_folded as Hpre
  wp_apply (NewRawNode.wp_proofRestart wp_NewRawNode γ N c cv lok si emptyStorContents
      (votersConfState vs) 0 (Membership.simple (GMap.listToSet vs)) RaftState.init F SV hSV
      H1 H2 H3 H4 H5 H6 H7 H8 H9 Hmx (.inl HAn) (by rw [Hb, HAn]; omega) (Nat.zero_le _)
      (by rw [Hb0]; exact Nat.zero_le _) (votersConfState_is vs Hnd) Hnsm Htlk HtrC emptyStorContents_holds x)
    $$ [Hpre]
    as %rn %err ⟨%Herr, %l, %sn, %g, %K, Hrn, -, %Hl, Hgen, Hfree, HrS, HF⟩
  · rw [HAn]; iexact Hpre
  have Hl0 : l = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [Hl.1, Hb, HAn]; rfl
  subst Hl0
  iapply HΦ
  isplitr; · ipureintro; exact Herr
  iexists sn, g, K
  iframe Hrn Hgen Hfree HrS HF

/-- **`NewRawNode` at an empty storage, in the harness's scope** (`NewRawNode.emptyStartAbsSpec`,
#33 S4): `restartAtSpec` at the scope flag `true`, the empty storage and the voters' conf state; the
restarted protocol state at the empty storage is the initial one (`pInit`), the boundary `0`. -/
theorem NewRawNode.wp_proofEmptyStartAbs
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG)) :
    NewRawNode.emptyStartAbsSpec (GF := GF) (hG := hG) := by
  unfold NewRawNode.emptyStartAbsSpec NewRawNode.emptyStartForm
  intro γ N c cv lok si vs F SV hpSV hSV H1 H2 H3 H4 H5 H6 H7 H8 H9 Hmx HA0 Hb0 Hnd Hnsm Htlk HtrC
    Hpq Hmd x
  have HAn : uint.nat cv.Applied' = 0 := by rw [HA0]; rfl
  have Hb : emptyStorContents.b = 0 := rfl
  wp_start_folded as ⟨Hc, Hlg, Hcl, Hvac, Hfits, HrS, Hconf, Hrs, #Hcap⟩
  wp_apply (ApiImpl.RawNodeStart.NewRawNode_restartAt_impl (some {}) wp_NewRawNode γ N c cv lok si
      emptyStorContents (votersConfState vs) 0 (Membership.simple (GMap.listToSet vs)) RaftState.init
      F SV hSV H1 H2 H3 H4 H5 H6 H7 H8 H9 Hmx (.inl HAn) (by rw [Hb, HAn]; omega) (Nat.zero_le _)
      (by rw [Hb0]; exact Nat.zero_le _) (votersConfState_is vs Hnd) Hnsm Htlk HtrC
      emptyStorContents_holds (fun md h => by
        cases h
        exact ⟨fun _ => Hpq.1, fun _ => Hpq.2,
          fun _ => by rw [Hmd.1]; exact (GMap.elem_of_list_to_set _ _).2 Hmd.2,
          fun _ => ⟨Hmd.1.symm, rfl, rfl⟩, fun _ => rfl⟩) x)
    $$ [Hc Hlg Hcl Hvac Hfits HrS Hconf Hrs]
    as %rn %err ⟨%Herr, %l, %sn, %g, %K, %fp, Hrn, %Hfp, -, %Hl, Hgen, Hfree, HrS, HF⟩
  · rw [HAn]
    iframe Hc Hlg Hcl Hvac Hfits HrS Hconf Hrs
    iintro !> %md %h %hs; iexact Hcap
  have Hl0 : l = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [Hl.1, Hb, HAn]; rfl
  subst Hl0
  iapply HΦ
  isplitr; · ipureintro; exact Herr
  iexists sn, g, K
  iframe Hgen Hfree HrS HF
  obtain rfl : fp = [] := Hfp rfl
  iExactEq Hrn
  simp only [restartR, rInit, Hb, HAn]
  rfl

end proof2

end EtcdGrove
end Perennial
