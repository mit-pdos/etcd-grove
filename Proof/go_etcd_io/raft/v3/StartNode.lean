/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.StartNode
public import Spec.go_etcd_io.raft.v3.setupNode
public import Spec.go_etcd_io.raft.v3.node__run
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.InvAdvance
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Proof.go_etcd_io.raft.v3.ApiVocab
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiView
import Proof.go_etcd_io.raft.v3.InvApiDec
import Proof.go_etcd_io.raft.v3.InvApiJoin
import Proof.go_etcd_io.raft.v3.InvApiBoot
import all Proof.go_etcd_io.raft.v3.InvNodeRule
import Proof.go_etcd_io.raft.v3.SnapValidCert
import Proof.go_etcd_io.raft.v3.StepGhostMode
import Proof.go_etcd_io.raft.v3.InvStorageRead
import Proof.go_etcd_io.raft.v3.ConfchangeApiImpl
import Proof.go_etcd_io.raft.v3.ConfchangeApi

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

`setupNode` (`NewRawNode`, `Bootstrap`, `newNode`), then as `RestartNode`'s from `newNode` on: the
node's ghost state (the channels' hand-shakes, the tick channel's invariant, `dlv` and `rof`, the
configuration shared with the driver at the peers), `go n.run()` with `runPre` at the delivered log
`[]` (D12: the boot entries reach the application through the first `Ready`s), the term ceiling at
the bootstrap term `1` (the budget's, `budget_alloc_boot`). (2026-10-30, stage R5: restored from
U9's deletion, over `NewRawNode`'s boot bundle.)
-/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the section header. -/
private abbrev StartNode.specRaw : Prop :=
  ∀ (γ : RaftNames) (md : RNMode) (bud : BudgetNames) (c : Loc) (cv : Config)
    (lok si : GoInterfaceOk) (sn : StorNames)
    (gdlm gcap gccq gcam glive : GName)
    (σ : StorState) (hs : HardStateM) (csm : ConfStateM) (R R' : IProp GF)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer) (ps : List w64) (ctxs : List (List w8))
    (bootLog : List EntryM),
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.Applied' = W64 0 →
  σ.prev = entryID.mk (W64 0) (W64 0) → σ.ents = [] → σ.pend = [] →
  σ.fr = 0 → σ.sg = 0 → σ.dt = ∅ →
  HsEmpty hs →
  csm.Voters' = [] →
  csm.VotersOutgoing' = [] →
  csm.Learners' = [] →
  csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  σ.fl = W64 0 →
  -- (2026-11-01, durability stage I-6) no attach record: an empty storage, nothing applied or
  -- committed (`NewRawNode`'s `AttachRec` holds vacuously and its `ownStorage sn.unrec` is this one)
  sn.unrec = sn →
  ps = pv.map Peer.ID' →
  ps ≠ [] → ps.Nodup → W64 0 ∉ ps →
  (ps.length : Int) ≤ 2 ^ 62 →
  cv.ID' ∈ ps →
  γ.reCfg = GMap.listToSet ps →
  γ.reBoot = bootLog →
  BootLogOk ps bootLog →
  γ.reNoSnap = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗ R ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"FirstIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 1) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"LastIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 0) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #()))
         {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
            hsOpt hp hs ∗ csPts cs DFrac.discard csm al ∗
            |={⊤}=> isStorageD sn (interface.ok si) ∗ ownStorage sn (interface.ok si) σ ∗ R' }}) ∗
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ bootMarshal ps ctxs bootLog ∗
      bootInit γ md cv.ID' (GMap.listToSet ps) bootLog ∗ isCommitted γ bootLog ∗
      -- the cluster's term budget, at least at the bootstrap term `1` (`budget_alloc_boot`)
      inv budgetN (budgetInv bud) ∗ termLB bud (W64 1) ∗
      certLink γ sn ∗
      -- the configuration names' initial states
      monoListAuthOwn gdlm 1 ([] : List EntryM) ∗ monoListLbOwn gdlm ([] : List EntryM) ∗
      dghostVar gcap (DFrac.own 1) ((0 : Nat), cfgState (GMap.listToSet ps) ∅) ∗
      dghostVar gccq (DFrac.own 1) ((0 : Nat), cfgState (GMap.listToSet ps) ∅) ∗
      monoNatAuthOwn gcam 1 0 ∗ monoNatLbOwn gcam 0 ∗ dghostVar glive (DFrac.own 1) false }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      ∃ (γn : NodeNames) (n : Loc),
        ⌜γn.raft = γ ∧ γn.bud = bud ∧ γn.stor = interface.ok si ∧ γn.mode = md ∧ γn.sn = sn ∧
         nd = interface.mkOk (go.GoType.PointerType node.ty) #n ∧
         γn.dlm = gdlm ∧ γn.cap = gcap ∧ γn.ccq = gccq ∧ γn.cam = gcam ∧ γn.live = glive⌝ ∗
        R' ∗
        isNodeChan γn cv.ID' n ∗ nodeDriverChan γn cv.ID' n [] hsZero ∗
        nodeLiveRaw γn 1 ∗
        nodeCfg γn 0 (cfgState (GMap.listToSet ps) ∅) ∗
        peers ↦*{dq} pv }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

private theorem StartNode.wp_raw
    (wp_setupNode : setupNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    StartNode.specRaw (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): `NewRawNode.spec` generalized (I-6: `rawNodeAt`); the raw triple to restate for a restart (I-2, I-6)
  sorry

end proof

/-! ## The spec, from the raw triple -/

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
      savedPredOwn sn.gk DFrac.discard (raftSnapCertD (GF := GF) γ.raft) -∗ certLink γ.raft sn := by
  iintro #Hci #Hsv #Hgk
  have HcN : raftCertN γ.raft = N := HU.2.2.1
  unfold certLink storCertOk
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

/-- `StartNode.spec` from the raw triple (2026-10-30, stage R5): the node in the cluster's dynamic
mode of the client's decisions, taking `MsgSnap`s, its ghost state the dynamic one at the bootstrap
state (`rboot`, configuration index `0`), its table entry inserted (`nodeTabOk`), its view at the
voters' membership. -/
private theorem wp_StartNode_impl
    (hS : EtcdGrove.StartNode.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.StartNode.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): the spec restated (durability I-2/I-4/I-6/I-7: `nodeVacant`, the update over `raftState`, `restartStorage`)
  sorry

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem StartNode.wp_proof
    (wp_setupNode : setupNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    StartNode.spec (GF := GF) (hG := hG) :=
  ApiImpl.wp_StartNode_impl (StartNode.wp_raw wp_setupNode wp_node_run)

end proof

end EtcdGrove
end Perennial
