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
import Proof.go_etcd_io.raft.v3.Protocol.Enter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The spec -/

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

/-- **`StartNode`** (2026-11-02, stage II (o); until then a raw triple over raft's internals, the
wrapper `sorry`): the client's update fires at the call's start (a ghost step: nothing physical is
read before `setupNode`), inside the id's slot (`raft_start_boot`, through its accessor), which
gives the bootstrap state's volatile half and the slot's whole generation with its free queue;
raft names the storage at the attach (`restartStorage`'s continuation, inside `InitialState`'s
post: fresh storage names, an empty view, the key `K` recording them); `setupNode` builds the
node; its table entry is inserted while the struct is still owned whole; then `run`'s ghost state
and `go n.run()`, as before. -/
private theorem wp_StartNode_impl
    (wp_setupNode : setupNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    EtcdGrove.StartNode.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.StartNode.spec
  intro γ N vs ctxs c cv lok si csm Q F peers dq pv H1 H2 H3 H4 H5 H6 H7 H8 H9 Happ Hv Hvo Hl Hln
    Hal Hvs
  wp_start as ⟨Hc, #Hlg, #Hboot, Hvac, HAU, Hrs, Hpeers, #Hctx⟩
  iunfold EtcdGrove.nodeBoot at Hboot
  iunfold nodeBootU at Hboot
  icases Hboot with ⟨#Hcl, %Hbp, #Hmarsh, #Hcb, #Hbinv, #Htlb1⟩
  obtain ⟨Hid, Hnd, Hnz, Hlen, Hcfg, ⟨gd, Hmr⟩, Hbl⟩ := Hbp
  ihave #Hcl' := Hcl
  iunfold isClusterU at Hcl'
  icases Hcl' with ⟨%HU, #Hci, #Hpool, #Htab⟩
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, -, -⟩
  have Hsl := HU.2.1
  obtain ⟨h0, h1, Hmd⟩ := Hmr.mode
  have HD : γ.raft.dyn = some (DynCfg.ofFold noDec (stOf (Membership.simple (GMap.listToSet vs))) h0) :=
    Hmr.1.2.2.1
  have HdynOk : ∀ γn : NodeNames, NodeOk γ γn → γn.mode.isDyn = true := fun γn h => by
    rw [h.2.2.2, Hmd]; rfl
  have Hmdb : γ.raft.reDyn.isSome = true := by
    have := reDyn_of HD
    cases h : γ.raft.reDyn with
    | none => exact absurd h this
    | some _ => rfl
  -- the client's update, inside the id's slot: the bootstrap state's volatile half
  have HsN : (↑(slotN γ.raft cv.ID') : CoPset) ⊆ ↑N := by
    intro p hp
    have := slotN_raftN γ.raft cv.ID' p hp
    unfold raftN at this; rw [HNs] at this
    exact nclose_subseteq N "raft" p this
  iunfold EtcdGrove.nodeVacant at Hvac
  iunfold nodeVacantU at Hvac
  imod raft_start_boot ⊤ γ.raft cv.ID' (md := true) Q CoPset.subseteq_top Hmdb $$ Hvac [HAU]
    with ⟨HQ, Hg, %gen, Hgen, Hfree⟩
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
    icases HS with ⟨HS, %HSi⟩
    subst HSi
    icases HC with ⟨-, Hcomm⟩
    ihave Hcomm := Hcomm $$ %PUnit.unit
    iunfold EtcdGrove.raftState at HS
    iunfold raftStateU at HS
    icases HS with ⟨Hdur, #Htlb0, #Hbi0⟩
    imodintro
    iframe Hdur
    iintro Hdur
    iapply Hcomm
    iunfold EtcdGrove.raftState
    unfold raftStateU
    iframe Hdur Htlb0 Hbi0
  -- the storage's frame and reads (`restartStorage` of the empty contents, freeze point `0`)
  iunfold restartStorage at Hrs
  icases Hrs with ⟨%i, %Rb, %f, %Hi, %Hf, HRb, #HFI, #HLI, #HIS⟩
  cases Hi
  have Hf0 : f = 0 := by
    have h0 : uint.nat (W64 0) = 0 := rfl
    simp only [StorContents.b, StorContents.commit, h0] at Hf; omega
  subst Hf0
  -- raft's storage names, fresh: the floor, the snapshot handed out, the certified terms, the
  -- contract's `SV` and the received snapshots' certificate (no attach record: nothing stored)
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%ga, Hga, #Hga0⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%gg, Hgg, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := w64) with ⟨%gdd, Hgd⟩
  imod saved_pred_alloc (EtcdGrove.snapshotValid (GF := GF) γ) DFrac.discard trivial
    with ⟨%gsv, #Hsv⟩
  imod saved_pred_alloc (raftSnapCertD (GF := GF) γ.raft) DFrac.discard trivial with ⟨%gk, #Hgk⟩
  let sn : StorNames := { ga := ga, gg := gg, gsv := gsv, gd := gdd, gk := gk }
  let σv : StorState := { prev := entryID.mk (W64 0) (W64 0), ents := [], pend := [] }
  -- (2026-11-02, stage II (p)) no attach record: its terms are vacuously the committed log's
  icases (entails_wand (persistent_entails_left (ownRaftGhost_cmt γ.raft cv.ID' _))) $$ Hg
    with ⟨Hg, %fpc, -, -, #Hcmt⟩
  ihave #Hct : ctCommitted (GF := GF) γ.raft sn $$ []
  · unfold ctCommitted
    iexists []
    isplitr
    · iapply isCommitted_mono γ.raft [] _ (List.nil_prefix) $$ Hcmt
    ipureintro; intro i t h; simp [sn] at h
  ihave #Hlink := certLink_make γ N HU sn $$ Hci Hsv Hgk Hct
  ihave HA : storAuths (GF := GF) sn σv $$ [Hga Hgg Hgd]
  · unfold storAuths storCaught
    iframe Hgg
    isplitl [Hga]
    · iExactEq Hga; rfl
    isplitl [Hgd]
    · iExactEq Hgd; rfl
    isplitr
    · iExactEq Hga0; rfl
    iintro !> %i' %t %H
    exact absurd H.2 List.not_mem_nil
  -- the node's configuration names, `live`, the durable state and role, the last batch's maps
  imod mono_list_own_alloc (GF := GF) ([] : List EntryM) with ⟨%gdlm, Hdlm, #Hdlb⟩
  imod dghostVar_alloc (GF := GF) ((0 : Nat), cfgState (GMap.listToSet vs) ∅) with ⟨%gcap, Hcap⟩
  imod dghostVar_alloc (GF := GF) ((0 : Nat), cfgState (GMap.listToSet vs) ∅) with ⟨%gccq, Hccq⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%gcam, Hcam, #Hcamlb⟩
  imod dghostVar_alloc (GF := GF) false with ⟨%glive, Hlive⟩
  imod dghostVar_alloc (GF := GF) ((RaftState.init, W64 0) : RaftState × StateType)
    with ⟨%gdur, Hdur⟩
  imod dghostVar_alloc (GF := GF)
    ((DurMaps.empty, (RaftState.init, W64 0)) : DurMaps × (RaftState × StateType)) with ⟨%gbw, Hbw⟩
  have Hne : vs ≠ [] := by intro h; rw [h] at Hid; cases Hid
  have Hns : γ.raft.reNoSnap = false := Hmr.1.2.2.2.1
  -- `setupNode`: `NewRawNode` (its storage the empty view at the fresh names), `Bootstrap`,
  -- `newNode`
  wp_auto
  wp_apply wp_setupNode γ.raft (γ.mode inferInstance) c cv lok si sn σv hsZero csm
    iprop(Rb ∗ storAuths sn σv) iprop(∃ K, storKeyNames K sn ∗ F K) peers dq pv vs ctxs
    γ.raft.reBoot H1 H2 H3 H4 H5 H6 H7 H8 H9 Happ rfl rfl rfl rfl rfl rfl ⟨rfl, rfl, rfl⟩ Hv Hvo
    Hl Hln Hal rfl rfl Hvs Hne Hnd Hnz (by omega) Hid Hcfg rfl Hbl Hns
    $$ [Hc HRb HA Hpeers Hg]
    as %np ⟨⟨%K, #HKn, HF⟩, %nv, %rn, Hnp, %Hnvrn, Hchans, Hrn, Hpeers⟩
  · iframe Hc Hlg Hpeers Hctx Hmarsh Hcb Hlink
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
    isplitr
    · iintro !> %Φ' !> ⟨HRb, HA⟩ HΦ'
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
      imod Hk $$ %K [] [] with ⟨Hst, Hsh, HF⟩
      · iunfold EtcdGrove.nodeAppliedLb
        ihave H := nodeAppliedLbU_zero (GF := GF) γ K
        iExactEq H; rfl
      · iunfold EtcdGrove.nodeCommitLb
        ihave H := nodeCommitLbU_zero (GF := GF) γ K
        iExactEq H; rfl
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
        icases Hsh with ⟨%e0, %He0, #Hc0, #Hl0, -, Hown, Hend⟩
        unfold ownStorage
        iexists e0
        isplitr
        · iExactEq Hc0; rfl
        isplitr
        · iExactEq Hl0; rfl
        isplitl [Hown]
        · iExactEq Hown; rfl
        isplitl [Hend]
        · iright; iExactEq Hend; rfl
        iframe HA
        ipureintro
        exact ⟨He0, Nat.le_refl _, by simp [StorState.kOut, σv], by simp [StorState.kOut, σv],
          Nat.le_refl _⟩
      iexists K
      iframe HKn HF
    -- the bootstrap state's volatile half, in the cluster's dynamic mode
    rw [Hmd]
    unfold bootInit
    isplitr
    · ipureintro; exact ⟨HD, stOf_simple _⟩
    unfold ownRaftGhostR
    rw [show (rboot (stOf (Membership.simple (GMap.listToSet vs))) γ.raft.reBoot).p =
      bootPState γ.raft.reBoot from rfl]
    iframe Hg
    isplitr
    · ipureintro
      exact RInv_rboot _ _ _ (by have := Hbl.2.1; omega)
    unfold logRecs rboot
    iapply (BigSepL.bigSepL_nil).2; iempintro
  -- the node's ghost state
  imod dghostVar_alloc ((([] : List EntryM), hsZero) : List EntryM × HardStateM) with ⟨%γdlv, Hdlv⟩
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
  imod nodeTab_insert γ N np nv (cfgNamesOf γn) $$ Htab Hnp with ⟨#Hnp, #Hte⟩
  haveI := nodeTabOk_persistent (GF := GF) γ np γn
  ihave #Htb : nodeTabOk (GF := GF) γ np γn $$ []
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
  ihave #Hnode : isNodeChan γn cv.ID' np $$ []
  · unfold isNodeChan
    iexists nv, r, lok'
    simp only [named]
    rw [Hnvrn]
    iframe #
    ipureintro; rfl
  ipersist n
  -- `go n.run()`
  wp_apply wp_fork $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam Hpend Hlive1 Hdur1 Hbw Hfree]
  · wp_apply wp_node_run γn cv.ID' np $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam Hpend Hlive1 Hdur1
      Hbw Hfree]
    · iframe Hnode
      unfold runPre
      iexists nv, _, (([], [], [], hsZero, none) : List EntryM × List EntryM × List EntryM ×
        HardStateM × Option SnapLoan)
      rw [Hnvrn]
      iframe Hnp Hrn Hrof1 Hrof2
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iframe Hdlv1 Htlb1
      iframe Hpend Hlive1 Hdur1 Hfree
      isplitr [Hbw]
      · unfold runCfg
        isplitr
        · ipureintro
          exact ⟨rfl, rfl, fun _ h => by simp at h, rfl⟩
        isplitl [Hdlm]
        · iExactEq Hdlm; rfl
        isplitr
        · simp only [rsDlv]
          iapply dlvKeysAt_nil
        iexists 0
        iframe Hcap1 Hcam
        isplitr
        · ipureintro; exact ⟨Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _)⟩
        iapply undecFree_empty
      iexists _; iexact Hbw
    itrivial
  iapply HΦ
  iexists np, K
  isplitr
  · ipureintro; rfl
  iframe HQ HF Hpeers
  isplitr
  · iunfold EtcdGrove.isNode
    unfold isNode
    iexists γn
    iframe Hnode Htb Hci Hpool
    ipureintro; exact ⟨Hnok, HU⟩
  isplitl [Hdlv2 Hreq1 Hreq2 Hdur2]
  · iunfold EtcdGrove.nodeDriver
    unfold nodeDriver NodeDriverState.init
    iexists γn, cv.ID', []
    isplitr
    · ipureintro; exact ⟨Hnok, rfl, rfl⟩
    isplitr; · iexact Hci
    isplitr; · ihave H := isCommittedLogLb_nil_impl (GF := GF) γ; iExactEq H; rfl
    isplitr; · ipureintro; exact Hdy
    isplitr; · iexact Htb
    isplitr
    · unfold hsCommitted; ileft; ipureintro; rfl
    isplitr; · iexact HKn
    ileft
    isplitr
    · ipureintro; rfl
    iframe Hdur2
    unfold nodeDriverChan dlvLb
    iframe Hnode Hdlv2 Hdlb
    isplitr
    · iapply dlvKeysAt_nil
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
        refine ⟨Hnok, Hdy, ?_⟩
        show CCGood (stOf (Membership.simple (GMap.listToSet vs)))
        rw [stOf_simple]; exact ccGood_cfgState _
      rw [stOf_simple]
      unfold nodeCfg
      iframe Hcap2 Hcamlb
      iexists _
      iframe Hccq1 Hccq2
    unfold confAtU
    iexists [], ∅
    isplitr; · ihave H := isCommittedLogLb_nil_impl (GF := GF) γ; iExactEq H; rfl
    isplitr; · iapply decLb_empty
    ipureintro
    exact ⟨Nat.le_refl _, _, gd, Hmr, rfl⟩
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

theorem StartNode.wp_proof
    (wp_setupNode : setupNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    StartNode.spec (GF := GF) (hG := hG) :=
  ApiImpl.wp_StartNode_impl wp_setupNode wp_node_run

end proof

end EtcdGrove
end Perennial
