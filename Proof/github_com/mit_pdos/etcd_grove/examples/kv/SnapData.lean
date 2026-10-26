/-
Lean-first (no Rocq counterpart).

# A snapshot's data, at the replica (D22 S-r, 2026-10-21)

What `run` needs to install and to take a snapshot (`KV__run.lean`), outside the spec/proof
discipline (lemmas on `Base.lean`'s `StateEnc` and raft's predicates):

* the data a replica's state encodes (`stateEnc_intro`: `encodeState`'s bindings of the two
  maps `runOwn` holds encode the replicated state of its client history), and what a
  decoded snapshot gives back (`maps_of_stateEnc`: `decodeState`'s maps are `runOwn`'s of the
  history the data encodes);
* an entry's data fact pins its client datum (`entDataIs_odOf`, `entsDataIs_odOf`: `Base.lean`'s
  `odOf`, which the cluster's certificate `kvSnapOk` reads);
* `Snapshot.GetData` on a snapshot whose pointer fields are all set (`ownSnapS`, what a
  snapshot `Ready` hands out), as raft's `GetData` spec is on `ownSnapM`
  (`wp_Snapshot_GetData_S`; raft's `InvPbSnapSet.lean` has the other two getters,
  `wp_Snapshot_GetMetadata_S` and `wp_SnapshotMetadata_GetIndex_S`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs
public import Proof.go_etcd_io.raft.v3.InvPbSnapSet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The bindings `kvs` and `ops` of a replica's maps `K` and `A` (`encodeState`'s `KVsOf`)
encode the replicated state of the history `H` the maps hold (`runOwn`). -/
theorem stateEnc_intro (H : List (List w8)) (K A : GMap (List w8) (List w8))
    (kvs ops : List (List w8 × List w8))
    (Hval : ∀ k, (K !! k).getD [] = kvFold H k) (HA : AppliedOk A H)
    (HK : KVsOf K kvs) (HO : KVsOf A ops) :
    StateEnc H (encState kvs ops) := by
  refine ⟨kvs, ops, rfl, HK.1, HO.1, fun k => by rw [HK.2 k]; exact Hval k, ?_⟩
  have He : (fun o => ops.lookup o) = (fun o => A !! o) := funext HO.2
  rw [He]; exact HA

/-- What `decodeState` gives back of data that encodes the history `H` (`StateEnc`, at the
bindings `kvs` and `ops`): maps as `runOwn` holds them at `H`. -/
theorem maps_of_stateEnc (H : List (List w8)) (kvs ops : List (List w8 × List w8))
    (K A : GMap (List w8) (List w8))
    (Hk : ∀ k, (kvs.lookup k).getD [] = kvFold H k)
    (Ho : AnsTab (fun o => ops.lookup o) H)
    (HK : ∀ k, K !! k = kvs.lookup k)
    (HAo : ∀ o, A !! o = ops.lookup o) :
    (∀ k, (K !! k).getD [] = kvFold H k) ∧ AppliedOk A H := by
  refine ⟨fun k => by rw [HK k]; exact Hk k, ?_⟩
  have He : (fun o => A !! o) = (fun o => ops.lookup o) := funext HAo
  unfold AppliedOk; rw [He]; exact Ho

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- An entry's data fact pins its client datum. -/
theorem entDataIs_odOf (γ : RaftNames) (e : EntryM) (o : Option (List w8)) :
    entDataIs (GF := GF) γ e o ⊢ ⌜o = odOf e⌝ := by
  cases o with
  | some d =>
    simp only [entDataIs, propDataIs]
    iintro ⟨⟨%Hd, -⟩, -⟩
    ipureintro
    obtain ⟨h1, h2, h3⟩ := Hd
    unfold odOf
    rw [if_pos ⟨h3, by rw [h1]; exact h2⟩, h1]
  | none =>
    simp only [entDataIs, propDataIs]
    iintro (%Hz | %Hc)
    · ipureintro
      unfold odOf
      rw [if_neg (fun h => h.2 Hz.2)]
    · ipureintro
      unfold odOf
      rw [if_neg (fun h => Hc.1 h.1)]

/-- A log's data facts pin its client data. -/
theorem entsDataIs_odOf (γ : RaftNames) (L : List EntryM) (ods : List (Option (List w8))) :
    ([∗list] e;o ∈ L;ods, entDataIs (GF := GF) γ e o) ⊢ ⌜ods = L.map odOf⌝ := by
  induction L generalizing ods with
  | nil =>
    iintro H
    ihave %H := (BigSepL2.bigSepL2_nil_inv_left (Φ := fun _ e o => entDataIs (GF := GF) γ e o)) $$ H
    ipureintro; simp [H]
  | cons e L ih =>
    iintro H
    icases (BigSepL2.bigSepL2_cons_inv_left (Φ := fun _ e o => entDataIs (GF := GF) γ e o)).1 $$ H with ⟨%o, %ods', %Hods, He, H⟩
    ihave %H1 := entDataIs_odOf γ e o $$ He
    ihave %H2 := ih ods' $$ H
    ipureintro
    subst Hods H1 H2
    rfl

end ghost

section getdata
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `Snapshot.GetData` on a snapshot with every pointer field set (`ownSnapS`): its data, lent. -/
theorem wp_Snapshot_GetData_S (p : Loc) (dq : DFrac) (s : SnapshotM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownSnapS p dq s }}
      (App (Val (p @!! go.GoType.PointerType raftpb.Snapshot.ty @!! go!"GetData")) (Val #()))
    {{ (ds : GoSlice), RET #ds;
        ds ↦*{dq} s.Data' ∗ (ds ↦*{dq} s.Data' -∗ ownSnapS p dq s) }} := by
  wp_start as Hs
  iNamed Hs
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  · iapply HΦ
    iframe Hd
    iintro Hd
    iunfold ownSnapS
    iexists ds, pm, uf
    isplitr
    · ipureintro; exact Hnn
    iframe HD Hd HM Hm Hpb

theorem ownSnapS_not_null (p : Loc) (dq : DFrac) (s : SnapshotM) :
    ownSnapS (GF := GF) p dq s ⊢ ownSnapS p dq s ∗ ⌜p ≠ null⌝ := by
  iintro H
  iNamed H
  isplitl
  · iunfold ownSnapS
    iexists ds, pm, uf
    isplitr
    · ipureintro; exact Hnn
    iframe HD Hd HM Hm Hpb
  ipureintro; exact Hnn

end getdata

section pend
variable [GooseExts]

/-- A batch numbered on from the boundary of a storage that holds no entries (one that has just
installed a snapshot) may be handed out (`memStorage_handout`'s premise). -/
theorem pendOk_of_logIndices (σ : StorState) (es : List EntryM) (hne : es ≠ [])
    (hents : σ.ents = []) (H : LogIndicesOk σ.prev es) : PendOk σ es := by
  refine ⟨hne, fun e0 h0 => ?_⟩
  have h0' : es[0]? = some e0 := by rw [List.head?_eq_getElem?] at h0; exact h0
  have H0 := H 0 e0 h0'
  rw [hents]
  simp only [List.length_nil] at H0 ⊢
  push_cast at H0 ⊢
  refine ⟨by omega, by omega, fun k e hk => ?_⟩
  have := H k e hk
  push_cast at this
  omega

theorem pendAbove_of_logIndices (σ : StorState) (es : List EntryM)
    (hfl : uint.Z σ.fl ≤ uint.Z σ.prev.index') (H : LogIndicesOk σ.prev es) : PendAbove σ es := by
  intro e0 h0
  have h0' : es[0]? = some e0 := by rw [List.head?_eq_getElem?] at h0; exact h0
  have H0 := H 0 e0 h0'
  push_cast at H0
  omega

end pend

/-! ### A `Ready`'s data, with or without a snapshot, as `run` reads it

`readyDataL` (raft's `InvNode.lean`) split in what `run` reads of every `Ready` (`rdCommon`: the
entries, the messages, the read states, the indices' bound) and what depends on its snapshot
(`rdSnap`: without one the right to append and a `nil` snapshot; with one, the loan's facts and
the storage). -/

section ready
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

def rdCommon (γ : NodeNames) (rd : Ready) (d ce es : List EntryM) (ms : List QMsg) : IProp GF :=
  iprop(entsRO rd.CommittedEntries' ce ∗ isCommitted γ.raft (d ++ ce) ∗ entsRO rd.Entries' es ∗
    rd.Messages' ↦* ms.map QMsg.loc ∗
    ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γ.raft γ.id q.st ∗
      termLB γ.bud q.st.msg.Term') ∗
    ([∗list] q ∈ ms, rdCred γ.raft (if q.st.msg.Type' = MsgReadIndex then 1 else 0)) ∗
    ([∗list] q ∈ ms, stTks γ.raft q.st) ∗
    (∃ sts : List ReadStateM, readStatesPts rd.ReadStates' sts ∗
      [∗list] st ∈ sts, readStateOk γ.raft st) ∗
    readyIdx γ.raft d ce es)

def rdSnap (γ : NodeNames) (rd : Ready) (d ce es : List EntryM) : Option SnapLoan → IProp GF
  | none => iprop(appendRight γ.stor es ∗ ⌜rd.Snapshot' = null⌝)
  | some l => iprop(ownSnapS l.ptr (DFrac.own (1 : Qp).half) l.snap ∗ isCommitted γ.raft l.dlv ∗
      ⌜l.ptr = rd.Snapshot' ∧ ce = [] ∧ d <+: l.dlv ∧ d.length < l.dlv.length ∧
        l.dlv.length = (uint.Z l.snap.Metadata'.Index').toNat ∧
        0 < uint.Z l.snap.Metadata'.Index' ∧ uint.Z l.snap.Metadata'.Index' < 2^61 ∧
        uint.Z l.fl ≤ uint.Z l.snap.Metadata'.Index' ∧ LogIndicesOk (snapId l.snap) es⌝ ∗
      readyOut γ.stor es (some l))

theorem readyDataL_split (γ : NodeNames) (rd : Ready) (d ce es : List EntryM) (ms : List QMsg)
    (p p' : HardStateM) (L : Option SnapLoan) :
    readyDataL (GF := GF) γ rd d ce es ms p p' L ⊢ rdCommon γ rd d ce es ms ∗ rdSnap γ rd d ce es L := by
  cases L with
  | none =>
    simp only [readyDataL, readyData, rdCommon, rdSnap]
    iintro ⟨#Hce, #Hcomm, #Hes, Happ, Hms, Hmsok, Hcr, Htks, Hsts, -, -, -, %Hsn, #Hidx⟩
    iframe Hce Hcomm Hes Happ Hms Hmsok Hcr Htks Hsts Hidx
    ipureintro; exact Hsn
  | some l =>
    simp only [readyDataL, readySnapData, rdCommon, rdSnap]
    iintro ⟨#Hce, #Hcomm, #Hes, Hms, Hmsok, Hcr, Htks, Hsts, -, -, -, #Hidx, -, Hsn, #Hdl, -, %Hl,
      Hout⟩
    iframe Hce Hcomm Hes Hms Hmsok Hcr Htks Hsts Hidx Hsn Hdl Hout
    ipureintro; exact Hl

end ready

end EtcdGrove
end Perennial
