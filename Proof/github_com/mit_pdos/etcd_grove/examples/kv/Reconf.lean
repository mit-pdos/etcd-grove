/-
Lean-first (no Rocq counterpart).

# The store over raft's cluster with snapshots and reconfiguration (2026-10-28, stage U4a;
2026-10-30, stage F of the client repair)

What `run`, `New` and `StartCluster` use of the store's cluster (`kvCluster`, `Defs.lean`):

* **The configuration stays the voters'.** The store proposes no conf change (`NormalReqs`), so a
  committed conf entry is raft's empty `ConfChangeV2` (`kv_committed_conf`, `Lemmas.lean`), which
  no simple configuration has (`committed_emptyV2_joint`): no committed entry is a conf entry, and
  every position keeps `kvMembership` (`skippedIn_noConf`, `confAt_skipped`). The positions with
  no conf entry (`NoConfChangeIn`) grow along a log (`noConf_snoc`) and survive extending it
  (`noConf_prefix`). (Until 2026-10-30 the committed conf entries were `RemoveMember`'s of
  non-voters, `rmShrink_notVoter`, `kvMembership_rm`, `kvRule_decide`.)
* **The snapshots' registry** (`kvSnapInv`): allocated empty (`kvSnapInv_alloc`); a snapshot the
  store takes at a committed prefix of the voters' membership, its data the encoded state, is
  recorded, which gives its validity, what `CreateSnapshot` takes (`kv_snap_make`); a
  certificate's snapshot is one of those (`kv_snap_read`). The invariant's contents are timeless
  (raft's `ownSnapsMade_timeless`): opening it spends no later credit.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Storage__InitialState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-! ## Positions without a conf entry -/

theorem noConf_empty (l : List LogEntry) (a : Nat) : NoConfChangeIn l a a := by
  intro k e h1 h2; omega

theorem noConf_prefix (l l' : List LogEntry) (a b : Nat) (h : NoConfChangeIn l a b)
    (hp : l <+: l') (hb : b ≤ l.length) : NoConfChangeIn l' a b := by
  intro k e h1 h2 h3
  apply h k e h1 h2
  obtain ⟨t, rfl⟩ := hp
  rwa [List.getElem?_append_left (by omega)] at h3

theorem noConf_snoc (l : List LogEntry) (a b : Nat) (e : LogEntry) (h : NoConfChangeIn l a b)
    (he : l[b]? = some e) (hc : ¬ e.isConfChange) : NoConfChangeIn l a (b + 1) := by
  intro k e' h1 h2 h3
  by_cases hk : k = b
  · subst hk; rw [he] at h3; cases h3; exact hc
  · exact h k e' h1 (by omega) h3

/-- The last term of a nonempty log, as its terms' list has it. -/
theorem kv_terms_last (l : List LogEntry) (hne : l ≠ []) :
    ∃ t, Option.map LogEntry.term l.getLast? = some t ∧
      (l.map LogEntry.term)[l.length - 1]? = some t := by
  refine ⟨(l.getLast hne).term, ?_, ?_⟩
  · rw [List.getLast?_eq_getLast hne]; rfl
  · have hl : l.length - 1 < l.length := by
      have := List.length_pos_iff.mpr hne; omega
    rw [List.getElem?_map, List.getElem?_eq_getElem hl, List.getLast_eq_getElem]
    rfl

/-! ## The voters' membership -/

/-- A list without repeats is a permutation of the elements of its set. -/
theorem kv_perm_elements_listToSet (l : List w64) (h : l.Nodup) :
    l ≡ₚ GMap.elements (GMap.listToSet l) := by
  refine (List.perm_ext_iff_of_nodup h (GMap.NoDup_elements _)).2 ?_
  intro k; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]

theorem kv_perm_elements_empty : ([] : List w64) ≡ₚ GMap.elements (∅ : GSet w64) := by
  refine (List.perm_ext_iff_of_nodup List.nodup_nil (GMap.NoDup_elements _)).2 ?_
  intro k
  rw [GMap.elem_of_elements]
  simp only [List.not_mem_nil, false_iff]
  exact GMap.not_elem_of_empty _

/-- The `ConfState` of the store's snapshots (the voters) reports the voters' membership. -/
theorem kvConfState_is : confStateIs (kv.kvConfState kvVoters) kvMembership :=
  ⟨kv_perm_elements_listToSet _ (by decide), kv_perm_elements_empty, kv_perm_elements_empty,
    kv_perm_elements_empty, rfl⟩

end pure

section reg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

theorem kvSnapN_raftN : (↑kvRaftN : CoPset) ⊆ ⊤ \ ↑kvSnapN :=
  mask_ndot_ne' nroot "kv_raft" "kv_snaps" (by decide)

/-- **The registry's invariant**, from the allocation's empty registry. -/
theorem kvSnapInv_alloc (γr : RKVNames) (E : CoPset) :
    ⊢ ownSnapsMade (GF := GF) γr.cluster [] ={E}=∗ kvSnapInv γr := by
  iintro Hown
  unfold kvSnapInv
  iapply inv_alloc
  inext
  iexists []
  iframe Hown
  iapply (BigSepL.bigSepL_nil).2; iempintro

/-- **A certificate's snapshot is one the store made**: of a committed prefix of the snapshot's
index, at the membership there (its lists report it, its auto-leave the membership's), its data
the encoded state of the prefix. (Until 2026-10-30 also at the voters' membership with no conf
entry in the prefix: the registry's records are kvreconf's now, `kvSnapRecOk`.) -/
theorem kv_snap_read (γr : RKVNames) (k : SnapTrip) (E : CoPset) (HE : ↑kvSnapN ⊆ E) :
    ⊢ kvCluster (GF := GF) γr -∗ snapshotCert γr.cluster kvRaftN k ={E}=∗
      ∃ (L : List LogEntry) (m : Membership), isCommittedLogLb γr.cluster L ∗
        confAt γr.cluster L.length m ∗
        ⌜L.length = uint.nat k.sid.index' ∧ kvSnapOk L k.dat ∧ k.cl.Is m ∧ k.al = m.autoLeave⌝ := by
  iintro #Hcl #Hcert
  ihave #Hcl' := Hcl
  unfold kvCluster
  icases Hcl' with ⟨#Hc, -, -, #Hinv⟩
  icases snapshotCert_made γr.cluster kvRaftN k $$ [Hc Hcert] with ⟨%l, %m, #Hl, #Ha, #Hmade, %Hp⟩
  · iframe Hc Hcert
  unfold kvSnapInv
  iinv Hinv with >Hb Hclose
  icases Hb with ⟨%S, Hown, #HS⟩
  ihave %Hel := snapMade_elem γr.cluster S _ $$ [Hown Hmade]
  · iframe Hown Hmade
  obtain ⟨j, Hj⟩ := List.getElem?_of_mem Hel
  ihave #Hrec := (BigSepL.bigSepL_lookup (Φ := fun _ s => kvSnapRecOk (GF := GF) γr s) Hj) $$ HS
  unfold kvSnapRecOk
  icases Hrec with ⟨%L, #HL, #HLa, %HLp⟩
  obtain ⟨Hlen, Hok⟩ := HLp
  simp only at Hlen Hok
  imod Hclose $$ [Hown] with -
  · inext
    iexists S
    iframe Hown HS
  imodintro
  iexists L, m
  iframe HL HLa
  ipureintro
  exact ⟨Hlen.trans Hp.1, Hok, Hp.2.2.1, Hp.2.2.2⟩

/-- **Certifying a snapshot the store takes** of the committed prefix `l` (its length `i`, last
term `t`), at the voters' membership, its `ConfState` the voters, its data `d` the encoded state of
`l`: recorded in the store's registry, and so valid (`snapshotCert_valid`), what
`MemoryStorage.CreateSnapshot` takes (`J.SV` of `kvJ`). (Until 2026-10-30 the certificate, with no
conf entry in `l`.) -/
theorem kv_snap_make (γr : RKVNames) (l : List LogEntry) (i t : w64) (d : List w8)
    (Hlen : l.length = uint.nat i) (Hpos : 0 < uint.Z i) (Hi : uint.Z i < 2 ^ 61)
    (Hlast : Option.map LogEntry.term l.getLast? = some t)
    (Hok : SnapListsOk ⟨⟨t, i⟩, (kv.kvConfState kvVoters).lists, false, d⟩)
    (Hd : kvSnapOk l d) :
    ⊢ kvCluster (GF := GF) γr -∗ isCommittedLogLb γr.cluster l -∗
      confAt γr.cluster l.length kvMembership ={⊤}=∗
      snapshotValid γr.cluster (memSnapMade i t (kv.kvConfState kvVoters) d) := by
  iintro #Hcl #Hl #Ha
  unfold kvCluster
  icases Hcl with ⟨#Hc, -, -, #Hinv⟩
  unfold kvSnapInv
  iinv Hinv with >Hb Hclose
  icases Hb with ⟨%S, Hown, #HS⟩
  imod snapshotCert_make γr.cluster kvRaftN (⊤ \ ↑kvSnapN) l i t d kvMembership
      (kv.kvConfState kvVoters) S kvSnapN_raftN Hlen Hlast Hok kvConfState_is
    $$ Hc Hl Ha Hown with ⟨Hown, #Hcert⟩
  imod Hclose $$ [Hown] with -
  · inext
    iexists S ++ [⟨l.length, kvMembership, d⟩]
    iframe Hown
    iapply (BigSepL.bigSepL_snoc (Φ := fun _ s => kvSnapRecOk (GF := GF) γr s)).2
    iframe HS
    unfold kvSnapRecOk
    iexists l
    iframe Hl Ha
    ipureintro
    exact ⟨rfl, Hd⟩
  imodintro
  iapply snapshotCert_valid γr.cluster kvRaftN (memSnapMade i t (kv.kvConfState kvVoters) d) Hpos Hi
  iframe Hc
  simp only [snapTrip, snapId, memSnapMade]
  rw [show (false = kvMembership.autoLeave) from rfl]
  iexact Hcert

end reg

end EtcdGrove
end Perennial
