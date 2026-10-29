/-
(U8 v2, 2026-10-29) **The read triples of raft's view of its storage, derived from the contract**
(`isStorage_of_V`): review 1's "derived contract", so that the log's read proofs (`raftLog.term`,
`slice`, `firstIndex`, `lastIndex`, `snapshot`) keep their shape. Raft's view `σ` and what it holds
for it (`ownStorage sn st σ`) are `InvStorage.lean`'s.

- `LastIndex`: with no batch out raft holds the end.
- `Term(i)`/`Entries(lo, hi)`: below the batch out, over the frozen prefix and the owned part; an
  `ErrCompacted` answer gives `storCompacted`, which the contract's bound (`Hbound`, through
  `raftBnd`) puts at most at `max fl sg`, and `sg ≤ prev.index` (`ownStorage`) at most at `fl`.
- `FirstIndex`: likewise, its answer at most one past `max prev.index fl`.
- `Snapshot`: at or past what raft knows is compacted; a non-empty one valid (`svCert`, the pin).
-/
module

public import Proof.go_etcd_io.raft.v3.InvStorage

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- The frozen prefix and the owned part, joined: the dummy and the physical log below `kOut`. -/
theorem view_pieces_app (σ : StorState) (e0 : EntryM)
    (h1 : uint.nat σ.prev.index' ≤ σ.fr) (h2 : σ.fr + 1 ≤ σ.kOut) :
    (e0 :: σ.ents.take (σ.fr - uint.nat σ.prev.index')) ++
      (σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop (σ.fr - uint.nat σ.prev.index') =
    e0 :: σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1) := by
  rw [List.cons_append]
  congr 1
  have : σ.ents.take (σ.fr - uint.nat σ.prev.index') =
      (σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).take (σ.fr - uint.nat σ.prev.index') := by
    rw [List.take_take]; congr 1; omega
  rw [this, List.take_append_drop]

theorem view_frozen_len (σ : StorState) (e0 : EntryM)
    (h1 : uint.nat σ.prev.index' ≤ σ.fr) (h2 : σ.fr + 1 ≤ σ.kOut)
    (h3 : σ.kOut ≤ uint.nat σ.prev.index' + 1 + σ.ents.length) :
    (e0 :: σ.ents.take (σ.fr - uint.nat σ.prev.index')).length =
      σ.fr + 1 - uint.nat σ.prev.index' := by
  simp only [List.length_cons, List.length_take]; omega

theorem view_owned_len (σ : StorState)
    (h1 : uint.nat σ.prev.index' ≤ σ.fr) (h2 : σ.fr + 1 ≤ σ.kOut)
    (h3 : σ.kOut ≤ uint.nat σ.prev.index' + 1 + σ.ents.length) :
    ((σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop
      (σ.fr - uint.nat σ.prev.index')).length = σ.kOut - 1 - σ.fr := by
  simp only [List.length_drop, List.length_take]; omega

/-- A read below the batch out is below `kOut`. -/
theorem kOut_of_pendFrom (σ : StorState) (n : Int) (Hp : PendFrom σ n)
    (Hn : n ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1) :
    n ≤ (σ.kOut : Int) := by
  unfold StorState.kOut
  cases Hh : σ.pend.head? with
  | none => simp only; have := uint_nat_eq σ.prev.index'; omega
  | some e0 => simp only; have := Hp e0 Hh; have := uint_nat_eq e0.Index'; omega

/-- A term read from the frozen prefix is the view's. -/
theorem termAt_of_frozen (σ : StorState) (e0 : EntryM) (i0 t : w64)
    (He0 : e0.Term' = σ.prev.term') (Hlo : uint.nat σ.prev.index' ≤ uint.nat i0)
    (Hhi : uint.nat i0 ≤ σ.fr)
    (Ht : (fun e : EntryM => e.Term') <$>
      (e0 :: σ.ents.take (σ.fr - uint.nat σ.prev.index'))[uint.nat i0 - uint.nat σ.prev.index']?
        = some t) :
    termAt σ.prev σ.ents i0 = some t := by
  have h1 := uint_nat_eq i0; have h2 := uint_nat_eq σ.prev.index'
  unfold termAt
  by_cases Hb : uint.Z i0 = uint.Z σ.prev.index'
  · rw [if_pos Hb]
    have : uint.nat i0 - uint.nat σ.prev.index' = 0 := by omega
    rw [this] at Ht
    simp only [List.getElem?_cons_zero, Option.map_eq_map, Option.map_some, Option.some.injEq] at Ht
    rw [← Ht, He0]
  · rw [if_neg Hb]
    have : uint.nat i0 - uint.nat σ.prev.index' = (uint.Z i0 - uint.Z σ.prev.index' - 1).toNat + 1 := by
      omega
    rw [this, List.getElem?_cons_succ, List.getElem?_take_of_lt (by omega)] at Ht
    exact Ht

/-- A term read from the owned part is the view's. -/
theorem termAt_of_owned (σ : StorState) (i0 t : w64)
    (Hlo : σ.fr < uint.nat i0) (Hhi : uint.nat i0 < σ.kOut)
    (Hfr : uint.nat σ.prev.index' ≤ σ.fr)
    (Ht : (fun e : EntryM => e.Term') <$>
      ((σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop
        (σ.fr - uint.nat σ.prev.index'))[uint.nat i0 - (σ.fr + 1)]? = some t) :
    termAt σ.prev σ.ents i0 = some t := by
  have h1 := uint_nat_eq i0; have h2 := uint_nat_eq σ.prev.index'
  unfold termAt
  rw [if_neg (by omega)]
  rw [List.getElem?_drop, List.getElem?_take_of_lt (by omega)] at Ht
  have : σ.fr - uint.nat σ.prev.index' + (uint.nat i0 - (σ.fr + 1)) =
      (uint.Z i0 - uint.Z σ.prev.index' - 1).toNat := by omega
  rw [this] at Ht
  exact Ht

/-- What `Entries` returns of the two pieces is a slice of the view's log below `hi`. -/
theorem entries_view (σ : StorState) (e0 : EntryM) (lo hi : w64)
    (H1 : uint.nat σ.prev.index' ≤ σ.fr) (H2 : σ.fr + 1 ≤ σ.kOut)
    (Hlo : uint.nat σ.prev.index' + 1 ≤ uint.nat lo) (Hhi : uint.nat hi ≤ σ.kOut) :
    (((e0 :: σ.ents.take (σ.fr - uint.nat σ.prev.index')) ++
      (σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop (σ.fr - uint.nat σ.prev.index')).drop
        (uint.nat lo - uint.nat σ.prev.index')).take (uint.nat hi - uint.nat lo) =
    (σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
      (uint.Z lo - uint.Z σ.prev.index' - 1).toNat := by
  have h1 := uint_nat_eq lo; have h2 := uint_nat_eq σ.prev.index'; have h3 := uint_nat_eq hi
  rw [view_pieces_app σ e0 H1 H2]
  have : uint.nat lo - uint.nat σ.prev.index' = (uint.Z lo - uint.Z σ.prev.index' - 1).toNat + 1 := by
    omega
  rw [this, List.drop_succ_cons, List.drop_take, List.take_take, List.drop_take]
  congr 1
  omega

end pure

section derive
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The contract's bound, read by raft at its view: a compaction point raft did not cause past `c`
is at most `max fl sg`. -/
theorem view_bound (sn : StorNames) (st : Storage) (σ : StorState) (Bnd : Nat → IProp GF) (c : Nat) :
    ⊢ □ (∀ (c : Nat), storCompacted st c ={⊤}=∗ Bnd c) -∗ □ (∀ (c : Nat), Bnd c -∗ raftBnd sn c) -∗
      storAuths sn σ -∗ storCompacted st c ={⊤}=∗
      storAuths sn σ ∗ ⌜c ≤ uint.nat σ.fl ∨ c ≤ σ.sg⌝ := by
  unfold storAuths raftBnd
  iintro #Hb #Hc ⟨Ha, Hg, Hd⟩ #Hcomp
  imod Hb $$ %c Hcomp with HB
  icases Hc $$ %c HB with ⟨%k, %Hk, (#Hl | #Hl)⟩
  · icases monoNatLbOwn_valid sn.ga 1 _ _ $$ Ha Hl with ⟨%_, %Hle⟩
    imodintro
    iframe Ha Hg Hd
    ipureintro; left; omega
  · icases monoNatLbOwn_valid sn.gg 1 _ _ $$ Hg Hl with ⟨%_, %Hle⟩
    imodintro
    iframe Ha Hg Hd
    ipureintro; right; omega

/-- (U8 v2) The contract's `DL`, read by raft at its view: a valid snapshot at or past the
compaction point raft holds, of index `i` and term `t`, is one whose term raft certified at `i`
(`σ.dt`): the other reading, `i` below a snapshot handed out, is below the compaction point
(`sg ≤ prev.index`). -/
theorem view_dl (sn : StorNames) (σ : StorState) (i : Nat) (t : w64)
    (Hsg : σ.sg ≤ uint.nat σ.prev.index') (Hi : uint.nat σ.prev.index' ≤ i) :
    ⊢ storAuths (GF := GF) sn σ -∗ raftDL sn i t -∗
      storAuths sn σ ∗ ⌜σ.dt.lookup i = some t⌝ := by
  unfold storAuths raftDL
  iintro ⟨Ha, Hg, Hd⟩ (#Hl | ⟨%k, %Hk, #Hl⟩)
  · icases ghost_map_lookup $$ Hd Hl with %Hlk
    iframe Ha Hg Hd
    ipureintro; exact Hlk
  · icases monoNatLbOwn_valid sn.gg 1 _ _ $$ Hg Hl with ⟨%_, %Hle⟩
    exfalso; omega

/-- **The read triples of raft's view, from the contract.** -/
theorem isStorage_of_V (sn : StorNames) (st : Storage) :
    isStorageV (GF := GF) sn st ⊢ isStorage sn st := by
  iintro #HV
  unfold isStorageV
  icases HV with ⟨%SV, %Bnd, %DL, #HP, #Hpin, #HSVp, #Hconv, #Hdl⟩
  unfold isStorageP
  icases HP with ⟨%i, %Hi, #HL, #HT, #HE, #HF, #HS, #Hb, #Hlen⟩
  unfold isStorage isStorageWith
  iexists i
  isplitr
  · ipureintro; exact Hi
  -- LastIndex
  isplitr
  · iintro %σ
    imodintro
    iintro %Φ ⟨Hown, %Hpn⟩ HΦ
    unfold ownStorage
    icases Hown with ⟨%e0, #Hcomp, #HFr, HO, Hend, Hau, %Hw⟩
    icases Hend with (%Hne | Hend)
    · exact absurd Hpn Hne
    wp_apply HL $$ %(uint.nat σ.prev.index' + 1 + σ.ents.length) [$Hend] as %li ⟨Hend, %Hli⟩
    iapply HΦ
    isplitr
    · ipureintro; have := uint_nat_eq li; have := uint_nat_eq σ.prev.index'; omega
    iexists e0
    iframe Hcomp HFr HO Hau
    isplitl [Hend]
    · iright; iexact Hend
    ipureintro; exact Hw
  -- FirstIndex
  isplitr
  · iintro %σ
    imodintro
    iintro %Φ Hown HΦ
    unfold ownStorage
    icases Hown with ⟨%e0, #Hcomp, #HFr, HO, Hend, Hau, %Hw⟩
    iapply wp_fupd
    wp_apply HF $$ %(uint.nat σ.prev.index') [$Hcomp] as %fi ⟨%Hfi, #Hfc⟩
    imod view_bound sn st σ Bnd _ $$ Hb Hconv Hau Hfc with ⟨Hau, %Hle⟩
    imodintro
    iapply HΦ
    have h1 := uint_nat_eq fi; have h2 := uint_nat_eq σ.prev.index'; have h3 := uint_nat_eq σ.fl
    isplitr
    · ipureintro
      obtain ⟨-, -, -, -, Hsg⟩ := Hw
      constructor
      · omega
      · rcases Hle with h | h <;> omega
    isplitr
    · iright
      unfold storCut
      have : (uint.Z fi - 1).toNat = uint.nat fi - 1 := by omega
      rw [this]; iexact Hfc
    iexists e0
    iframe Hcomp HFr HO Hau Hend
    ipureintro; exact Hw
  -- Term
  isplitr
  · iintro %σ %i0 %ec
    imodintro
    iintro %Φ ⟨Hown, %Hr, %Hpf, #Hec⟩ HΦ
    unfold ownStorage
    icases Hown with ⟨%e0, #Hcomp, #HFr, HO, Hend, Hau, %Hw⟩
    obtain ⟨Ht0, H1, H2, H3, H4⟩ := Hw
    have Hk := kOut_of_pendFrom σ _ Hpf (by omega)
    have h1 := uint_nat_eq i0; have h2 := uint_nat_eq σ.prev.index'; have h3 := uint_nat_eq σ.fl
    by_cases Hcase : uint.nat i0 ≤ σ.fr
    · iapply wp_fupd
      wp_apply HT $$ %(uint.nat σ.prev.index') %DFrac.discard
          %(e0 :: σ.ents.take (σ.fr - uint.nat σ.prev.index')) %i0 %ec [$HFr $Hec] as %t %err ⟨-, Hres⟩
      · ipureintro
        rw [view_frozen_len σ e0 H1 H2 H3]
        omega
      icases Hres with (%Hres | ⟨%Herr, #Hc⟩)
      · imodintro
        iapply HΦ
        isplitr
        · ileft; ipureintro
          exact ⟨Hres.1, termAt_of_frozen σ e0 i0 t Ht0 (by omega) Hcase Hres.2⟩
        iexists e0
        iframe Hcomp HFr HO Hau Hend
        ipureintro; exact ⟨Ht0, H1, H2, H3, H4⟩
      · imod view_bound sn st σ Bnd _ $$ Hb Hconv Hau Hc with ⟨Hau, %Hle⟩
        imodintro
        iapply HΦ
        isplitr
        · iright
          isplitr
          · ipureintro; refine ⟨Herr, ?_⟩; rcases Hle with h | h <;> omega
          unfold storCut
          have : (uint.Z i0 + 1).toNat = uint.nat i0 + 1 := by omega
          rw [this]; iexact Hc
        iexists e0
        iframe Hcomp HFr HO Hau Hend
        ipureintro; exact ⟨Ht0, H1, H2, H3, H4⟩
    · iapply wp_fupd
      wp_apply HT $$ %(σ.fr + 1) %(DFrac.own 1)
          %((σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop (σ.fr - uint.nat σ.prev.index'))
          %i0 %ec [$HO $Hec] as %t %err ⟨HO, Hres⟩
      · ipureintro
        rw [view_owned_len σ H1 H2 H3]
        omega
      icases Hres with (%Hres | ⟨%Herr, #Hc⟩)
      · imodintro
        iapply HΦ
        isplitr
        · ileft; ipureintro
          exact ⟨Hres.1, termAt_of_owned σ i0 t (by omega) (by omega) H1 Hres.2⟩
        iexists e0
        iframe Hcomp HFr HO Hau Hend
        ipureintro; exact ⟨Ht0, H1, H2, H3, H4⟩
      · imod view_bound sn st σ Bnd _ $$ Hb Hconv Hau Hc with ⟨Hau, %Hle⟩
        imodintro
        iapply HΦ
        isplitr
        · iright
          isplitr
          · ipureintro; refine ⟨Herr, ?_⟩; rcases Hle with h | h <;> omega
          unfold storCut
          have : (uint.Z i0 + 1).toNat = uint.nat i0 + 1 := by omega
          rw [this]; iexact Hc
        iexists e0
        iframe Hcomp HFr HO Hau Hend
        ipureintro; exact ⟨Ht0, H1, H2, H3, H4⟩
  -- Entries
  isplitr
  · iintro %σ %lo %hi %maxSize %ec
    imodintro
    iintro %Φ ⟨Hown, %Hr, %Hpf, #Hec⟩ HΦ
    unfold ownStorage
    icases Hown with ⟨%e0, #Hcomp, #HFr, HO, Hend, Hau, %Hw⟩
    obtain ⟨Ht0, H1, H2, H3, H4⟩ := Hw
    have Hk := kOut_of_pendFrom σ _ Hpf (by omega)
    have h1 := uint_nat_eq lo; have h2 := uint_nat_eq σ.prev.index'; have h3 := uint_nat_eq hi
    have h4 := uint_nat_eq σ.fl
    have Hlen := view_frozen_len σ e0 H1 H2 H3
    have Hix : uint.nat σ.prev.index' + (e0 :: σ.ents.take (σ.fr - uint.nat σ.prev.index')).length =
        σ.fr + 1 := by rw [Hlen]; omega
    ihave HO : storLog st (uint.nat σ.prev.index' +
        (e0 :: σ.ents.take (σ.fr - uint.nat σ.prev.index')).length) (DFrac.own 1)
        ((σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop (σ.fr - uint.nat σ.prev.index'))
        $$ [HO]
    · rw [Hix]; iexact HO
    iapply wp_fupd
    wp_apply HE $$ %(uint.nat σ.prev.index') %DFrac.discard %(DFrac.own 1)
        %(e0 :: σ.ents.take (σ.fr - uint.nat σ.prev.index'))
        %((σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop (σ.fr - uint.nat σ.prev.index'))
        %lo %hi %maxSize %ec [$HFr $HO $Hec] as %sl %es %err ⟨-, HO, Hres⟩
    · ipureintro
      rw [Hlen, view_owned_len σ H1 H2 H3]
      omega
    ihave HO : storLog st (σ.fr + 1) (DFrac.own 1)
        ((σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop (σ.fr - uint.nat σ.prev.index'))
        $$ [HO]
    · rw [← Hix]; iexact HO
    icases Hres with (⟨%Herr, #Hc⟩ | ⟨%Herr, #Hes, %Hpost⟩)
    · imod view_bound sn st σ Bnd _ $$ Hb Hconv Hau Hc with ⟨Hau, %Hle⟩
      imodintro
      iapply HΦ $$ %sl %es %err
      ileft
      isplitr
      · ipureintro; refine ⟨Herr, ?_⟩; rcases Hle with h | h <;> omega
      isplitr
      · unfold storCut
        have : (uint.Z lo).toNat = uint.nat lo := by omega
        rw [this]; iexact Hc
      iexists e0
      iframe Hcomp HFr HO Hau Hend
      ipureintro; exact ⟨Ht0, H1, H2, H3, H4⟩
    · imodintro
      iapply HΦ $$ %sl %es %err
      iright
      isplitr
      · ipureintro; exact Herr
      iframe Hes
      obtain ⟨Hne, Hcap, Hpre⟩ := Hpost
      rw [entries_view σ e0 lo hi H1 H2 (by omega) (by omega)] at Hpre
      isplitr
      · ipureintro
        refine ⟨Hne, ?_, ?_, Hcap, Hpre⟩
        · have := Hpre.length_le
          simp only [List.length_drop, List.length_take] at this
          omega
        · intro e He
          exact List.mem_of_mem_drop (Hpre.subset He)
      iexists e0
      iframe Hcomp HFr HO Hau Hend
      ipureintro; exact ⟨Ht0, H1, H2, H3, H4⟩
  -- the no-wrap bound
  isplitr
  · iintro !> %σ Hown
    unfold ownStorage
    icases Hown with ⟨%e0, #Hcomp, #HFr, HO, Hend, Hau, %Hw⟩
    obtain ⟨Ht0, H1, H2, H3, H4⟩ := Hw
    icases Hlen $$ %_ %_ %_ HFr with ⟨%Hb1, -⟩
    icases Hlen $$ %_ %_ %_ HO with ⟨%Hb2, HO⟩
    have Hfl := view_frozen_len σ e0 H1 H2 H3
    have Hol := view_owned_len σ H1 H2 H3
    have HkO : σ.kOut ≤ 2^61 := by
      rcases Hb1 with h | h
      · exact absurd h (List.cons_ne_nil _ _)
      rcases Hb2 with h' | h'
      · rw [h', List.length_nil] at Hol; rw [Hfl] at h; omega
      · rw [Hol] at h'; omega
    isplitr
    · ipureintro
      have h2 := uint_nat_eq σ.prev.index'
      constructor
      · intro Hp
        unfold StorState.kOut at HkO
        rw [Hp] at HkO
        simp only [List.head?_nil] at HkO
        omega
      · intro e0' He
        unfold StorState.kOut at HkO
        rw [He] at HkO
        simp only at HkO
        have := uint_nat_eq e0'.Index'
        omega
    iexists e0
    iframe Hcomp HFr HO Hau Hend
    ipureintro; exact ⟨Ht0, H1, H2, H3, H4⟩
  -- Snapshot
  · iintro %σ %esu %n
    imodintro
    iintro %Φ ⟨Hown, #Hesu, #Hn⟩ HΦ
    unfold ownStorage
    icases Hown with ⟨%e0, #Hcomp, #HFr, HO, Hend, Hau, %Hw⟩
    have h2 := uint_nat_eq σ.prev.index'
    ihave #Hc : storCompacted st (max (uint.nat σ.prev.index') n.toNat) $$ []
    · icases Hn with (%Hn | #Hn)
      · rw [Nat.max_eq_left (by omega)]; iexact Hcomp
      · unfold storCut
        by_cases Hle : n.toNat ≤ uint.nat σ.prev.index'
        · rw [Nat.max_eq_left Hle]; iexact Hcomp
        · rw [Nat.max_eq_right (by omega)]; iexact Hn
    iapply wp_fupd
    wp_apply HS $$ %(max (uint.nat σ.prev.index') n.toNat) %esu [$Hc $Hesu] as %snap %err Hres
    icases Hres with (%Hres | ⟨%Herr, %sv, Hsv, %Hix, Hval⟩)
    · imodintro
      iapply HΦ
      isplitl [HO Hend Hau]
      · iexists e0
        iframe Hcomp HFr HO Hau Hend
        ipureintro; exact Hw
      ileft; ipureintro; exact Hres
    icases Hval with (%H0 | ⟨Hv0, HD⟩)
    · imodintro
      iapply HΦ
      isplitl [HO Hend Hau]
      · iexists e0
        iframe Hcomp HFr HO Hau Hend
        ipureintro; exact Hw
      iright
      isplitr
      · ipureintro; exact Herr
      iexists sv
      iframe Hsv
      have h5 := uint_nat_eq sv.Metadata'.Index'
      isplitr
      · ipureintro
        refine ⟨?_, by omega, ?_⟩
        · intro Hc0 H0
          have hz : uint.nat sv.Metadata'.Index' = 0 := by rw [H0]; rfl
          rcases Hc0 with Hc0 | Hc0
          · apply Hc0
            apply uint_Z_inj.1
            have : uint.Z (W64 0) = 0 := rfl
            omega
          · omega
        · by_cases h : n ≤ 0 <;> omega
      ileft; ipureintro; exact H0
    ihave #Hv := HSVp $$ Hv0
    imod Hdl $$ %sv Hv HD with #Hrd
    icases view_dl sn σ _ _ Hw.2.2.2.2 (by omega) $$ Hau Hrd with ⟨Hau, %Hlk⟩
    imodintro
    iapply HΦ
    isplitl [HO Hend Hau]
    · iexists e0
      iframe Hcomp HFr HO Hau Hend
      ipureintro; exact Hw
    iright
    isplitr
    · ipureintro; exact Herr
    iexists sv
    iframe Hsv
    have h5 := uint_nat_eq sv.Metadata'.Index'
    isplitr
    · ipureintro
      refine ⟨?_, by omega, ?_⟩
      · intro Hc0 H0
        have hz : uint.nat sv.Metadata'.Index' = 0 := by rw [H0]; rfl
        rcases Hc0 with Hc0 | Hc0
        · apply Hc0
          apply uint_Z_inj.1
          have : uint.Z (W64 0) = 0 := rfl
          omega
        · omega
      · by_cases h : n ≤ 0 <;> omega
    iright
    isplitr
    · unfold svCert
      iexists SV
      iframe Hpin
      imodintro; iexact Hv
    ipureintro; exact Hlk

end derive

end EtcdGrove
end Perennial
