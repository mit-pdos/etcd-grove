/-
Read-index (2026-10-12): the protocol argument behind a `ReadState`
(notes/decisions.md, "Read-index: a request registry per leader term, acks bounded by
the event history").

* A read context `c` is created by a client, which holds the registry's authority
  (`reReads`), with a committed log `Lc` it knows (`readReq γ c Lc`).
* A `ReadState{Index: i, RequestCtx: c}` carries `readOk γ c i`: `|Lc| ≤ i`.
* At a request's arrival the leader of `T` records `((c, i), d)` (`RqRec`): `d = none`
  with `readOk γ c i` already, or `d = some (t', q)`, the request *doomed*: a quorum `q`
  acknowledged at a term `t' > T` (`doomed`). `ownRaftGhost_read_arrive` decides which,
  from the global committed log's justification.
* A follower `v` answering a heartbeat at `T` is in no doomed record's quorum
  (`ownRaftGhost_not_doomed`: its event history has every acknowledgement at or below its
  term).
* A quorum of such followers confirms a record: it is not doomed (`rqRecOk_confirm`).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.LeaderCompleteness

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF]
variable {md : Bool}

/-! ### Read contexts -/


theorem readReq_agree (γ : RaftNames) (c : List w8) (L1 L2 : List EntryM) :
    ⊢ readReq (GF := GF) γ c L1 -∗ readReq γ c L2 -∗ ⌜L1 = L2⌝ := by
  unfold readReq
  iintro ⟨%q1, #H1, -⟩ ⟨%q2, #H2, -⟩
  ihave %H := ghostMapElem_agree $$ H1 H2
  ipureintro
  exact congrArg Prod.snd H

section inv
variable [InvGS GF]

/-- Firing a read's update with both halves of the commit invariant open. -/
theorem readAu_fire_open (γ : RaftNames) (Qr : List EntryM → IProp GF)
    (l : List EntryM) :
    ⊢ readAu (GF := GF) γ Qr -∗ ghostVar γ.reRLog (1 : Qp).half l
      ={(⊤ \ ↑raftRegN) \ ↑raftLogN}=∗ ghostVar γ.reRLog (1 : Qp).half l ∗ □ Qr l := by
  iintro #Hau Hv
  iapply (fupd_mask_mono (P := iprop(ghostVar (GF := GF) γ.reRLog (1 : Qp).half l ∗ □ Qr l))
    raftN_open_sub)
  iapply readAu_fire γ Qr l $$ Hau Hv

/-- Depositing a read (2026-10-14, stage R; replaces `readReq_alloc`), at `⊤`: the update is
fired at once, at the global committed log `Lc` of the moment, with the invariant open. The
client gets that log -- every committed log it knew (`L0`) is a prefix of it --, the request's
record and its handle. -/
theorem read_deposit (γ : RaftNames) (c : List w8) (Qr : List EntryM → IProp GF)
    (L0 : List EntryM) :
    ⊢ raftCommitInv (GF := GF) γ -∗ rdFresh γ c -∗ readAu γ Qr -∗ isCommitted γ L0 ={⊤}=∗
      ∃ Lc, ⌜L0 <+: Lc⌝ ∗ readReq γ c Lc ∗ isRead γ c Qr := by
  iintro #Hinv Hfr #Hau #HL0
  ihave #Hri := raftCommitInv_reg γ $$ Hinv
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  unfold raftRegInv regsOwn
  iinv Hri with ⟨%l, >Hq2, Hregs⟩ Hclose2
  unfold raftLogInv raftLogInvBody logRest
  iinv Hli with ⟨%P, >HP, >#Hj, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose1
  icases rlq_join γ P l $$ Hq1 Hq2 with ⟨%Heq, Hv⟩
  subst Heq
  iunfold regsAt at Hregs
  icases Hregs with ⟨%R, %RR, Hprops, Hreads, #Hnoop⟩
  iunfold readsReg at Hreads
  icases Hreads with ⟨>Hra, Hs⟩
  ihave Hs := (BigSepM.bigSepM_later).1 $$ Hs
  cases HRc : RR !! c with
  | some r =>
    icases (BigSepM.bigSepM_delete (Φ := fun c r =>
      iprop(▷ (readSlot (GF := GF) γ r P ∗ rdFresh γ c))) HRc).1 $$ Hs
      with ⟨⟨-, >Hfr'⟩, -⟩
    unfold rdFresh
    ihave %Hne := ghostMapElem_ne γ.reRdFresh c c (DFrac.own 1) () () $$ Hfr Hfr'
    exact absurd rfl Hne
  | none =>
  imod readAu_fire_open γ Qr P $$ Hau Hv with ⟨Hv, #HQ⟩
  imod saved_pred_alloc Qr DFrac.discard trivial with ⟨%γq, #Hsp⟩
  imod ghost_map_insert_persist c ((γq, P) : GName × List EntryM) HRc $$ Hra
    with ⟨Hra, #Hel⟩
  ihave #Hslot : readSlot γ (γq, P) P $$ []
  · unfold readSlot
    iexists Qr
    iframe Hsp Hau
    isplitr
    · ipureintro; exact List.prefix_refl _
    imodintro
    iintro %n %Hn
    have : n = P.length := by simp at Hn; omega
    rw [this, List.take_length]
    iexact HQ
  ihave #HcP := ownCommitted_lb γ P $$ HP
  ihave %HL0P := isCommitted_prefix γ L0 P $$ HL0 HP
  icases rlq_split γ P $$ Hv with ⟨Hq1, Hq2⟩
  imod Hclose1 $$ [HP Htbl Hwt Hq1] with -
  · inext
    iexists P
    iframe HP Hj Htbl Hwt Hds Hq1
  imod Hclose2 $$ [Hq2 Hprops Hra Hs Hfr] with -
  · iexists P
    iframe Hq2
    unfold regsAt readsReg
    inext
    iexists R, Std.insert RR c (γq, P)
    iframe Hprops Hnoop Hra
    iapply (BigSepM.bigSepM_insert (Φ := fun c r =>
      iprop(readSlot (GF := GF) γ r P ∗ rdFresh γ c)) HRc).2
    iframe Hslot Hfr
    iexact Hs
  imodintro
  iexists P
  isplitr
  · ipureintro; exact HL0P
  isplitr
  · unfold readReq
    iexists γq
    iframe Hel HcP
  unfold isRead
  iexists γq, P
  iframe Hel Hsp

/-- Collecting (2026-10-14, stage R): a read witness at `i` and a committed log at least `i`
long give the update's result at that log -- it was fired there, the log being the global one
at some commit after the deposit (`|Lc| ≤ i`) --, under the invariant's later and the saved
predicate's. -/
theorem read_collect (γ : RaftNames) (E : CoPset) (c : List w8)
    (Qr : List EntryM → IProp GF) (i : w64) (L : List EntryM) :
    ↑raftN ⊆ E → uint.Z i ≤ (L.length : Int) →
    ⊢ raftCommitInv (GF := GF) γ -∗ readWit γ c Qr i -∗ isCommitted γ L ={E}=∗ ▷ ▷ □ Qr L := by
  intro HE HiL
  iintro #Hinv #Hw #HL
  unfold readWit isRead readOk readReq
  icases Hw with ⟨⟨%γq, %Lc, #Hel, #Hsp⟩, ⟨%Lc', ⟨%γq', #Hel', -⟩, %HLc⟩⟩
  ihave %Hpq := ghostMapElem_agree $$ Hel Hel'
  have HLc' : Lc = Lc' := congrArg Prod.snd Hpq
  subst HLc'
  have Hlen : Lc.length ≤ L.length := by have := HLc; have := HiL; omega
  clear Hpq HLc HiL
  ihave #Hri := raftCommitInv_reg γ $$ Hinv
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  have HE1 := raftRegN_of HE
  unfold raftRegInv regsOwn
  iinv Hri with ⟨%l, >Hq2, Hregs⟩ Hclose2
  have HE2 := raftLogN_of_diff HE
  unfold raftLogInv raftLogInvBody logRest
  iinv Hli with ⟨%P, >HP, >#Hj, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose1
  ihave %Heq := ghostVar_agree γ.reRLog P rlq l rlq $$ Hq1 Hq2
  subst Heq
  ihave %HLP := isCommitted_prefix γ L P $$ HL HP
  iunfold regsAt at Hregs
  icases Hregs with ⟨%R, %RR, Hprops, Hreads, #Hnoop⟩
  iunfold readsReg at Hreads
  icases Hreads with ⟨>Hra, Hs⟩
  icases ghost_map_lookup $$ Hra Hel with %HRc
  ihave Hs := (BigSepM.bigSepM_later).1 $$ Hs
  ihave #Hslot : ▷ readSlot γ (γq, Lc) P $$ [Hs]
  · ihave ⟨⟨#Hsl, -⟩, -⟩ := (BigSepM.bigSepM_delete (Φ := fun c r =>
      iprop(▷ (readSlot (GF := GF) γ r P ∗ rdFresh γ c))) HRc).1 $$ Hs
    iexact Hsl
  imod Hclose1 $$ [HP Htbl Hwt Hq1] with -
  · inext
    iexists P
    iframe HP Hj Htbl Hwt Hds Hq1
  imod Hclose2 $$ [Hq2 Hprops Hra Hs] with -
  · iexists P
    iframe Hq2
    unfold regsAt readsReg
    inext
    iexists R, RR
    iframe Hprops Hnoop Hra
    iexact Hs
  imodintro
  inext
  iunfold readSlot at Hslot
  icases Hslot with ⟨%Qr', #Hsp', #-, %Hpre, #Hres⟩
  have HlenP : L.length ≤ P.length := HLP.length_le
  have Hn : Lc.length ≤ L.length ∧ L.length ≤ P.length := ⟨Hlen, HlenP⟩
  ihave #HQ' := Hres $$ %L.length %Hn
  have HtL : P.take L.length = L := by
    obtain ⟨r, rfl⟩ := HLP; exact List.take_left
  rw [HtL]
  ihave #Heq := saved_pred_agree γq DFrac.discard DFrac.discard Qr' Qr L $$ Hsp' Hsp
  inext
  ihave Hiff := internalEq_iff _ _ $$ Heq
  icases Hiff with ⟨Hiff, -⟩
  imodintro
  iapply Hiff $$ HQ'

end inv
theorem readOk_prefix (γ : RaftNames) (c : List w8) (i : w64) (Lc D : List EntryM) :
    uint.Z i ≤ (D.length : Int) →
    ⊢ readOk (GF := GF) γ c i -∗ readReq γ c Lc -∗ isCommitted γ D -∗ ⌜Lc <+: D⌝ := by
  intro Hle
  unfold readOk
  iintro ⟨%L, #Hr, %HL⟩ #Hr' #HD
  icases readReq_agree γ c L Lc $$ Hr Hr' with %Heq
  subst Heq
  unfold readReq
  icases Hr with ⟨%_, -, #Hc⟩
  icases isCommitted_agree γ L D $$ Hc HD with %Hp
  ipureintro
  rcases Hp with Hp | Hp
  · exact Hp
  · have := Hp.length_le
    have : L.length = D.length := by omega
    exact (Hp.eq_of_length this.symm) ▸ List.prefix_refl _

/-! ### Request records -/


/-- A record whose doom quorum (if any) misses every member of a joint quorum `Q` of a
recorded configuration (the reader's, at confirmation) is not doomed. Since 2026-10-14
(reconfiguration stage B4) the quorums are joint quorums of recorded configurations, and the
static instance has them overlap (`CfgAt.overlap`). B5: the paper's section 8, by cases on the
reader's and the doom fact's configuration indices (the far cases through the doom fact's
witness and at-most-one, `lc_core` at the doom term, I3 at the reader). -/
theorem rqRecOk_confirm (γ : RaftNames) (T : w64) (r : RqRec) (P : List EntryM)
    (c : CfgM) (Q : GSet w64) (Hst : γ.reDyn = none) :
    CfgAt γ P c → JQuorum c Q →
    (∀ v ∈ Q, ∀ t' q, r.2 = some (t', q) → v ∉ q) →
    ⊢ rqRecOk (GF := GF) γ T r -∗ readOk γ r.1.1 r.1.2 := by
  intro HcQ HQ Hw
  rcases h : r.2 with _ | ⟨t', U⟩ <;> simp only [rqRecOk, h]
  · iintro H; iexact H
  · unfold doomed
    iintro ⟨%n, %G, %a, %c', %q, %HqU, #Hcqa, -, -⟩
    icases cqAt_parts γ _ _ _ _ _ _ $$ Hcqa with ⟨%Hpq, -⟩
    obtain ⟨-, -, Hc', Hq'⟩ := Hpq
    obtain ⟨x, Hx1, Hx2⟩ := CfgAt.overlap Hst HcQ Hc' Q q HQ Hq'
    exact absurd (HqU.2.2 x Hx2) (Hw x Hx1 t' U h)

/-- The arrival's choice of the doom fact's witnesses (2026-10-14, stage B5): the union `U` of the
quorums of those of a term above `T` (every member of which acknowledged above `T`). -/
theorem doom_choice (γ : RaftNames) (G : List EntryM) (T tD : w64) : ∀ (m : Nat),
    ⊢ (∀ (k : Nat), ∀ (_ : IsConfPos G k ∧ k < m),
        ∃ (tw nw : w64) (Gw : List EntryM) (aw : w64) (cw : CfgM) (qw : GSet w64),
          ∃ (_ : WitOk G k tw nw Gw aw (uint.Z tD + 1)), cqAt (GF := GF) γ tw nw Gw aw cw qw) -∗
      ∃ U : GSet w64,
        (∀ (u : w64), ∀ (_ : u ∈ U), ∃ (t'' i'' : w64),
          ⌜uint.Z T < uint.Z t'' ∧ 0 < uint.Z i''⌝ ∗ isAcked γ u t'' i'') ∗
        (∀ (k : Nat), ∀ (_ : IsConfPos G k ∧ k < m),
          ∃ (tw nw : w64) (Gw : List EntryM) (aw : w64) (cw : CfgM) (qw : GSet w64),
            ⌜WitOk G k tw nw Gw aw (uint.Z tD + 1) ∧
              (uint.Z T < uint.Z tw → ∀ x, x ∈ qw → x ∈ U)⌝ ∗ cqAt γ tw nw Gw aw cw qw) := by
  intro m
  induction m with
  | zero =>
    iintro #H
    iexists (∅ : GSet w64)
    isplitr
    · iintro %u %hu
      exfalso
      rw [GMap.elem_of_gset, GMap.lookup_empty] at hu
      cases hu
    · iintro %k %hk
      exfalso; have := hk.2; omega
  | succ m ih =>
    iintro #H
    icases ih $$ [] with ⟨%U0, #HU0, #HW0⟩
    · iintro %k %Hk
      iapply H $$ %k %(⟨Hk.1, by omega⟩ : IsConfPos G k ∧ k < m + 1)
    by_cases hp : IsConfPos G m
    · ihave Hwm := H $$ %m %(⟨hp, by omega⟩ : IsConfPos G m ∧ m < m + 1)
      icases Hwm with ⟨%tw, %nw, %Gw, %aw, %cw, %qw, %Hwo, #Hcqw⟩
      icases cqAt_parts γ tw nw Gw aw cw qw $$ Hcqw with ⟨-, -, -, #Hackw, -⟩
      iexists (if uint.Z T < uint.Z tw then U0 ∪ qw else U0)
      isplitr
      · iintro %u %hu
        by_cases hT : uint.Z T < uint.Z tw
        · rw [ite_eq_left hT] at hu
          rcases (GMap.elem_of_union u U0 qw).1 hu with h | h
          · iapply HU0 $$ %u %h
          · ihave ⟨%i', %Hi', #Ha⟩ := BigSepM.bigSepM_lookup
              (Φ := fun v _ => iprop(∃ i', ⌜uint.Z nw ≤ uint.Z i'⌝ ∗ isAcked (GF := GF) γ v tw i'))
              ((GMap.elem_of_gset _ _).mp h) $$ Hackw
            iexists tw, i'
            iframe Ha
            ipureintro; exact ⟨hT, by have := Hwo.2.1; omega⟩
        · rw [ite_eq_right hT] at hu
          iapply HU0 $$ %u %hu
      · iintro %k %Hk
        by_cases hkm : k = m
        · subst hkm
          iexists tw, nw, Gw, aw, cw, qw
          iframe Hcqw
          ipureintro
          refine ⟨Hwo, fun hT x hx => ?_⟩
          rw [ite_eq_left hT]; exact GMap.elem_of_union_r _ hx
        · ihave Hw := HW0 $$ %k %(⟨Hk.1, by omega⟩ : IsConfPos G k ∧ k < m)
          icases Hw with ⟨%tw', %nw', %Gw', %aw', %cw', %qw', %Hwo', #Hc'⟩
          iexists tw', nw', Gw', aw', cw', qw'
          iframe Hc'
          ipureintro
          refine ⟨Hwo'.1, fun hT x hx => ?_⟩
          have hx' := Hwo'.2 hT x hx
          split
          · exact GMap.elem_of_union_l _ hx'
          · exact hx'
    · iexists U0
      iframe HU0
      iintro %k %Hk
      have hkm : k < m := by
        rcases Nat.lt_or_ge k m with h | h
        · exact h
        · exfalso; have : k = m := by have := Hk.2; omega
          subst this; exact hp Hk.1
      iapply HW0 $$ %k %(⟨Hk.1, hkm⟩ : IsConfPos G k ∧ k < m)

/-- A commit fact of a term above `T`, at a nonzero index, dooms a record (the arrival's case
split): its quorum and, in the dynamic mode, its witnesses' of terms above `T`. -/
theorem doomed_intro (γ : RaftNames) (T t n : w64) (G : List EntryM) (a : w64) (c : CfgM)
    (q : GSet w64) :
    uint.Z T < uint.Z t → 0 < uint.Z n →
    ⊢ cqAt (GF := GF) γ t n G a c q -∗ ∃ U, doomed γ T t U := by
  intro HT Hn
  iintro #Hc
  icases cqAt_parts γ t n G a c q $$ Hc with ⟨%Hp, -, -, #Hacks, #Hd⟩
  ihave #Hq : (∀ (u : w64), ∀ (_ : u ∈ q), ∃ (t'' i'' : w64),
      ⌜uint.Z T < uint.Z t'' ∧ 0 < uint.Z i''⌝ ∗ isAcked (GF := GF) γ u t'' i'') $$ []
  · iintro %u %hu
    ihave ⟨%i', %Hi', #Ha⟩ := BigSepM.bigSepM_lookup
      (Φ := fun v _ => iprop(∃ i', ⌜uint.Z n ≤ uint.Z i'⌝ ∗ isAcked (GF := GF) γ v t i'))
      ((GMap.elem_of_gset _ _).mp hu) $$ Hacks
    iexists t, i'
    iframe Ha
    ipureintro; exact ⟨HT, by omega⟩
  cases hD : γ.reDyn with
  | none =>
    iexists q
    unfold doomed
    iexists n, G, a, c, q
    iframe Hc Hq
    isplitr
    · ipureintro; exact ⟨HT, Hn, fun x hx => hx⟩
    · iapply dynOn_static γ _ hD
  | some D' =>
    have Hdyn : γ.reDyn ≠ none := by rw [hD]; simp
    ihave #Hd' := dynOn_elim γ _ Hdyn $$ Hd
    iunfold cqDyn at Hd'
    icases Hd' with ⟨-, #Hwit⟩
    icases doom_choice γ G T t (uint.Z a).toNat $$ Hwit with ⟨%U0, #HU0, #HW0⟩
    iexists (U0 ∪ q)
    unfold doomed
    iexists n, G, a, c, q
    iframe Hc
    isplitr
    · ipureintro; exact ⟨HT, Hn, fun x hx => GMap.elem_of_union_r _ hx⟩
    isplitr
    · iintro %u %hu
      rcases (GMap.elem_of_union u U0 q).1 hu with h | h
      · iapply HU0 $$ %u %h
      · iapply Hq $$ %u %h
    · unfold dynOn
      iright
      iintro %k %Hk
      ihave Hw := HW0 $$ %k %Hk
      icases Hw with ⟨%tw, %nw, %Gw, %aw, %cw, %qw, %Hwo, #Hcw⟩
      iexists tw, nw, Gw, aw, cw, qw
      iframe Hcw
      ipureintro
      exact ⟨Hwo.1, fun hT x hx => GMap.elem_of_union_l _ (Hwo.2 hT x hx)⟩

section inv
variable [InvGS GF]

/-- An index of a log past the leader's campaign log `l0` is in the leader's term-log authority
`M`, hence at most `L` (2026-10-16, stage R8a): the index `z` (in range of `w64`) names an entry of
`l` past `l0`, which has a fragment of `γt` (`leadFrags`). -/
private theorem leadFrags_idx_le (γt : GName) (M : GMap w64 (EntryM × w64)) (l0 l : List EntryM)
    (b : entryID) (L z : Int) :
    PlogWfR b l → (∀ i, (M !! i).isSome → uint.Z i ≤ L) →
    uint.Z b.index' + (l0.length : Int) < z → z ≤ plogLastIndexZ b l → z < 2 ^ 64 →
    ⊢ ghostMapAuth (GF := GF) γt 1 M -∗ leadFrags γt l0 l -∗ ⌜z ≤ L⌝ := by
  intro Hwf Hdom Hz0 Hzl Hz64
  iintro Ha #Hlf
  unfold leadFrags
  have HbZ := uint_Z_nonneg b.index'
  unfold plogLastIndexZ at Hzl
  obtain ⟨e, He⟩ : ∃ e, l[(z - uint.Z b.index' - 1).toNat]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  ihave He' := BigSepL.bigSepL_lookup (Φ := fun k e => if l0.length ≤ k then
      iprop(∃ pt : w64, e.Index' ↪[γt]□ ((e, pt) : EntryM × w64)) else iprop(True)) He
    $$ Hlf
  rw [ite_eq_left (show l0.length ≤ (z - uint.Z b.index' - 1).toNat by omega)]
  icases He' with ⟨%pt, He'⟩
  icases ghost_map_lookup $$ Ha He' with %HM
  have Hd := Hdom _ (by rw [HM]; rfl)
  have Hw := Hwf _ _ He (by omega)
  ipureintro; omega

/-- A log of the leader of `s.term` (`leadPrefix`) is within the leader's own log (2026-10-16,
stage R8a, D11; the core of `ownLogGhost_within`, which takes the full log): the prefix names
the leader's own term log (`isTermLog` against `leadLogOwn`'s entry), whose fragments are all in
the leader's term-log authority `M`, and nothing in `M` is past the leader's last index. Bounded
at `2 ^ 64 - 1` because `leadPrefix` has only `PlogWfR` (the entries' indices in range). The ghost
state is handed back. -/
theorem ownLogGhost_prefix_within (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64)
    (ldr : w64) (bL : entryID) (l : List EntryM) :
    s.role = .leader →
    ⊢ isLeader (GF := GF) γ id s.term -∗ leadPrefix γ ldr s.term bL l -∗ ownLogGhost γ id s kl -∗
      ⌜min (plogLastIndexZ bL l) (2 ^ 64 - 1) ≤ plogLastIndexZ s.base s.log⌝ ∗
      ownLogGhost γ id s kl := by
  intro Hr
  unfold ownLogGhost
  iintro #Hl #Hp H
  icases H with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  ihave Hres : iprop(⌜min (plogLastIndexZ bL l) (2 ^ 64 - 1) ≤ plogLastIndexZ s.base s.log⌝ ∗
      leadLogOwn γ s terms ∗ ghostMapAuth γm 1 terms) $$ [Hterms Htlog]
  · unfold leadPrefix isTermLog
    unfold leadLogOwn
    rw [Hr]
    icases Htlog with ⟨%γt, %M, %l0, %Hγt, Ha, #Hfr, %Hdom, %Hpre, #Hlf⟩
    icases Hp with ⟨#Hl', %γt', %l0', ⟨%γm', %Hγm', #Htf⟩, %Hwr', -, #Hlf'⟩
    icases isLeader_unique γ id ldr s.term $$ Hl Hl' with %Hid
    subst Hid
    rw [Htname] at Hγm'
    cases Hγm'
    ihave %Hlook := ghost_map_lookup $$ Hterms Htf
    rw [Hγt] at Hlook
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (γt = γt' ∧ s.base = bL) ∧ l0 = l0' := by simpa using Hlook
    obtain ⟨HwR, -⟩ := Hwr'
    have Hl0 := Hpre.length_le
    have HbZ := uint_Z_nonneg s.base.index'
    have Hb64 := uint_Z_lt s.base.index'
    ihave %Hle : ⌜min (plogLastIndexZ s.base l) (2 ^ 64 - 1) ≤ plogLastIndexZ s.base s.log⌝
        $$ [Ha]
    · by_cases Hcase : min (plogLastIndexZ s.base l) (2 ^ 64 - 1) ≤
          uint.Z s.base.index' + (l0.length : Int)
      · ipureintro; unfold plogLastIndexZ at Hcase ⊢; omega
      · iapply leadFrags_idx_le γt M l0 l s.base (plogLastIndexZ s.base s.log)
          (min (plogLastIndexZ s.base l) (2 ^ 64 - 1)) HwR Hdom
          (by unfold plogLastIndexZ at Hcase ⊢; omega) (by unfold plogLastIndexZ at *; omega)
          (by unfold plogLastIndexZ at *; omega) $$ Ha Hlf'
    isplitr
    · ipureintro; exact Hle
    iframe Hterms
    iexists γt, M, l0
    iframe Ha Hfr Hlf
    ipureintro; exact ⟨Hγt, Hdom, Hpre⟩
  icases Hres with ⟨%Hle, Htlog, Hterms⟩
  isplitr
  · ipureintro; exact Hle
  iexists γm, terms, γa, acks, fp, γc, camps, γl, vlogs, γw, wins
  iframe % # ∗

/-- A leader's current log is at least as long as every log of its term (`leadFull`): the
entries it created are in its term log, whose indices are within its log
(`leadLogOwn`). -/
theorem ownLogGhost_within (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64)
    (G : List EntryM) :
    s.role = .leader →
    ⊢ isLeader (GF := GF) γ id s.term -∗ leadFull γ s.term G -∗ ownLogGhost γ id s kl -∗
      ⌜plogLastIndexZ base0 G ≤ plogLastIndexZ s.base s.log⌝ := by
  intro Hr
  iintro #Hl #HG H
  unfold leadFull
  icases HG with ⟨%ldr, %bL, %l, %fpG, #Hp, #Hpf, %HG⟩
  subst HG
  unfold lpfull
  icases Hpf with ⟨%F0, -, -, %HfG⟩
  obtain ⟨HfG, -, HwG, -⟩ := HfG
  icases ownLogGhost_prefix_within γ id s kl ldr bL l Hr $$ Hl Hp H with ⟨%Hle, -⟩
  ipureintro
  rw [full_last_index _ _ _ HfG]
  -- the log's last index is in range (`PlogWf`: its last entry's index is a `w64`)
  have Hb64 := uint_Z_lt bL.index'
  have HL : plogLastIndexZ bL l < 2 ^ 64 := by
    unfold plogLastIndexZ
    cases hl : l with
    | nil => simp; omega
    | cons e0 l' =>
      obtain ⟨e, He⟩ : ∃ e, (e0 :: l')[l'.length]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by simp)⟩
      have := HwG l'.length e (by rw [hl]; exact He)
      have := uint_Z_lt e.Index'
      simp only [List.length_cons]; push_cast at *; omega
  omega

/-- What a leader has: its full log, with records, which extends its campaign log and is
a `leadFull` of its term; and every log of its term is within it. -/
theorem node_leader (γ : RaftNames) (id2 : w64) (ps2 : PState) :
    ps2.role = .leader →
    ⊢ ownRaftGhost (GF := GF) γ id2 ps2 md -∗
      ∃ fp2 F0, ⌜FullOk ps2.base fp2 ∧ PlogWf ps2.base ps2.log ∧
                  F0 <+: fp2 ++ ps2.log⌝ ∗
        logRecs γ base0 fp2 ∗ logRecs γ ps2.base ps2.log ∗
        isLeader γ id2 ps2.term ∗ isCamp γ id2 ps2.term F0 ∗
        leadFull γ ps2.term (fp2 ++ ps2.log) := by
  intro Hr2
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  have Hw : leaderWit (GF := GF) γ id2 ps2 = isLeader γ id2 ps2.term := by
    unfold leaderWit; rw [Hr2]
  rw [Hw]
  icases ownLogGhost_lead_full γ id2 ps2 kl Hr2 $$ Hlead Hlg with ⟨⟨%fp, #Hp, #Hpf, -⟩, Hlg⟩
  icases ownLogGhost_recs γ id2 ps2 kl $$ Hlg with ⟨-, #Hr⟩
  ihave #HLF := leadFull_intro γ id2 ps2.term ps2.base ps2.log fp $$ Hp Hpf
  unfold lpfull
  icases Hpf with ⟨%F0, #Hc0, #Hfr, %Hf⟩
  obtain ⟨Hf, Hpre, Hw, -⟩ := Hf
  iexists fp, F0
  isplitr; · ipureintro; exact ⟨Hf, Hw, Hpre⟩
  iframe Hfr Hr Hlead Hc0 HLF

theorem node_within (γ : RaftNames) (id2 : w64) (ps2 : PState) (G : List EntryM) :
    ps2.role = .leader →
    ⊢ ownRaftGhost (GF := GF) γ id2 ps2 md -∗ leadFull γ ps2.term G -∗
      ⌜plogLastIndexZ base0 G ≤ plogLastIndexZ ps2.base ps2.log⌝ := by
  intro Hr2
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩ #HG
  iNamed H
  have Hw : leaderWit (GF := GF) γ id2 ps2 = isLeader γ id2 ps2.term := by
    unfold leaderWit; rw [Hr2]
  rw [Hw]
  iapply ownLogGhost_within γ id2 ps2 kl G Hr2 $$ Hlead HG Hlg

/-- A record whose doom set misses every member of a joint quorum `Q` of the reader's
configuration (its full log's prefix at its configuration index `aL`) is not doomed, in the
dynamic mode (2026-10-14, stage B5; the paper's section 8). With `j_r` the reader's and `j_m` the
doom fact's configuration indices: adjacent, `Q` meets the doom quorum; `j_r ≥ j_m + 2`, the
reader's witness of its conf entry `j_m + 1` (0-based, `W`) is in the doom term's campaign log
(`lc_core` at the doom term), so the doom fact's log has two conf entries past its index, against
its I1 (repair 4); `j_r ≤ j_m - 2`, the doom fact's witness of its conf entry `j_r + 1`: of a term
above `T`, `Q` meets its quorum (recorded in the doom set); at most `T`, its log is in the reader's
(`lc_core` at `T`, or the reader's own log of `T`), two conf entries past the reader's
configuration index, against I3 at the reader. -/
theorem rqRecOk_confirm_dyn (γ : RaftNames) (T L : w64) (r : RqRec) (FL F0L : List EntryM)
    (aL cL : w64) (c : CfgM) (Q : GSet w64) (Hdyn : γ.reDyn ≠ none) (Y : IProp GF)
    (HLw : ∀ G, ⊢ Y -∗ leadFull γ T G -∗ ⌜plogLastIndexZ base0 G ≤ plogLastIndexZ base0 FL⌝) :
    CfgAt γ (FL.take (uint.Z aL).toNat) c → JQuorum c Q →
    confCount (FL.drop (uint.Z aL).toNat) ≤ 1 → uint.Z aL ≤ uint.Z cL → PlogWf base0 FL →
    CampOk T F0L → F0L <+: FL →
    (∀ v ∈ Q, ∀ t' q, r.2 = some (t', q) → v ∉ q) →
    ⊢ votesTbl (GF := GF) γ -∗ isLeader γ L T -∗ isCamp γ L T F0L -∗ logRecs γ base0 FL -∗
      isCommitted γ (FL.take (uint.Z aL).toNat) -∗ commitIn γ FL cL T -∗ leadFull γ T FL -∗
      Y -∗ rqRecOk γ T r -∗ readOk γ r.1.1 r.1.2 := by
  intro HcQ HQ HI3 HaL HwFL Hcok Hpre Hw
  iintro HS #Hl #Hc #HrFL #HcFL #HcmL #HflL HY
  rcases h : r.2 with _ | ⟨tD, U⟩ <;> simp only [rqRecOk, h]
  · iintro H; iexact H
  unfold doomed
  iintro ⟨%nD, %GD, %aD, %cD, %qD, %HD, #HcqD, -, #HdW⟩
  iexfalso
  icases cqAt_parts γ tD nD GD aD cD qD $$ HcqD with ⟨%Hp, #HflD, #HcGD, -, #HdD⟩
  ihave #HdD' := dynOn_elim γ _ Hdyn $$ HdD
  iunfold cqDyn at HdD'
  icases HdD' with ⟨%HI1D, -⟩
  ihave #HdW' := dynOn_elim γ _ Hdyn $$ HdW
  ihave #HcqD' := cqAt_cq γ _ _ _ _ _ _ $$ HcqD
  icases cq_full γ tD nD GD $$ HcqD' with ⟨%HwGD, #HrGD⟩
  icases isCommitted_agree γ _ _ $$ HcGD HcFL with %Hpre2
  by_cases Hadj : confCount (GD.take (uint.Z aD).toNat) ≤ confCount (FL.take (uint.Z aL).toNat) + 1 ∧
      confCount (FL.take (uint.Z aL).toNat) ≤ confCount (GD.take (uint.Z aD).toNat) + 1
  · obtain ⟨x, hx1, hx2⟩ := CfgAt.overlap_adj Hpre2 Hadj.2 Hadj.1 Hp.2.2.1 HcQ qD Q Hp.2.2.2 HQ
    ipureintro
    exact absurd (HD.2.2 x hx1) (Hw x hx2 tD U h)
  rcases (by omega : confCount (GD.take (uint.Z aD).toNat) + 2 ≤ confCount (FL.take (uint.Z aL).toNat) ∨
      confCount (FL.take (uint.Z aL).toNat) + 2 ≤ confCount (GD.take (uint.Z aD).toNat)) with Hfar | Hfar
  · -- the reader is newer: its witness, in the doom term's campaign log
    obtain ⟨p, hp, hpc, hpcc⟩ :=
      exists_confPos FL (uint.Z aL).toNat (confCount (GD.take (uint.Z aD).toNat) + 1) (by omega)
    ihave #HwL := commitIn_w γ FL cL T Hdyn $$ HcmL
    iunfold witsB at HwL
    ihave Hw2 := HwL $$ %p %(⟨hpc, by omega⟩ : IsConfPos FL p ∧ p < (uint.Z cL).toNat)
    icases Hw2 with ⟨%tw, %nw, %Gw, %aw, %cw, %qw, %Hwo, #Hcqw⟩
    ihave #Hcqw' := cqAt_cq γ _ _ _ _ _ _ $$ Hcqw
    icases cq_full γ tw nw Gw $$ Hcqw' with ⟨%HwGw, #HrGw⟩
    icases cq_base γ tw nw Gw $$ Hcqw' with ⟨%HGwn, -⟩
    icases leadFull_camp γ tD GD $$ HflD with ⟨%ldr, %F0D, #HlD, #HcD, %HpreD⟩
    icases isCamp_ok γ ldr tD F0D $$ HcD with %HcokD
    icases lc_core γ ((uint.Z tD).toNat + 1) tD tw nw Gw ldr F0D GD (by omega)
      (by have := Hwo.1; have := HD.1; omega) HwGD (prefix_camp_last tD F0D GD HcokD HpreD)
      $$ HS Hcqw' HlD HcD HrGD with %HGDnw
    icases full_take_eq γ Gw GD nw HwGw HwGD (by rw [HGwn]; rfl) (by rw [HGwn, HGDnw])
      $$ HrGw HrGD with %Htk
    ipureintro
    refine far_older HI1D ?_ hpc hpcc
    rw [take_agree_le Htk.symm (by have := Hwo.2.1; omega), Hwo.2.2.2.1]
  · -- the reader is older: the doom fact's witness
    obtain ⟨p, hp, hpc, hpcc⟩ :=
      exists_confPos GD (uint.Z aD).toNat (confCount (FL.take (uint.Z aL).toNat) + 1) (by omega)
    ihave Hw2 := HdW' $$ %p %(⟨hpc, hp⟩ : IsConfPos GD p ∧ p < (uint.Z aD).toNat)
    icases Hw2 with ⟨%tw, %nw, %Gw, %aw, %cw, %qw, %Hwo, #Hcqw⟩
    obtain ⟨Hwo1, HwU⟩ := Hwo
    icases cqAt_parts γ tw nw Gw aw cw qw $$ Hcqw with ⟨%Hpw, #HflW, #HcGw, -, -⟩
    ihave #Hcqw' := cqAt_cq γ _ _ _ _ _ _ $$ Hcqw
    icases cq_full γ tw nw Gw $$ Hcqw' with ⟨%HwGw, #HrGw⟩
    have Hcw : confCount (Gw.take (uint.Z aw).toNat) = confCount (FL.take (uint.Z aL).toNat) + 1 := by
      rw [Hwo1.2.2.2.2, hpcc]
    by_cases HtwT : uint.Z T < uint.Z tw
    · icases isCommitted_agree γ _ _ $$ HcGw HcFL with %Hpre3
      obtain ⟨x, hx1, hx2⟩ := CfgAt.overlap_adj Hpre3 (by omega) (by omega) Hpw.2.2.1 HcQ qw Q
        Hpw.2.2.2 HQ
      ipureintro
      exact absurd (HwU HtwT x hx1) (Hw x hx2 tD U h)
    · ihave %HFLnw : ⌜plogTermAt base0 FL nw = some tw⌝ $$ [HS HY]
      · by_cases HtwT' : uint.Z tw < uint.Z T
        · iapply lc_core γ ((uint.Z T).toNat + 1) T tw nw Gw L F0L FL (by omega) HtwT' HwFL
            (prefix_camp_last T F0L FL Hcok Hpre) $$ HS Hcqw' Hl Hc HrFL
        · have Hte : tw = T := uint_Z_inj.mp (by omega)
          subst Hte
          ihave %Hlen := HLw Gw $$ HY HflW
          have HsGw : (plogTermAt base0 Gw nw).isSome := by rw [Hpw.1]; rfl
          have HsFL : (plogTermAt base0 FL nw).isSome := by
            apply plogTermAt_in_range
            have := (plogTermAt_some_range _ _ _ _ Hpw.1).2
            refine ⟨by rw [base0_index]; exact uint_Z_nonneg _, by omega⟩
          icases leadFull_agree γ tw Gw FL nw HsGw HsFL $$ HflW HflL with %Hag
          ipureintro; rw [← Hag]; exact Hpw.1
      icases full_take_eq γ Gw FL nw HwGw HwFL (by rw [Hpw.1]; rfl) (by rw [Hpw.1, HFLnw])
        $$ HrGw HrFL with %Htk
      ipureintro
      refine far_older (ConfI1_of_drop HI3) ?_ hpc hpcc
      rw [take_agree_le Htk.symm (by have := Hwo1.2.1; omega), Hwo1.2.2.2.1]


/-- A campaign's term is nonzero: its log's terms are all below it, the boundary's
term `0` (at index `0`) among them. -/
theorem CampOk.term_nz {T : w64} {F : List EntryM} (H : CampOk T F) : T ≠ W64 0 := by
  intro hT
  have h0 : plogTermAt base0 F (W64 0) = some (W64 0) := by
    simp [plogTermAt, base0]
  have := H.2 _ _ h0
  rw [hT] at this
  exact Int.lt_irrefl _ this

/-- A candidate's or a leader's term is nonzero (2026-10-10): it holds the record of its
campaign at that term (`campOwn`), and a campaign does not wrap the term (`CampOk`).
`Step` gives a leader's to `appendEntry` (through `stepLeader`), which stamps the
self-acknowledgement with it: `RawNode.Advance` steps that message, and `Step` asks a
`MsgAppResp` for a nonzero term. -/
theorem ownRaftGhost_term_nz (γ : RaftNames) (id : w64) (s : PState) :
    s.role ≠ .follower →
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ ⌜s.term ≠ W64 0⌝ := by
  intro Hr
  unfold ownRaftGhost ownLogGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  icases Hlg with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  unfold campOwn at *
  cases Hrole : s.role with
  | follower => exact absurd Hrole Hr
  | candidate =>
    rw [Hrole] at *
    ihave %Hc := isCamp_ok γ id s.term _ $$ Hcown
    ipureintro; exact Hc.term_nz
  | leader =>
    rw [Hrole] at *
    icases Hcown with ⟨%F0, #Hc0, -⟩
    ihave %Hc := isCamp_ok γ id s.term _ $$ Hc0
    ipureintro; exact Hc.term_nz

/-! ### Followers: no acknowledgement above their term -/

theorem ownRaftGhost_ack_le (γ : RaftNames) (v : w64) (s : PState) (t i : w64) :
    ⊢ ownRaftGhost (GF := GF) γ v s md -∗ ackEv γ v t i -∗ ⌜uint.Z t ≤ uint.Z s.term⌝ := by
  unfold ownRaftGhost ownLogGhost ownEvs ackEv
  iintro ⟨%γv, %voted, %kl, H⟩ ⟨%γe', %L, %HL, #Hlb⟩
  iNamed H
  icases Hlg with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  icases Hevs with ⟨%γe, %evs, %Hγe, Ha, %Hevs⟩
  obtain ⟨Hγe', Hin, -⟩ := HL
  rw [Hγe] at Hγe'; cases Hγe'
  icases mono_list_auth_lb_valid $$ Ha Hlb with %Hp
  ipureintro
  have := Hevs.2.1 _ (Hp.2.subset Hin)
  simpa [aevTerm] using this

/-- A node at term `T` is in no quorum that dooms a record of `T`. -/
theorem ownRaftGhost_not_doomed (γ : RaftNames) (v : w64) (s : PState) (r : RqRec) :
    ⊢ ownRaftGhost (GF := GF) γ v s md -∗ rqRecOk γ s.term r -∗
      ⌜∀ t' q, r.2 = some (t', q) → v ∉ q⌝ := by
  iintro Hown #Hr
  rcases h : r.2 with _ | ⟨t', q⟩ <;> simp only [rqRecOk, h]
  · ipureintro; intro t' q h'; cases h'
  · unfold doomed
    icases Hr with ⟨%n, %G, %a, %c, %q', %Hpq, -, #HU, -⟩
    by_cases hv : v ∈ q
    · ihave ⟨%t'', %i'', %Hti, #Ha⟩ := HU $$ %v %hv
      unfold isAcked
      icases Ha with (%H0 | ⟨-, #Hev⟩)
      · exfalso; have := Hti.2; omega
      · ihave %Hle := ownRaftGhost_ack_le γ v s t'' i'' $$ Hown Hev
        exfalso; have := Hti.1; omega
    · ipureintro
      intro t'' q' hh
      cases hh
      exact hv

/-! ### Arrival at the leader -/

/-- The persistent facts of a node's log state the arrival needs. -/
theorem ownLogGhost_commitIn (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗
      ∃ fp, ⌜FullOk s.base fp ∧ LogOk s⌝ ∗ logRecs γ base0 fp ∗ logRecs γ s.base s.log ∗
        commitIn γ (fp ++ s.log) s.commit s.term := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexists fp
  isplitr; · ipureintro; exact ⟨Hfull.1, Hlog_ok⟩
  iframe Hfrecs Hrecs Hcommit

/-- The case split at the leader's arrival: the global committed log `P` is justified by a
commit at a term `t`; above `T` it dooms the request, at `T` it is the leader's own (at most
its commit index), below `T` it is behind the leader's own committed entry of `T`. -/
theorem read_arrive_core (γ : RaftNames) (id : w64) (s : PState) (c : List w8)
    (Lc P fp : List EntryM) :
    s.role = .leader →
    s.term ≠ W64 0 →
    plogTermAt s.base s.log s.commit = some s.term →
    Lc <+: P →
    FullOk s.base fp → LogOk s →
    ⊢ committedJust (GF := GF) γ P -∗ votesTbl γ -∗ lcmOwn γ id s -∗ isLeader γ id s.term -∗
      commitIn γ (fp ++ s.log) s.commit s.term -∗ readReq γ c Lc -∗
      votesTbl γ ∗ lcmOwn γ id s ∗ ∃ d, rqRecOk γ s.term ((c, s.commit), d) := by
  intro Hr Htnz Hct HLP Hfull Hlok
  iintro #Hj Htbl Hlcm #Hl #Hcmt #Hrq
  -- a short enough committed log: the request is read at once
  have Hok : ∀ (len : Int), (P.length : Int) ≤ len → len ≤ uint.Z s.commit →
      (Lc.length : Int) ≤ uint.Z s.commit := by
    intro len H1 H2
    have := HLP.length_le
    omega
  have Hnone : (Lc.length : Int) ≤ uint.Z s.commit →
      ⊢ readReq (GF := GF) γ c Lc -∗ ∃ d, rqRecOk γ s.term ((c, s.commit), d) := by
    intro Hle
    iintro #Hrq
    iexists none
    unfold rqRecOk readOk
    iexists Lc
    iframe Hrq
    ipureintro; exact Hle
  unfold committedJust
  icases Hj with (%HP0 | ⟨%t, %n, %G, %ldr, #Hcq, %HP0, #Hldr, #Hclb⟩)
  · subst HP0
    iframe Htbl Hlcm
    iapply Hnone (Hok 0 (by simp) (uint_Z_nonneg _)) $$ Hrq
  · have HPn : (P.length : Int) ≤ uint.Z n := by
      rw [HP0, List.length_take]; have := uint_Z_nonneg n; omega
    rcases Int.lt_trichotomy (uint.Z s.term) (uint.Z t) with HtT | HtT | HtT
    · -- doomed, unless the log is empty
      by_cases Hn0 : uint.Z n = 0
      · iframe Htbl Hlcm
        iapply Hnone (Hok (uint.Z n) HPn (by rw [Hn0]; exact uint_Z_nonneg _)) $$ Hrq
      · iframe Htbl Hlcm
        icases cq_cqAt γ t n G $$ Hcq with ⟨%a, %cQ, %q, #Hcqa⟩
        icases doomed_intro γ s.term t n G a cQ q HtT (by have := uint_Z_nonneg n; omega)
          $$ Hcqa with ⟨%U, #Hdm⟩
        iexists (some (t, U))
        simp only [rqRecOk]
        iexact Hdm
    · -- the leader's own commit
      have Ht : t = s.term := uint_Z_inj.mp HtT.symm
      subst Ht
      icases isLeader_unique γ ldr id s.term $$ Hldr Hl with %Heq
      subst Heq
      icases lcmOwn_bound_keep γ ldr s n Hr $$ Hlcm Hclb with ⟨Hlcm, %Hb⟩
      iframe Htbl Hlcm
      iapply Hnone (Hok (uint.Z n) HPn Hb) $$ Hrq
    · -- an earlier term's commit is behind the leader's entry of its own term
      have Hbi : uint.Z s.base.index' ≤ uint.Z s.commit := Hlok.2.1
      have HFi : plogTermAt base0 (fp ++ s.log) s.commit = some s.term := by
        rw [full_term_at s.base fp s.log s.commit Hfull Hbi]; exact Hct
      icases cq_full γ t n G $$ Hcq with ⟨%HwG, #HrG⟩
      icases recs_mono γ G HwG $$ HrG with %Hmono
      icases cq_base γ _ _ _ $$ Hcq with ⟨%HGn, -⟩
      ihave #Hcmt' := commitIn_j γ _ _ _ $$ Hcmt
      ieval (unfold commitJ) at Hcmt'
      icases Hcmt' with (%Hc0 | ⟨%t2, %n2, %G2, #Hcq2, %Hc2⟩)
      · -- commit index `0`: the entry there is the sentinel of term `0`
        exfalso
        have Hc : s.commit = W64 0 := uint_Z_inj.mp (by rw [Hc0]; rfl)
        rw [Hc, show (W64 0 : w64) = (base0 : entryID).index' from rfl, plogTermAt_base] at HFi
        exact Htnz (Option.some.inj HFi).symm
      · by_cases Hle : uint.Z n ≤ uint.Z s.commit
        · iframe Htbl Hlcm
          iapply Hnone (Hok (uint.Z n) HPn Hle) $$ Hrq
        · icases cq_agree γ t n t2 n2 s.commit G G2 (by omega) Hc2.1 $$ Htbl Hcq Hcq2 with %Hag
          have HGi : plogTermAt base0 G s.commit = some s.term :=
            (Hag s.commit (Int.le_refl _)).trans (Hc2.2.2.trans HFi)
          have := Hmono s.commit n s.term t (by omega) HGi HGn
          exfalso; omega

theorem leaderWit_leader (γ : RaftNames) (id : w64) (s : PState) (h : s.role = .leader) :
    leaderWit (GF := GF) γ id s = isLeader γ id s.term := by
  unfold leaderWit; rw [h]

/-- A request arriving at the leader of `T`, whose commit index is at an entry of `T`: it
is recorded, read at the commit index, doomed or not. -/
theorem ownRaftGhost_read_arrive (γ : RaftNames) (id : w64) (s : PState) (c : List w8)
    (Lc : List EntryM) :
    s.role = .leader →
    plogTermAt s.base s.log s.commit = some s.term →
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ readReq γ c Lc ={⊤ \ ↑raftRegN}=∗
      ownRaftGhost γ id s md ∗ ∃ d, rqRecOk γ s.term ((c, s.commit), d) := by
  intro Hr Hct
  iintro Hown #Hrq
  icases persistent_entails_right
    (wand_entails (ownRaftGhost_term_nz (GF := GF) γ id s (by rw [Hr]; decide))) $$ Hown
    with ⟨%Htnz, Hown⟩
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ihave #Hl : isLeader γ id s.term $$ []
  · rw [← leaderWit_leader γ id s Hr]; iexact Hlead
  ihave ⟨%fp, %Hfl, #Hfr, #Hrecs, #Hcmt⟩ := ownLogGhost_commitIn γ id s kl $$ Hlg
  ihave #Hinv := ownLogGhost_inv $$ Hlg
  ihave #Hrq' := Hrq
  ieval (unfold readReq) at Hrq'
  icases Hrq' with ⟨%_, -, #HLc⟩
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  unfold raftLogInv raftLogInvBody
  iinv Hli with ⟨%P, >HP, >#Hj, >Htbl, Hwt, Hpo⟩ Hclose
  ihave %HLP := isCommitted_prefix γ Lc P $$ HLc HP
  icases read_arrive_core γ id s c Lc P fp Hr Htnz Hct HLP Hfl.1 Hfl.2
    $$ Hj Htbl Hlcm Hl Hcmt Hrq with ⟨Htbl, Hlcm, #Hres⟩
  imod Hclose $$ [HP Htbl Hpo Hwt] with -
  · inext
    iexists P
    iframe
    iexact Hj
  imodintro
  iframe Hres
  unfold ownRaftGhost
  iexists γv, voted, kl
  iframe % # ∗

end inv

end ghost

end EtcdGrove
end Perennial
