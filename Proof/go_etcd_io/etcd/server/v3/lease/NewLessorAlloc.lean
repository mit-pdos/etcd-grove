/-
**`newLessor`'s ghost step** (prove-ps2-newlessor5, 2026-11-21): from the fresh lessor's fields (the
struct literal's, the leases `initAndRecover` made), every ghost name the lessor's predicates mention,
`le.mu` made (`init_RWMutex`, at `lessorMu_fractional`), the channels' idioms (`expiredC` a bag of
`lessorExpiredC`'s payloads, `stopC` a close-once channel, `doneC` a broadcast channel). What
`newLessor`'s proof calls once, between `initAndRecover` and `go le.runLoop()`. Lean-first.

`newLessor_alloc_at` (F2's P-L1, 2026-11-26; `notes/specs-only/ledger.md`, "2026-11-26:
`lessorAbsentStays_dist.law`") makes the lessor at a name `γl` the caller chose, from half of `γl`'s ghost
map's authority at `∅` and the slot `lessorSlot γl` holding the other half: it opens the slot, joins the
halves, inserts the lessor's two keys, and closes the slot with the history law (`lessorHistOk_of_rdInv`)
and a pin. `newLessor_alloc` (a fresh name) allocates the name and the slot and calls it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.NewLessorGhost
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorMuFrac
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorSlot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **Every id the guard holds of is granted** (`leaseGranted`). -/
theorem granted_of_guard (γl : GName) (GA : w64 → IProp GF) :
    ∀ L : List w64, lessorGuard (GF := GF) γl GA ∗ □ ([∗list] id ∈ L, GA id) ⊢
      □ [∗list] id ∈ L, leaseGranted γl id
  | [] => by
    iintro ⟨-, -⟩
    imodintro; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
  | x :: L => by
    iintro ⟨#Hg, #Hl⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hl with ⟨#Hx, #Hl⟩
    ihave #Hrest := granted_of_guard γl GA L $$ [$Hg $Hl]
    imodintro
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    iframe Hrest
    iunfold leaseGranted
    iexists GA; iframe Hg Hx

/-- **The lessor at `lp`, its ghost state allocated at the caller's name `γl`** (see the file header):
the lessor's fields after `initAndRecover` (the recovered leases `recs.zip ls`, the minimum TTL `mt`),
the channels, the grant guard of the records' ids, half of `γl`'s authority at `∅` and its slot; the
lessor's predicates at `γl`, its lock's `actualMaxReaders` reader slots, the expiry loop's token and
`doneC`'s close right. -/
theorem newLessor_alloc_at (γl : GName) (lp lm im np : Loc) (h : GoSlice) (hx : List (Loc × w64)) (b : GoInterface)
    (mt : w64) (ec sc dc : GoChan) (γec γsc γdc : ChanNames) (GA : w64 → IProp GF) (mono : Bool)
    (recs : List (w64 × w64 × w64)) (ls : List Loc) (reqOf : w64 → w64) (Lr : List w64)
    (hlp : lp ≠ null) (hlen : ls.length = recs.length) (hnd : (recs.map (·.1)).Nodup)
    (hrq : ∀ x ∈ recs, sint.Z (reqOf x.1) ≤ sint.Z x.2.1) (hLr : Lr.Perm (recs.map (·.1))) :
    (ghostMapAuth γl (1 : Qp).half (∅ : GMap Bool LessorGV) ∗ lessorSlot γl) ∗
    lF go!"mu" lp ↦ (zero_val _root_.Perennial.sync.RWMutex) ∗
      lF go!"demotec" lp ↦ (chan.nil : GoChan) ∗
      lF go!"leaseMap" lp ↦ lm ∗ lm ↦$ recMap (recs.zip ls) ∗
      lF go!"itemMap" lp ↦ im ∗ im ↦$ (∅ : GMap LeaseItem w64) ∗
      lF go!"rd" lp ↦ func.nil ∗ lF go!"cp" lp ↦ func.nil ∗ lF go!"b" lp ↦ b ∗
      lF go!"leaseExpiredNotifier" lp ↦ np ∗ notifierAt np 1 ∗
      lF go!"leaseCheckpointHeap" lp ↦ h ∗ queueAt h hx 1 ∗
      lF go!"expiredC" lp ↦□ ec ∗ isChan ec γec GoSlice ∗ ownChan γec GoSlice (ChanState.Buffered []) ∗
      lF go!"stopC" lp ↦□ sc ∗ isChan sc γsc Unit ∗ ownChan γsc Unit ChanState.Idle ∗
      lF go!"doneC" lp ↦□ dc ∗ isChan dc γdc Unit ∗ ownChan γdc Unit ChanState.Idle ∗
      ([∗list] p ∈ recs.zip ls, recLease mt p.1 p.2) ∗ ⧖ recs.length ∗
      □ ([∗list] id ∈ recs.map (·.1), GA id) ⊢
    |={⊤}=> lessorInv lp γl ∗ lessorModeIs γl mono ∗ lessorExpiredC lp GA ∗
      lessorGuard γl GA ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), lessorRd lp γl) ∗
      leaseOwn γl Lr ∅ ∗ lessorWinTie γl [] ∗ leaseEver γl (recs.map (·.1)) ∗ leaseRevokers γl Lr ∗
      rdOwn γl func.nil ∗ lF go!"b" lp ↦{DFrac.own (1 : Qp).half} b ∗ lessorStopTok lp ∗
      lessorStopRecv lp ∗ □ ([∗list] x ∈ recs, leaseReqIs γl x.1 (reqOf x.1)) ∗
      lessorAt γl 0 (recMap (recs.zip ls), ∅, recTTLs mt recs) ∗ notifRTok γl ∗
      ownBroadcastChan dc γdc iprop(True) .Pending := by
  iintro ⟨⟨Hhalf, #Hslot⟩, Hmu, Hdem, Hlm, HM, Him, HI, Hrd, Hcp, Hb, Hnf, Hnot, Hh, Hhq, #Hecf, #Hec, Heco,
    #Hscf, #Hsc, Hsco, #Hdcf, #Hdc, Hdco, Hrl, #Hr, #HGA⟩
  -- the recovered leases, as `xs`
  have hfst : (recs.zip ls).map Prod.fst = recs := List.map_fst_zip (by omega)
  have hids : (recs.zip ls).map (·.1.1) = recs.map (·.1) := by
    calc (recs.zip ls).map (·.1.1) = ((recs.zip ls).map Prod.fst).map (·.1) := by
          rw [List.map_map]; rfl
      _ = recs.map (·.1) := by rw [hfst]
  have hndx : ((recs.zip ls).map (·.1.1)).Nodup := by rw [hids]; exact hnd
  have hrqx : ∀ p ∈ recs.zip ls, sint.Z (reqOf p.1.1) ≤ sint.Z p.1.2.1 :=
    fun p hp => hrq p.1 (List.of_mem_zip hp).1
  -- the item sets' map: the recovered leases registered
  imod (ghost_map_alloc_empty (GF := GF) (K := Loc) (V := GMap LeaseItem Unit)) with ⟨%γS, HSa⟩
  ihave Hids0 : iprop([∗map] l ↦ _S ∈ (∅ : GMap Loc (GMap LeaseItem Unit)),
      ∃ id : w64, lsF go!"ID" l ↦□ id) $$ []
  · iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2; itrivial
  imod recs_register γS mt (recs.zip ls) ∅ $$ [$HSa $Hids0 $Hrl]
    with ⟨%Sm, ⟨-, %H2, %H3, %H4⟩, HSa, #Hids, #Httls, Hregs⟩
  have hSm : ∀ (l : Loc) (S : GMap LeaseItem Unit), Sm.lookup l = some S →
      l ∈ (recs.zip ls).map (·.2) ∧ S = ∅ := fun l S hS => by
    rcases H2 l S hS with h | h
    · simp at h
    · exact h
  have hSm2 : ∀ p ∈ recs.zip ls, Sm.lookup p.2 = some ∅ := fun p hp => (H3 p hp).2
  -- the readers' names and invariant
  icases ptsto_halves_split _ _ $$ Hnf with ⟨Hnf1, Hnf2⟩
  imod lessor_rd_alloc lp np mt (recs.zip ls) mono reqOf γS Sm hndx H4 hSm hSm2 hrqx
    $$ [$HSa $Hids $Httls $Hnf2 $Hnot]
    with ⟨%γr, ⟨%HγS, %Hmono⟩, #Hrinv, #Hninv, #Hdinv, Hho, Hhm, #Hidx, HSo, HUo, #HQe, Hwo, Hwt,
      Hdm, Hx, Hy⟩
  subst HγS
  -- the grant guard, the closers' map, the lessor's ghost map
  imod (saved_pred_alloc (GF := GF) GA DFrac.discard trivial) with ⟨%γga, #Hga⟩
  imod (ghost_map_alloc (GF := GF) (recMap (recs.zip ls))) with ⟨%γcl, Hcla, Hcle⟩
  -- the slot: the member's half at `∅` excludes the published case (its pin); the halves joined
  iinv Hslot with Hsb Hsclose
  icases Hsb with (>Hh2 | Hpub)
  rotate_left
  · iexfalso
    icases Hpub with ⟨-, >⟨%γr', #Hp'⟩⟩
    iapply lessorPinR_not_empty γl γr' (1 : Qp).half
    iframe Hhalf Hp'
  ihave Hla : iprop(ghostMapAuth (GF := GF) γl 1 (∅ : GMap Bool LessorGV)) $$ [Hhalf Hh2]
  · iapply (ghostMapAuth_halves γl (∅ : GMap Bool LessorGV)).2; iframe Hhalf Hh2
  -- the lessor's two keys
  imod (ghost_map_insert (GF := GF) (m := (∅ : GMap Bool LessorGV)) false
    (Sum.inl (lp, γga, γcl, γr) : LessorGV) rfl) $$ Hla with ⟨Hla, Hlf⟩
  have h1 : ((∅ : GMap Bool LessorGV).insert false (Sum.inl (lp, γga, γcl, γr))).lookup true = none := by
    rw [GMap.lookup_insert_ne _ _ (by decide)]; rfl
  imod (ghost_map_insert (GF := GF) true (Sum.inr Lr : LessorGV) h1) $$ Hla with ⟨Hla, Hlt⟩
  ihave Hla : iprop(ghostMapAuth (GF := GF) γl 1 (lessorGhost lp γga γcl γr Lr)) $$ [Hla]
  · unfold lessorGhost; iexact Hla
  imod (ghostMapElem_persist false γl _ _) $$ Hlf with #Hpin
  ihave #HpinA : lessorPinAll (GF := GF) γl lp γga γcl γr $$ []
  · iunfold lessorPinAll; iexact Hpin
  ihave #HpinG : lessorPinG (GF := GF) γl lp γga γcl $$ []
  · iunfold lessorPinG; iexists γr; iexact HpinA
  ihave #HpinR : lessorPinR (GF := GF) γl γr $$ []
  · iunfold lessorPinR; iexists lp, γga, γcl; iexact HpinA
  ihave #HpinL : lessorPin (GF := GF) γl lp $$ []
  · iunfold lessorPin; iexists γga, γcl; iexact HpinG
  ihave #Hrdinv : lessorRdInv (GF := GF) γl $$ []
  · iunfold lessorRdInv; iexists γr; iframe HpinR Hrinv
  ihave #Hguard : lessorGuard (GF := GF) γl GA $$ []
  · iunfold lessorGuard; iexists lp, γga, γcl; iframe HpinG Hga
  -- the slot closed with the history law
  ihave #Hhist := lessorHistOk_of_rdInv γl $$ Hrdinv
  imod Hsclose $$ [] with -
  · inext; iright; iframe Hhist; iexists γr; iexact HpinR
  icases ((ghostMapElem_fractional (GF := GF) true γl (Sum.inr Lr : LessorGV)).fractional
    (1 : Qp).half (1 : Qp).half).1 $$ [Hlt] with ⟨Hlt1, Hlt2⟩
  · rw [Qp.half_add_half]; iexact Hlt
  -- the leases' locks
  imod recover_locks_all γl γr mt ⊤ (recs.zip ls) $$ [$Hrdinv $HpinR $Hregs] with Hd
  ihave Hd : iprop([∗list] p ∈ recs.zip ls, iprop(lsF go!"ttl" p.2 ↦□ grantTTL mt p.1.2.1 ∗
      recCore γl p.1.1 p.2)) $$ [Hd]
  · iunfold recDone at Hd; iexact Hd
  icases (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)).1 $$ Hd with ⟨-, Hd⟩
  ihave Hd := (recMap_bigSepM (fun id l => recCore (GF := GF) γl id l) (recs.zip ls) hndx).2 $$ Hd
  ihave Hcle : iprop([∗map] id ↦ l ∈ recMap (recs.zip ls), iprop(
      ghostMapElem (GF := GF) γcl id (DFrac.own (1 : Qp).half) l ∗
      ghostMapElem γcl id (DFrac.own (1 : Qp).half) l)) $$ [Hcle]
  · iapply BigSepM.bigSepM_impl $$ Hcle
    iintro !> %k %v %_ He
    iapply ((ghostMapElem_fractional (GF := GF) k γcl v).fractional (1 : Qp).half (1 : Qp).half).1
    rw [Qp.half_add_half]; iexact He
  ihave Hall : iprop([∗map] id ↦ l ∈ recMap (recs.zip ls), iprop(closerAt (GF := GF) γl γcl ∅ id l ∗
      ((ghostMapElem γcl id (DFrac.own (1 : Qp).half) l ∗
        ∃ c : GoChan, lsF go!"revokec" l ↦□ c ∗ revokeCloser c) ∗
      (isLeaseObj γl l ∗ leaseMeta id l 1)))) $$ [Hd Hcle]
  · ihave ⟨Hn1, Hn2⟩ : iprop(([∗map] id ↦ l ∈ recMap (recs.zip ls),
          ghostMapElem (GF := GF) γcl id (DFrac.own (1 : Qp).half) l) ∗
        [∗map] id ↦ l ∈ recMap (recs.zip ls), ghostMapElem (GF := GF) γcl id (DFrac.own (1 : Qp).half) l)
        $$ [Hcle]
    · rw [← BigSepM.bigSepM_sep_eq]; iexact Hcle
    ihave H : iprop([∗map] id ↦ l ∈ recMap (recs.zip ls), iprop(recCore (GF := GF) γl id l ∗
        ghostMapElem (GF := GF) γcl id (DFrac.own (1 : Qp).half) l ∗
          ghostMapElem γcl id (DFrac.own (1 : Qp).half) l)) $$ [Hd Hn1 Hn2]
    · rw [BigSepM.bigSepM_sep_eq, BigSepM.bigSepM_sep_eq]; iframe
    iapply BigSepM.bigSepM_impl $$ H
    iintro !> %k %v %_ ⟨Hc, He1, He2⟩
    iunfold recCore at Hc
    icases Hc with ⟨#Hlo, Hm, Hio, Hmu1, Hrc⟩
    iunfold closerAt
    iframe
    iexact Hlo
  ihave ⟨Hcls, Hall⟩ : iprop(([∗map] id ↦ l ∈ recMap (recs.zip ls), closerAt (GF := GF) γl γcl ∅ id l) ∗
      [∗map] id ↦ l ∈ recMap (recs.zip ls),
        iprop((ghostMapElem (GF := GF) γcl id (DFrac.own (1 : Qp).half) l ∗
          ∃ c : GoChan, lsF go!"revokec" l ↦□ c ∗ revokeCloser c) ∗
        (isLeaseObj γl l ∗ leaseMeta id l 1))) $$ [Hall]
  · rw [← BigSepM.bigSepM_sep_eq]; iexact Hall
  ihave ⟨Hrv, Hall⟩ : iprop(([∗map] id ↦ l ∈ recMap (recs.zip ls),
      iprop(ghostMapElem (GF := GF) γcl id (DFrac.own (1 : Qp).half) l ∗
        ∃ c : GoChan, lsF go!"revokec" l ↦□ c ∗ revokeCloser c)) ∗
      [∗map] id ↦ l ∈ recMap (recs.zip ls), iprop(isLeaseObj (GF := GF) γl l ∗ leaseMeta id l 1))
      $$ [Hall]
  · rw [← BigSepM.bigSepM_sep_eq]; iexact Hall
  ihave ⟨#Hlos, Hmetas⟩ : iprop(([∗map] _id ↦ l ∈ recMap (recs.zip ls), isLeaseObj (GF := GF) γl l) ∗
      [∗map] id ↦ l ∈ recMap (recs.zip ls), leaseMeta (GF := GF) id l 1) $$ [Hall]
  · rw [← BigSepM.bigSepM_sep_eq]; iexact Hall
  -- the live set's membership, the grants
  have hmem : ∀ id : w64, id ∈ Lr ↔ ((recMap (recs.zip ls)).lookup id).isSome := fun id => by
    rw [hLr.mem_iff, recMap_isSome, hids]
  ihave #Hgr0 := granted_of_guard γl GA (recs.map (·.1)) $$ [$Hguard $HGA]
  ihave #Hgr : iprop([∗list] id ∈ Lr, leaseGranted (GF := GF) γl id) $$ []
  · iapply (BigSepL.bigSepL_perm (PROP := IProp GF) (Φ := fun id => leaseGranted (GF := GF) γl id)
      hLr).2
    iexact Hgr0
  have hlast : [recSnap mt (recs.zip ls)].getLast? =
      some (recMap (recs.zip ls), ∅, recTTLs mt ((recs.zip ls).map Prod.fst)) := rfl
  -- the lock's resource
  icases ptsto_halves_split _ _ $$ Him with ⟨Him1, Him2⟩
  icases ownMap_halves_split im (∅ : GMap LeaseItem w64) $$ HI with ⟨HI1, HI2⟩
  icases ptsto_halves_split _ _ $$ Hrd with ⟨Hrd1, Hrd2⟩
  icases ptsto_halves_split _ _ $$ Hb with ⟨Hb1, Hb2⟩
  -- `stopC`
  imod (token_alloc (GF := GF)) with ⟨%γt, Ht⟩
  imod (inv_alloc onceChanN ⊤ (onceChanInv (GF := GF) γsc γt)) $$ [Hsco] with #Hsci
  · inext; iunfold onceChanInv; iexists .Idle; dsimp only; iframe Hsco
  ihave #Honce : onceRecv (GF := GF) sc γt $$ []
  · iunfold onceRecv; iexists γsc; iframe Hsc Hsci
  ihave #Hstr : lessorStopRecv (GF := GF) lp $$ []
  · iunfold lessorStopRecv; iexists sc, γt; iframe Hscf Honce
  ihave #Hsz : ⧖ (GMap.size (recMap (recs.zip ls))) $$ []
  · iapply (preceipt_mono (GF := GF) (m := GMap.size (recMap (recs.zip ls)))
      (n := recs.length) ?_) $$ Hr
    have := recMap_size (recs.zip ls)
    rw [List.length_zip] at this
    omega
  ihave Hmures : lessorMu (GF := GF) lp γl 1 $$ [Hlm HM Him1 HI1 Hrd1 Hla Hcla Hlt1 Hmetas Hdem Hnf1 Hx Hh
      Hhq Hcp Hb1 Hdm Hhm]
  · iunfold lessorMu
    iexists lm, im, recMap (recs.zip ls), ∅, func.nil, Lr
    iframe Hlm HM Him1 HI1 Hrd1 Hsz Hlos
    isplitl [Hla Hcla]
    · iunfold lessorAuth
      iexists γga, γcl, γr
      iframe Hla Hcla Hgr
    isplitl [Hlt1]
    · iunfold leaseFrag; iexact Hlt1
    isplitr
    · ipureintro; exact hmem
    isplitl [Hmetas Hdem Hnf1 Hx Hh Hhq Hcp Hb1 Hdm]
    · iunfold lessorExtra
      iexists chan.nil, np, h, hx, b
      iframe Hdem Hnf1 Hh Hhq Hcp Hmetas Hb1 Hstr
      isplitl [Hx]
      · iunfold notifShare; iexists γr; iframe HpinR Hx Hninv
      iunfold demoteTie; iexists γr; iframe HpinR Hdm Hdinv
    iexists γr, [recSnap mt (recs.zip ls)]
    iframe HpinR Hhm
    ipureintro; exact ⟨_, hlast⟩
  -- `le.mu`
  imod (sync.init_RWMutex (lessorMu (GF := GF) lp γl) (E := ⊤) (lF go!"mu" lp)) $$ [Hmures] Hmu
    with HmuRs
  · inext; iexact Hmures
  have hmax : sync.rwmutex.actualMaxReaders.toNat =
      (sync.rwmutex.actualMaxReaders.toNat - 1) + 1 := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  ihave ⟨HmuRs, #HmuG⟩ : iprop(([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
      sync.ownRWMutex (GF := GF) (lF go!"mu" lp) (lessorMu lp γl)) ∗
      sync.isRWMutexGuard (lF go!"mu" lp) (lessorMu lp γl)) $$ [HmuRs]
  · rw [hmax, List.replicate_succ]
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ HmuRs with ⟨HmuR, HmuRest⟩
    icases sync.ownRWMutex_guard _ _ $$ HmuR with ⟨HmuR, #HmuG⟩
    iframe HmuG
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    iframe HmuR HmuRest
  -- `expiredC`, `doneC`
  imod (start_bag (fun ls => iprop(⌜¬ leasesNoExpiry⌝ ∗ expiredLeases GA ls)) (.Buffered []) ec γec trivial)
    $$ Hec Heco with #HecB
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γdc dc $$ Hdc Hdco with Hpend
  icases ownBroadcastChan_open _ _ _ _ $$ Hpend with ⟨%γbi, #Hbi, Hpend⟩
  ihave #Hunk := ownBroadcastChan_close dc γdc iprop(True) Broadcast.Unknown γbi $$ [$Hbi]
  ihave Hpend := ownBroadcastChan_close dc γdc iprop(True) Broadcast.Pending γbi $$ [$Hbi $Hpend]
  imodintro
  iframe Hpend Hguard Hb2
  isplitr
  · iunfold lessorInv; iframe HpinL HmuG Hrdinv; ipureintro; exact hlp
  isplitr
  · iunfold lessorModeIs; iexists γr; iframe HpinR; ipureintro; exact Hmono
  isplitr
  · iunfold lessorExpiredC; iexists ec, γec; iframe Hecf HecB
  isplitl [HmuRs]
  · iunfold lessorRd; iexact HmuRs
  isplitl [Hlt2 Hcls Him2 HI2 Hho HSo Hwo]
  · iunfold leaseOwn; iunfold leaseOwnW
    isplitl [Hlt2]
    · iunfold leaseFrag; iexact Hlt2
    iunfold leaseClosers
    iexists lp, γga, γcl, recMap (recs.zip ls), im
    iframe HpinG Him2 HI2 Hcls
    isplitr
    · ipureintro; exact hmem
    isplitr
    · ipureintro; intro it x h; simp at h
    isplitr
    · ipureintro; intro it x h; simp at h
    iexists γr, [recSnap mt (recs.zip ls)], Sm
    iframe HpinR Hho HSo
    isplitr
    · ipureintro; exact ⟨_, hlast⟩
    iunfold winOwn; iexists []; iframe Hwo; ipureintro; rfl
  isplitl [Hwt]
  · iunfold lessorWinTie; iexists γr; iframe HpinR Hwt
  isplitl [HUo]
  · iunfold leaseEver; iexists γr; iframe HpinR; rw [← hids]; iexact HUo
  isplitl [Hrv]
  · iunfold leaseRevokers
    iexists lp, γga, γcl, recMap (recs.zip ls)
    iframe HpinG Hrv
    ipureintro; exact hmem
  isplitl [Hrd2]
  · iunfold rdOwn; iexists lp; iframe HpinL Hrd2
  isplitl [Ht]
  · iunfold lessorStopTok; iexists sc, dc, γt, γdc; iframe Hscf Hdcf Honce Ht Hunk
  isplitr
  · iframe Hstr
  isplitr
  · imodintro
    rw [← BigSepL.bigSepL_map (fun x : w64 × w64 × w64 => x.1)
      (Φ := fun _ id => leaseReqIs (GF := GF) γl id (reqOf id)), ← hids]
    iapply (BigSepL.bigSepL_impl (PROP := IProp GF)) $$ HQe
    iintro !> %k %id %_ #He
    iunfold leaseReqIs; iexists γr; iframe HpinR He
  isplitr
  · iunfold lessorAt; iexists γr; iframe HpinR
    have hσ : recSnap mt (recs.zip ls) = (recMap (recs.zip ls), ∅, recTTLs mt recs) := by
      unfold recSnap; rw [hfst]
    rw [← hσ]; iexact Hidx
  iunfold notifRTok; iexists γr; iframe HpinR Hy

/-- **The fresh lessor at `lp`, its ghost state allocated** (see the file header): the lessor's
fields after `initAndRecover` (the recovered leases `recs.zip ls`, the minimum TTL `mt`), the
channels, the grant guard of the records' ids; the lessor's predicates at a fresh `γl`, its lock's
`actualMaxReaders` reader slots, the expiry loop's token and `doneC`'s close right. -/
theorem newLessor_alloc (lp lm im np : Loc) (h : GoSlice) (hx : List (Loc × w64)) (b : GoInterface)
    (mt : w64) (ec sc dc : GoChan) (γec γsc γdc : ChanNames) (GA : w64 → IProp GF) (mono : Bool)
    (recs : List (w64 × w64 × w64)) (ls : List Loc) (reqOf : w64 → w64) (Lr : List w64)
    (hlp : lp ≠ null) (hlen : ls.length = recs.length) (hnd : (recs.map (·.1)).Nodup)
    (hrq : ∀ x ∈ recs, sint.Z (reqOf x.1) ≤ sint.Z x.2.1) (hLr : Lr.Perm (recs.map (·.1))) :
    lF go!"mu" lp ↦ (zero_val _root_.Perennial.sync.RWMutex) ∗
      lF go!"demotec" lp ↦ (chan.nil : GoChan) ∗
      lF go!"leaseMap" lp ↦ lm ∗ lm ↦$ recMap (recs.zip ls) ∗
      lF go!"itemMap" lp ↦ im ∗ im ↦$ (∅ : GMap LeaseItem w64) ∗
      lF go!"rd" lp ↦ func.nil ∗ lF go!"cp" lp ↦ func.nil ∗ lF go!"b" lp ↦ b ∗
      lF go!"leaseExpiredNotifier" lp ↦ np ∗ notifierAt np 1 ∗
      lF go!"leaseCheckpointHeap" lp ↦ h ∗ queueAt h hx 1 ∗
      lF go!"expiredC" lp ↦□ ec ∗ isChan ec γec GoSlice ∗ ownChan γec GoSlice (ChanState.Buffered []) ∗
      lF go!"stopC" lp ↦□ sc ∗ isChan sc γsc Unit ∗ ownChan γsc Unit ChanState.Idle ∗
      lF go!"doneC" lp ↦□ dc ∗ isChan dc γdc Unit ∗ ownChan γdc Unit ChanState.Idle ∗
      ([∗list] p ∈ recs.zip ls, recLease mt p.1 p.2) ∗ ⧖ recs.length ∗
      □ ([∗list] id ∈ recs.map (·.1), GA id) ⊢
    |={⊤}=> ∃ γl : GName, lessorInv lp γl ∗ lessorModeIs γl mono ∗ lessorExpiredC lp GA ∗
      lessorGuard γl GA ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), lessorRd lp γl) ∗
      leaseOwn γl Lr ∅ ∗ lessorWinTie γl [] ∗ leaseEver γl (recs.map (·.1)) ∗ leaseRevokers γl Lr ∗
      rdOwn γl func.nil ∗ lF go!"b" lp ↦{DFrac.own (1 : Qp).half} b ∗ lessorStopTok lp ∗
      lessorStopRecv lp ∗ □ ([∗list] x ∈ recs, leaseReqIs γl x.1 (reqOf x.1)) ∗
      lessorAt γl 0 (recMap (recs.zip ls), ∅, recTTLs mt recs) ∗ notifRTok γl ∗
      ownBroadcastChan dc γdc iprop(True) .Pending := by
  iintro H
  imod (ghost_map_alloc_empty (GF := GF) (K := Bool) (V := LessorGV)) with ⟨%γl, Ha⟩
  icases (ghostMapAuth_halves γl (∅ : GMap Bool LessorGV)).1 $$ Ha with ⟨Ha1, Ha2⟩
  imod (inv_alloc lessorSlotN ⊤ iprop(ghostMapAuth (GF := GF) γl (1 : Qp).half (∅ : GMap Bool LessorGV) ∨
      (lessorHistOk γl ∗ ∃ γr : LessorRdNames, lessorPinR γl γr))) $$ [Ha2] with #Hs
  · inext; ileft; iexact Ha2
  ihave #Hslot : lessorSlot (GF := GF) γl $$ []
  · iunfold lessorSlot; iexact Hs
  imod (newLessor_alloc_at γl lp lm im np h hx b mt ec sc dc γec γsc γdc GA mono recs ls reqOf Lr
    hlp hlen hnd hrq hLr) $$ [Ha1 H] with Hpost
  · isplitl [Ha1]
    · iframe Ha1 Hslot
    iexact H
  imodintro
  iexists γl
  iexact Hpost

end alloc

end lease
end EtcdGrove
end Perennial
