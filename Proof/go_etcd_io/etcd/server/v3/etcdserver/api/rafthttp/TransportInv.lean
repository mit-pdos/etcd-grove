/-
**The transport's lock and its stop rights** (rafthttp stage 6c; D39). Lean-first.
* `trLockP` (fractional, `t.mu`'s, an `RWMutex`): the `peers` and `remotes` maps (each `nil` once
  `Stop` ran: `mapOrNil`), their entries' facts (`peerOk`, `remoteOk`, persistent), half of a
  ghost record `γs` of the maps (`trRec`), and half of a ghost record `γr`: the ids `AddRemote` was
  called for (the remotes' keys among them), those `AddPeer` was (stage 6d: the peers' keys, until
  `Stop` empties the maps) and whether `Stop` ran (the maps are not `nil` until it does); the
  other half with `transportLive` (not stopped) while peers and remotes may be added, then in an
  invariant (`trRemotesFrozen`: the ids for good, `Stop` sets the flag).
* `trStopInv` (an invariant): the other half of the record, with the right to stop each peer and
  remote it lists (`peerStop`, `remoteStop`): `AddPeer`/`AddRemote` add one under the write lock,
  `Stop` takes them all under it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The record of the transport's maps: their pointers and contents. -/
abbrev trRec := Loc × Loc × GMap w64 GoInterface × GMap w64 Loc

/-- The ids `AddRemote` and `AddPeer` were called for (stage 6d): `.1` the remotes', `.2` the
peers'. -/
abbrev trIds := List w64 × List w64

/-- A map `M` at `m`, at the fraction `q`, or `nil` and empty. -/
def mapOrNil {V : Type} [ZeroVal V] (m : Loc) (q : Qp) (M : GMap w64 V) :
    IProp GF :=
  iprop(⌜m = null ∧ M = ∅⌝ ∨ ownMap m (DFrac.own q) M)

/-- The peers' facts: each entry a `*peer` of `peerOk`. -/
def peersOk (Rh : RaftHttp GF) (lid : w64) (γd : GName) (R : IProp GF)
    (PM : GMap w64 GoInterface) : IProp GF :=
  iprop([∗map] id ↦ pi ∈ PM, ∃ p : Loc,
    ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗ peerOk Rh lid id γd R p)

/-- The remotes' facts. -/
def remotesOk (Rh : RaftHttp GF) (lid : w64) (R : IProp GF) (RM : GMap w64 Loc) : IProp GF :=
  iprop([∗map] id ↦ g ∈ RM, remoteOk Rh lid id R g)

/-- **What the transport `t`'s mutex guards** at the fraction `q` (see the file header). -/
def trLockP (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs γr : GName)
    (q : Qp) : IProp GF :=
  iprop(∃ (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (rs : trIds)
      (sb : Bool),
    t.[rafthttp.Transport, go!"peers"] ↦{DFrac.own q} pm ∗
    t.[rafthttp.Transport, go!"remotes"] ↦{DFrac.own q} rm ∗
    mapOrNil pm q PM ∗ mapOrNil rm q RM ∗ ghostVar γs q.half ((pm, rm, PM, RM) : trRec) ∗
    ghostVar γr q.half (rs, sb) ∗
    ⌜(∀ id, (RM !! id).isSome → id ∈ rs.1) ∧ (sb = false → pm ≠ null ∧ rm ≠ null) ∧
      (rm ≠ null → ∀ id ∈ rs.2, (PM !! id).isSome)⌝ ∗
    □ peersOk Rh lid γd R PM ∗ □ remotesOk Rh lid R RM)

/-- **A reader's token of the transport's mutex** (exclusive): what `RLock` takes; `Start` gives a
supply of them (`Send`'s caller, each handler invocation's `Get`, `CutPeer`'s and `MendPeer`'s). -/
def trReadTok (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF)
    (γs γr : GName) : IProp GF :=
  sync.ownRWMutex (t.[rafthttp.Transport, go!"mu"]) (trLockP Rh t lid γd R γs γr)

def trRemN : Namespace := nroot.@"rafthttp_tr_remotes"

/-- **The ids `AddRemote` and `AddPeer` were called for, `rs`, for good** (persistent): the half
of `γr` no longer with `transportLive` (no more `AddRemote`, `AddPeer`). -/
def trRemotesFrozen (γr : GName) (rs : trIds) : IProp GF :=
  inv trRemN (∃ sb : Bool, ghostVar (GF := GF) γr (1 : Qp).half (rs, sb))

instance trRemotesFrozen_persistent (γr : GName) (rs : trIds) :
    Persistent (trRemotesFrozen (GF := GF) γr rs) := by
  unfold trRemotesFrozen; infer_instance

def trStopN : Namespace := nroot.@"rafthttp_tr_stop"

/-- **The transport's stop rights** (see the file header). -/
def trStopInv (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) : IProp GF :=
  inv trStopN iprop(∃ (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc),
    ghostVar γs (1 : Qp).half ((pm, rm, PM, RM) : trRec) ∗
    ([∗map] id ↦ pi ∈ PM, ∃ p : Loc,
      ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗ peerStop Rh id R p) ∗
    ([∗map] id ↦ g ∈ RM, remoteStop Rh id R g))

instance trStopInv_persistent (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) :
    Persistent (trStopInv Rh R γs) := by
  unfold trStopInv; infer_instance

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem mapOrNil_fractional {V : Type} [ZeroVal V] (m : Loc) (M : GMap w64 V)
    (q1 q2 : Qp) :
    mapOrNil (GF := GF) m (q1 + q2) M ⊣⊢ mapOrNil m q1 M ∗ mapOrNil m q2 M := by
  unfold mapOrNil
  constructor
  · iintro (%H | H)
    · isplitl
      · ileft; ipureintro; exact H
      · ileft; ipureintro; exact H
    · icases ((ownMap_fractional (GF := GF) m M).fractional q1 q2).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iright; iexact H1
      · iright; iexact H2
  · iintro ⟨(%H | H1), (%H' | H2)⟩
    · ileft; ipureintro; exact H
    · ileft; ipureintro; exact H
    · ileft; ipureintro; exact H'
    · iright
      iapply ((ownMap_fractional (GF := GF) m M).fractional q1 q2).2
      iframe

instance trLockP_fractional (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF)
    (γs γr : GName) : Fractional (trLockP Rh t lid γd R γs γr) where
  fractional q1 q2 := by
    have hpt : ∀ v : Loc, ∀ f : GoString,
        (t.[rafthttp.Transport, f] ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢
        t.[rafthttp.Transport, f] ↦{DFrac.own q1} v ∗ t.[rafthttp.Transport, f] ↦{DFrac.own q2} v :=
      fun v f => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1)
        (DFrac.own q2)
    have hgv := fun (x : trRec) => (ghostVar_fractional (GF := GF) γs x).fractional q1.half q2.half
    have hgr := fun (x : trIds × Bool) =>
      (ghostVar_fractional (GF := GF) γr x).fractional q1.half q2.half
    unfold trLockP
    rw [Qp_half_add]
    refine ⟨?_, ?_⟩
    · iintro ⟨%pm, %rm, %PM, %RM, %rs, %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro⟩
      icases (hgr (rs, sb)).1 $$ Hgr with ⟨Hgr1, Hgr2⟩
      icases (hpt pm _).1 $$ Hp with ⟨Hp1, Hp2⟩
      icases (hpt rm _).1 $$ Hr with ⟨Hr1, Hr2⟩
      icases (mapOrNil_fractional pm PM q1 q2).1 $$ Hpm with ⟨Hpm1, Hpm2⟩
      icases (mapOrNil_fractional rm RM q1 q2).1 $$ Hrm with ⟨Hrm1, Hrm2⟩
      icases (hgv (pm, rm, PM, RM)).1 $$ Hg with ⟨Hg1, Hg2⟩
      isplitl [Hp1 Hr1 Hpm1 Hrm1 Hg1 Hgr1]
      · iexists pm, rm, PM, RM, rs, sb; iframe; iframe #; ipureintro; exact Hrs
      · iexists pm, rm, PM, RM, rs, sb; iframe; iframe #; ipureintro; exact Hrs
    · iintro ⟨⟨%pm, %rm, %PM, %RM, %rs, %sb, Hp1, Hr1, Hpm1, Hrm1, Hg1, Hgr1, %Hrs, #Hpo, #Hro⟩,
        ⟨%pm', %rm', %PM', %RM', %rs', %sb', Hp2, Hr2, Hpm2, Hrm2, Hg2, Hgr2, -, -, -⟩⟩
      ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg1 Hg2
      ihave %Hagr := ghostVar_agree γr _ _ _ _ $$ Hgr1 Hgr2
      cases Hag
      cases Hagr
      iexists pm, rm, PM, RM, rs, sb
      isplitl [Hp1 Hp2]
      · iapply (hpt pm _).2; iframe
      isplitl [Hr1 Hr2]
      · iapply (hpt rm _).2; iframe
      isplitl [Hpm1 Hpm2]
      · iapply (mapOrNil_fractional pm PM q1 q2).2; iframe
      isplitl [Hrm1 Hrm2]
      · iapply (mapOrNil_fractional rm RM q1 q2).2; iframe
      isplitl [Hg1 Hg2]
      · iapply (hgv (pm, rm, PM, RM)).2; iframe
      isplitl [Hgr1 Hgr2]
      · iapply (hgr (rs, sb)).2; iframe
      iframe #
      ipureintro; exact Hrs

/-- `v, ok := m[k]` of a map keyed by member ids that may be `nil` (`mapOrNil`). -/
theorem wp_lookup2_mapOrNil [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]
    {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (elem_type : go.GoType) [IntoValTyped (GF := GF) V elem_type] (m : Loc) (q : Qp)
    (M : GMap w64 V) (k : w64) :
    {{ mapOrNil (GF := GF) m q M }}
      (App (App (Val (map.lookup2 go_etcd_io.etcd.client.pkg.v3.types.ID.ty elem_type)) (Val #m))
        (Val #k))
    {{ RET (PairV #((M !! k).getD (zero_val V)) #(decide ((M !! k).isSome))); mapOrNil m q M }} := by
  iintro %Φ Hm HΦ
  iunfold mapOrNil at Hm
  icases Hm with (⟨%Hnil, %HM⟩ | Hm)
  · subst Hnil HM
    rw [show (null : Loc) = map.nil from rfl]
    wp_pures
    simp only [GMap.lookup_empty, Option.getD_none, Option.isSome_none, Bool.false_eq_true,
      decide_false]
    iapply HΦ
    iunfold mapOrNil; ileft; ipureintro; exact ⟨rfl, rfl⟩
  · wp_apply wp_map_lookup2 $$ [$Hm] as Hm
    iapply HΦ
    iunfold mapOrNil; iright; iexact Hm

/-- The frozen list of remotes' ids is any share's. -/
theorem trRemotes_agree (γr : GName) (rs rs' : trIds) (sb : Bool) (q : Qp) :
    ⊢ trRemotesFrozen (GF := GF) γr rs -∗ ghostVar γr q (rs', sb) ={⊤}=∗
      ghostVar γr q (rs', sb) ∗ ⌜rs' = rs⌝ := by
  iintro #Hinv Hg
  unfold trRemotesFrozen
  iinv Hinv with Hi Hclose
  imod Hi with ⟨%sb', Hi⟩
  ihave %Hag := ghostVar_agree γr _ _ _ _ $$ Hi Hg
  imod Hclose $$ [Hi] with -
  · iexists sb'; iexact Hi
  imodintro
  iframe
  ipureintro; cases Hag; rfl

/-- **A peer added** (`AddPeer`, under the write lock, its half of the record): the record gets
it, and the stop invariant its stop right. -/
theorem trStop_add_peer (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (pm rm : Loc)
    (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (id : w64) (p : Loc) (hn : PM !! id = none) :
    ⊢ trStopInv Rh R γs -∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, RM) : trRec) -∗
      peerStop Rh id R p ={⊤}=∗
      ghostVar γs (1 : Qp).half ((pm, rm,
        <[id := interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p]> PM, RM) : trRec) := by
  iintro #Hinv Hg Hst
  unfold trStopInv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%pm', %rm', %PM', %RM', Hg', Hps, Hrs⟩
  imod Hg' with Hg'
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  cases Hag
  imod ghostVar_update_halves ((pm, rm,
      <[id := interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p]> PM, RM) : trRec) γs _ _
    $$ Hg Hg' with ⟨Hg, Hg'⟩
  imod Hclose $$ [Hg' Hps Hrs Hst] with -
  · inext
    iexists pm, rm, _, RM
    iframe Hg' Hrs
    iapply (BigSepM.bigSepM_insert hn).2
    iframe Hps
    iexists p
    iframe Hst
    ipureintro; rfl
  imodintro
  iexact Hg

/-- **A remote added** (`AddRemote`, under the write lock): the record gets it, the stop invariant
its stop right. -/
theorem trStop_add_remote (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (pm rm : Loc)
    (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (id : w64) (g : Loc) (hn : RM !! id = none) :
    ⊢ trStopInv Rh R γs -∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, RM) : trRec) -∗
      remoteStop Rh id R g ={⊤}=∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, <[id := g]> RM) : trRec) := by
  iintro #Hinv Hg Hst
  unfold trStopInv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%pm', %rm', %PM', %RM', Hg', Hps, Hrs⟩
  imod Hg' with Hg'
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  cases Hag
  imod ghostVar_update_halves ((pm, rm, PM, <[id := g]> RM) : trRec) γs _ _ $$ Hg Hg'
    with ⟨Hg, Hg'⟩
  imod Hclose $$ [Hg' Hps Hrs Hst] with -
  · inext
    iexists pm, rm, PM, _
    iframe Hg' Hps
    iapply (BigSepM.bigSepM_insert hn).2
    iframe
  imodintro
  iexact Hg

/-- **The transport stopped** (`Stop`, under the write lock): the peers' and remotes' stop rights
leave the stop invariant, whose record (and the lock's half) becomes the empty one. -/
theorem trStop_take (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (pm rm : Loc)
    (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) :
    ⊢ trStopInv Rh R γs -∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, RM) : trRec) -∗ £ 1 -∗ £ 1 ={⊤}=∗
      ghostVar γs (1 : Qp).half (((null : Loc), (null : Loc), ∅, ∅) : trRec) ∗
      ([∗map] id ↦ pi ∈ PM, ∃ p : Loc,
        ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗ peerStop Rh id R p) ∗
      ([∗map] id ↦ g ∈ RM, remoteStop Rh id R g) := by
  iintro #Hinv Hg Hlc1 Hlc2
  unfold trStopInv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%pm', %rm', %PM', %RM', Hg', Hps, Hrs⟩
  imod Hg' with Hg'
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  cases Hag
  imod ghostVar_update_halves (((null : Loc), (null : Loc), ∅, ∅) : trRec) γs _ _ $$ Hg Hg'
    with ⟨Hg, Hg'⟩
  imod Hclose $$ [Hg'] with -
  · inext
    iexists null, null, ∅, ∅
    iframe Hg'
    isplitl
    · iapply BigSepM.bigSepM_empty.2; itrivial
    · iapply BigSepM.bigSepM_empty.2; itrivial
  imod lc_fupd_elim_later $$ Hlc1 Hps with Hps
  imod lc_fupd_elim_later $$ Hlc2 Hrs with Hrs
  imodintro
  iframe

/-- **The transport marked stopped** (`Stop`, under the write lock): both halves of `γr`. -/
theorem trRemotes_stop (γr : GName) (rs : trIds) (sb : Bool) :
    ⊢ trRemotesFrozen (GF := GF) γr rs -∗ ghostVar γr (1 : Qp).half (rs, sb) ={⊤}=∗
      ghostVar γr (1 : Qp).half (rs, true) := by
  iintro #Hinv Hg
  unfold trRemotesFrozen
  iinv Hinv with Hi Hclose
  imod Hi with ⟨%sb', Hi⟩
  imod ghostVar_update_halves (rs, true) γr _ _ $$ Hi Hg with ⟨Hi, Hg⟩
  imod Hclose $$ [Hi] with -
  · iexists true; iexact Hi
  imodintro
  iexact Hg

/-- A key of a duplicate-free enumeration is in its suffix from its index, and the suffix after
it holds only other keys. -/
theorem drop_mem_step {α : Type} {keys : List α} (hnd : keys.Nodup) {i : Nat} {key : α}
    (hi : keys[i]? = some key) :
    key ∈ keys.drop i ∧ ∀ k ∈ keys.drop (i + 1), k ≠ key ∧ k ∈ keys.drop i := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hi
  have heq : keys.drop i = key :: keys.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hlt, hget]
  have hnd' : (keys.drop i).Nodup := hnd.sublist (List.drop_sublist i keys)
  rw [heq] at hnd'
  rw [heq]
  refine ⟨by simp, fun k hk => ⟨fun h => ?_, by simp [hk]⟩⟩
  subst h; exact (List.nodup_cons.1 hnd').1 hk

/-- **Ranging over a `mapOrNil` map, consuming each entry's `S`** (`Stop`'s loops), with a loop
resource `I` (the loop variable's cell): the body of an entry `k ↦ v`, given `S k v`, executes. -/
theorem wp_range_mapOrNil {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (key_type elem_type : go.GoType) [IntoValTyped (GF := GF) w64 key_type]
    (m : Loc) (q : Qp) (M : GMap w64 V) (body : GoFunc) (S : w64 → V → IProp GF) (I : IProp GF)
    (Φ : val → IProp GF) :
    ⊢ mapOrNil m q M -∗ ([∗map] k ↦ v ∈ M, S k v) -∗ I -∗
      ((□ ∀ (k : w64) (v : V), ⌜M !! k = some v⌝ -∗ I -∗ S k v -∗
          WP (App (App (Val #body) (Val #k)) (Val #v)) {{ bv, ⌜bv = executeVal⌝ ∗ I }}) ∗
       (mapOrNil m q M -∗ I -∗ Φ executeVal)) -∗
      WP (App (App (Val (map.forRange key_type elem_type)) (Val #m)) (Val #body)) {{ Φ }} := by
  iintro Hm HS HI ⟨#Hb, HΦ⟩
  iunfold mapOrNil at Hm
  icases Hm with (⟨%Hmn, %HMe⟩ | Hm)
  · subst Hmn; subst HMe
    wp_call
    try simp only [show (null : Loc) = map.nil from rfl]
    iapply HΦ $$ [] HI
    iunfold mapOrNil; ileft; ipureintro; exact ⟨rfl, rfl⟩
  iapply wp_map_for_range (fun keys (i : Int) => iprop(⌜0 ≤ i⌝ ∗ I ∗ ∃ M' : GMap w64 V,
      ⌜∀ k ∈ keys.drop i.toNat, M' !! k = M !! k⌝ ∗ [∗map] k ↦ v ∈ M', S k v))
    body key_type elem_type m M (DFrac.own q) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknd⟩
  isplitl [HS HI]
  · isplitr
    · ipureintro; omega
    iframe HI
    iexists M; iframe; ipureintro; intro _ _; rfl
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hki, %Hmv⟩ ⟨%Hi0, HI, %M', %HM', HS⟩
    obtain ⟨hk, hstep⟩ := drop_mem_step Hknd Hki
    have HM'k : M' !! key = some v := by rw [HM' key hk]; exact Hmv
    icases (BigSepM.bigSepM_delete (Φ := S) (m := M') HM'k).1 $$ HS with ⟨Hk, HS⟩
    iapply wp_wand $$ [Hk HI]
    · iapply Hb $$ %key %v %Hmv HI Hk
    iintro %bv ⟨%Hbv, HI⟩
    subst Hbv
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; omega
    iframe HI
    iexists _; iframe HS
    ipureintro
    intro k hk'
    have hn : (i + 1).toNat = i.toNat + 1 := by omega
    rw [hn] at hk'
    obtain ⟨hne, hk2⟩ := hstep k hk'
    rw [← HM' k hk2]
    exact GMap.lookup_delete_ne _ (Ne.symm hne)
  iintro ⟨-, HI, -⟩ Hm
  iapply HΦ $$ [Hm] HI
  iunfold mapOrNil; iright; iexact Hm

end lemmas

end EtcdGrove
end Perennial
