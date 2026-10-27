/-
**The transport's lock and its stop rights** (rafthttp stage 6c; D39). Lean-first.
* `trLockP` (fractional, `t.mu`'s, an `RWMutex`): the `peers` and `remotes` maps (each `nil` once
  `Stop` ran: `mapOrNil`), their entries' facts (`peerOk`, `remoteOk`, persistent), half of a
  ghost record `γs` of the maps and of the ids whose remotes took their `R`s from the pool
  (`trRec`; the remotes' keys exactly, until `Stop`), and half of a ghost record `γr`: the peers'
  ids (D43 M5c: the owner's `AddPeer`/`RemovePeer`/`RemoveAllPeers` change them; the peers' keys
  cover them until `Stop` empties the maps) and whether `Stop` ran (the maps are not `nil` until
  it does); the other half with the owner (`trLive`: not stopped), or in an invariant once frozen
  (`trRemotesFrozen`: the ids for good, `Stop` sets the flag); and (D43 M5a, 2026-10-26) the
  leader's stats' followers' map (`trStats`: `AddPeer`'s `Follower` and `removePeer`'s `delete`
  write it, both under the write lock).
* `trStopInv` (an invariant): the other half of the record, with the right to stop each peer and
  remote it lists (`peerStop`, `remoteStop`): `AddPeer`/`AddRemote` add one under the write lock,
  `Stop` takes them all under it; and (D43 M5c) the pool of `R`s for the remotes (`trPool`): four
  for each id of the list `L` that `Start` was given, until a remote of that id takes them
  (`AddRemote`, any lock holder: a handler's for a sender that is no peer). A remote is only ever
  started for an id of `L` (what `CutPeer` and `MendPeer` need, `id ∉ L`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Defs

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

/-- The record of the transport's maps: their pointers and contents, and the ids whose remotes
took their `R`s from the pool (D43 M5c). -/
abbrev trRec := Loc × Loc × GMap w64 GoInterface × GMap w64 Loc × List w64

/-- The peers' ids (D43 M5c; stage 6d until then: the remotes' and the peers'). -/
abbrev trIds := List w64

/-- An entry of the pool of `R`s (D43 M5c): four `R`s for the remote of `id`, or taken. -/
def trPoolE (R : IProp GF) (T : List w64) (id : w64) : IProp GF :=
  iprop(⌜id ∈ T⌝ ∨ (R ∗ R ∗ R ∗ R))

/-- **The pool of `R`s for the remotes** (D43 M5c): four for each id of `L` whose remote has not
taken them (`T`, the ids that did, among `L`). -/
def trPool (R : IProp GF) (L T : List w64) : IProp GF :=
  iprop(⌜∀ id ∈ T, id ∈ L⌝ ∗ [∗list] id ∈ L, trPoolE (GF := GF) R T id)

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

/-- The transport's leader stats (`t.LeaderStats`) with their followers' map at the fraction `q`
(D43 M5a). -/
def trStats (t : Loc) (q : Qp) : IProp GF :=
  iprop(∃ ls : Loc, t.[rafthttp.Transport, go!"LeaderStats"] ↦□ ls ∗ v2stats.isLeaderStats ls ∗
    v2stats.lsFollowers ls q)

instance trStats_fractional (t : Loc) : Fractional (trStats (GF := GF) t) where
  fractional q1 q2 := by
    unfold trStats
    refine ⟨?_, ?_⟩
    · iintro ⟨%ls, #Hl, #Hi, Hf⟩
      icases ((v2stats.lsFollowers_fractional (GF := GF) ls).fractional q1 q2).1 $$ Hf
        with ⟨H1, H2⟩
      isplitl [H1]
      · iexists ls; iframe; iframe #
      · iexists ls; iframe; iframe #
    · iintro ⟨⟨%ls, #Hl, #Hi, H1⟩, ⟨%ls', #Hl', -, H2⟩⟩
      ihave %Hla := typedPointsto_agree_wand _ _ _ _ _ $$ Hl Hl'
      subst Hla
      iexists ls
      iframe #
      iapply ((v2stats.lsFollowers_fractional (GF := GF) ls).fractional q1 q2).2
      iframe

/-- **What the transport `t`'s mutex guards** at the fraction `q` (see the file header). -/
def trLockP (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs γr : GName)
    (q : Qp) : IProp GF :=
  iprop(∃ (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (T : List w64)
      (rs : trIds) (sb : Bool),
    t.[rafthttp.Transport, go!"peers"] ↦{DFrac.own q} pm ∗
    t.[rafthttp.Transport, go!"remotes"] ↦{DFrac.own q} rm ∗
    mapOrNil pm q PM ∗ mapOrNil rm q RM ∗ ghostVar γs q.half ((pm, rm, PM, RM, T) : trRec) ∗
    ghostVar γr q.half (rs, sb) ∗
    ⌜(sb = false → pm ≠ null ∧ rm ≠ null) ∧ (rm ≠ null → ∀ id ∈ rs, (PM !! id).isSome) ∧
      (rm ≠ null → ∀ id, (RM !! id).isSome ↔ id ∈ T)⌝ ∗
    □ peersOk Rh lid γd R PM ∗ □ remotesOk Rh lid R RM ∗ trStats t q)

/-- **A reader's token of the transport's mutex** (exclusive): what `RLock` takes; `Start` gives a
supply of them (`Send`'s caller, each handler invocation's `Get`, `CutPeer`'s and `MendPeer`'s). -/
def trReadTok (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF)
    (γs γr : GName) : IProp GF :=
  sync.ownRWMutex (t.[rafthttp.Transport, go!"mu"]) (trLockP Rh t lid γd R γs γr)

def trRemN : Namespace := nroot.@"rafthttp_tr_remotes"

/-- **The peers' ids `rs`, for good** (persistent): the half of `γr` no longer with the owner
(`trLive`: no more `AddPeer`, `RemovePeer`). (D43 M5e, 2026-10-26, the user's (B): a quarter
always here, the other quarter the stop token `trFrozenTok` while not stopped, here once
stopped: `Stop` takes the token.) -/
def trRemotesFrozen (γr : GName) (rs : trIds) : IProp GF :=
  inv trRemN iprop(∃ sb : Bool, ghostVar (GF := GF) γr (1 : Qp).half.half (rs, sb) ∗
    (if sb then ghostVar (GF := GF) γr (1 : Qp).half.half (rs, sb) else iprop(True)))

/-- **The frozen transport's stop token** (exclusive; D43 M5e, 2026-10-26, the user's (B)): the
quarter of `γr` at "not stopped" that `Stop` takes; its holder (the static server's apply thread)
knows the transport is not stopped (`AddPeer_frozen`). -/
def trFrozenTok (γr : GName) (rs : trIds) : IProp GF :=
  ghostVar (GF := GF) γr (1 : Qp).half.half (rs, false)

instance trRemotesFrozen_persistent (γr : GName) (rs : trIds) :
    Persistent (trRemotesFrozen (GF := GF) γr rs) := by
  unfold trRemotesFrozen; infer_instance

def trStopN : Namespace := nroot.@"rafthttp_tr_stop"

/-- **The transport's stop rights** (see the file header). -/
def trStopInv (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64) : IProp GF :=
  inv trStopN iprop(∃ (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc)
      (T : List w64),
    ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, T) : trRec) ∗
    ([∗map] id ↦ pi ∈ PM, ∃ p : Loc,
      ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗ peerStop Rh id R p) ∗
    ([∗map] id ↦ g ∈ RM, remoteStop Rh id R g) ∗ trPool R L T)

instance trStopInv_persistent (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64) :
    Persistent (trStopInv Rh R γs L) := by
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
    · iintro ⟨%pm, %rm, %PM, %RM, %T, %rs, %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro,
        Hts⟩
      icases ((trStats_fractional (GF := GF) t).fractional q1 q2).1 $$ Hts with ⟨Hts1, Hts2⟩
      icases (hgr (rs, sb)).1 $$ Hgr with ⟨Hgr1, Hgr2⟩
      icases (hpt pm _).1 $$ Hp with ⟨Hp1, Hp2⟩
      icases (hpt rm _).1 $$ Hr with ⟨Hr1, Hr2⟩
      icases (mapOrNil_fractional pm PM q1 q2).1 $$ Hpm with ⟨Hpm1, Hpm2⟩
      icases (mapOrNil_fractional rm RM q1 q2).1 $$ Hrm with ⟨Hrm1, Hrm2⟩
      icases (hgv (pm, rm, PM, RM, T)).1 $$ Hg with ⟨Hg1, Hg2⟩
      isplitl [Hp1 Hr1 Hpm1 Hrm1 Hg1 Hgr1 Hts1]
      · iexists pm, rm, PM, RM, T, rs, sb; iframe; iframe #; ipureintro; exact Hrs
      · iexists pm, rm, PM, RM, T, rs, sb; iframe; iframe #; ipureintro; exact Hrs
    · iintro ⟨⟨%pm, %rm, %PM, %RM, %T, %rs, %sb, Hp1, Hr1, Hpm1, Hrm1, Hg1, Hgr1, %Hrs, #Hpo,
          #Hro, Hts1⟩,
        ⟨%pm', %rm', %PM', %RM', %T', %rs', %sb', Hp2, Hr2, Hpm2, Hrm2, Hg2, Hgr2, -, -, -, Hts2⟩⟩
      ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg1 Hg2
      ihave %Hagr := ghostVar_agree γr _ _ _ _ $$ Hgr1 Hgr2
      cases Hag
      cases Hagr
      iexists pm, rm, PM, RM, T, rs, sb
      isplitl [Hp1 Hp2]
      · iapply (hpt pm _).2; iframe
      isplitl [Hr1 Hr2]
      · iapply (hpt rm _).2; iframe
      isplitl [Hpm1 Hpm2]
      · iapply (mapOrNil_fractional pm PM q1 q2).2; iframe
      isplitl [Hrm1 Hrm2]
      · iapply (mapOrNil_fractional rm RM q1 q2).2; iframe
      isplitl [Hg1 Hg2]
      · iapply (hgv (pm, rm, PM, RM, T)).2; iframe
      isplitl [Hgr1 Hgr2]
      · iapply (hgr (rs, sb)).2; iframe
      isplitr
      · ipureintro; exact Hrs
      iframe #
      iapply ((trStats_fractional (GF := GF) t).fractional q1 q2).2
      iframe

/-- A `nil` map of `mapOrNil` is empty. -/
theorem mapOrNil_null_empty {V : Type} [ZeroVal V] (m : Loc) (q : Qp) (M : GMap w64 V) :
    mapOrNil (GF := GF) m q M ⊢ ⌜m = null → M = ∅⌝ := by
  iintro H
  iunfold mapOrNil at H
  icases H with (%H | H)
  · ipureintro; intro _; exact H.2
  · ihave %Hnn := ownMap_not_nil m _ _ $$ H
    ipureintro; intro h; exact absurd h Hnn

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
  imod Hi with ⟨%sb', Hi, Hx⟩
  ihave %Hag := ghostVar_agree γr _ _ _ _ $$ Hi Hg
  imod Hclose $$ [Hi Hx] with -
  · iexists sb'; iframe
  imodintro
  iframe
  ipureintro; cases Hag; rfl

/-- **A peer added** (`AddPeer`, under the write lock, its half of the record): the record gets
it, and the stop invariant its stop right. -/
theorem trStop_add_peer (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64)
    (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (T : List w64) (id : w64)
    (p : Loc) (hn : PM !! id = none) :
    ⊢ trStopInv Rh R γs L -∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, T) : trRec) -∗
      peerStop Rh id R p ={⊤}=∗
      ghostVar γs (1 : Qp).half ((pm, rm,
        <[id := interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p]> PM, RM, T) : trRec) := by
  iintro #Hinv Hg Hst
  unfold trStopInv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%pm', %rm', %PM', %RM', %T', Hg', Hps, Hrs, Hpool⟩
  imod Hg' with Hg'
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  cases Hag
  imod ghostVar_update_halves ((pm, rm,
      <[id := interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p]> PM, RM, T) : trRec) γs _ _
    $$ Hg Hg' with ⟨Hg, Hg'⟩
  imod Hclose $$ [Hg' Hps Hrs Hst Hpool] with -
  · inext
    iexists pm, rm, _, RM, T
    iframe Hg' Hrs Hpool
    iapply (BigSepM.bigSepM_insert hn).2
    iframe Hps
    iexists p
    iframe Hst
    ipureintro; rfl
  imodintro
  iexact Hg

/-- **A remote added** (`AddRemote`, under the write lock): the record gets it, the stop invariant
its stop right. -/
theorem trStop_add_remote (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64)
    (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (T : List w64) (id : w64)
    (g : Loc) (hn : RM !! id = none) :
    ⊢ trStopInv Rh R γs L -∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, T) : trRec) -∗
      remoteStop Rh id R g ={⊤}=∗
      ghostVar γs (1 : Qp).half ((pm, rm, PM, <[id := g]> RM, T) : trRec) := by
  iintro #Hinv Hg Hst
  unfold trStopInv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%pm', %rm', %PM', %RM', %T', Hg', Hps, Hrs, Hpool⟩
  imod Hg' with Hg'
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  cases Hag
  imod ghostVar_update_halves ((pm, rm, PM, <[id := g]> RM, T) : trRec) γs _ _ $$ Hg Hg'
    with ⟨Hg, Hg'⟩
  imod Hclose $$ [Hg' Hps Hrs Hst Hpool] with -
  · inext
    iexists pm, rm, PM, _, T
    iframe Hg' Hps Hpool
    iapply (BigSepM.bigSepM_insert hn).2
    iframe
  imodintro
  iexact Hg

/-- **The transport stopped** (`Stop`, under the write lock): the peers' and remotes' stop rights
leave the stop invariant, whose record (and the lock's half) becomes the empty one. -/
theorem trStop_take (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64) (pm rm : Loc)
    (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (T : List w64) :
    ⊢ trStopInv Rh R γs L -∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, T) : trRec) -∗ £ 1 -∗
      £ 1 ={⊤}=∗
      ghostVar γs (1 : Qp).half (((null : Loc), (null : Loc), ∅, ∅, T) : trRec) ∗
      ([∗map] id ↦ pi ∈ PM, ∃ p : Loc,
        ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗ peerStop Rh id R p) ∗
      ([∗map] id ↦ g ∈ RM, remoteStop Rh id R g) := by
  iintro #Hinv Hg Hlc1 Hlc2
  unfold trStopInv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%pm', %rm', %PM', %RM', %T', Hg', Hps, Hrs, Hpool⟩
  imod Hg' with Hg'
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  cases Hag
  imod ghostVar_update_halves (((null : Loc), (null : Loc), ∅, ∅, T) : trRec) γs _ _ $$ Hg Hg'
    with ⟨Hg, Hg'⟩
  imod Hclose $$ [Hg' Hpool] with -
  · inext
    iexists null, null, ∅, ∅, T
    iframe Hg' Hpool
    isplitl
    · iapply BigSepM.bigSepM_empty.2; itrivial
    · iapply BigSepM.bigSepM_empty.2; itrivial
  imod lc_fupd_elim_later $$ Hlc1 Hps with Hps
  imod lc_fupd_elim_later $$ Hlc2 Hrs with Hrs
  imodintro
  iframe

/-- **The transport marked stopped** (`Stop`, under the write lock): both halves of `γr`, the
frozen record's with the stop token (D43 M5e). -/
theorem trRemotes_stop (γr : GName) (rs : trIds) (sb : Bool) :
    ⊢ trRemotesFrozen (GF := GF) γr rs -∗ trFrozenTok γr rs -∗
      ghostVar γr (1 : Qp).half (rs, sb) ={⊤}=∗ ghostVar γr (1 : Qp).half (rs, true) := by
  iintro #Hinv Htk Hg
  unfold trRemotesFrozen trFrozenTok
  iinv Hinv with Hi Hclose
  imod Hi with ⟨%sb', Hi, Hx⟩
  ihave %Hag := ghostVar_agree γr _ _ _ _ $$ Hi Htk
  cases Hag
  ihave Hh := (ghostVar_split_half (GF := GF) γr (1 : Qp).half (rs, false)).2 $$ [Hi Htk]
  · iframe
  imod ghostVar_update_halves (rs, true) γr _ _ $$ Hh Hg with ⟨Hh, Hg⟩
  icases (ghostVar_split_half (GF := GF) γr (1 : Qp).half (rs, true)).1 $$ Hh with ⟨Hi, Hi'⟩
  imod Hclose $$ [Hi Hi'] with -
  · inext; iexists true; iframe Hi; simp only [↓reduceIte]; iexact Hi'
  imodintro
  iexact Hg

/-- **The stop token says "not stopped"** (D43 M5e): with a share of `γr`, its stopped flag is
`false` and its ids the frozen ones. -/
theorem trFrozenTok_agree (γr : GName) (rs rs' : trIds) (sb : Bool) (q : Qp) :
    trFrozenTok (GF := GF) γr rs ∗ ghostVar γr q (rs', sb) ⊢ ⌜rs' = rs ∧ sb = false⌝ := by
  unfold trFrozenTok
  iintro ⟨Ht, Hg⟩
  ihave %Hag := ghostVar_agree γr _ _ _ _ $$ Ht Hg
  ipureintro; cases Hag; exact ⟨rfl, rfl⟩

/-- A pool entry stays one when more ids are taken. -/
theorem trPoolE_mono (R : IProp GF) (T : List w64) (id x : w64) :
    trPoolE R T x ⊢ trPoolE R (id :: T) x := by
  unfold trPoolE
  iintro (%h | H)
  · ileft; ipureintro; exact List.mem_cons_of_mem _ h
  · iright; iexact H

/-- The entries of a pool, with `id` taken: the four `R`s of `id`'s first entry. -/
theorem trPoolL_take (R : IProp GF) (T : List w64) (id : w64) (hn : id ∉ T) :
    ∀ L : List w64, id ∈ L →
      ([∗list] x ∈ L, trPoolE R T x) ⊢ (R ∗ R ∗ R ∗ R) ∗ [∗list] x ∈ L, trPoolE R (id :: T) x
  | [], h => absurd h (by simp)
  | y :: L, h => by
    iintro ⟨Hy, H⟩
    by_cases hy : y = id
    · subst hy
      iunfold trPoolE at Hy
      icases Hy with (%Hin | HR)
      · exact absurd Hin hn
      iframe HR
      isplitr
      · iunfold trPoolE; ileft; ipureintro; exact List.mem_cons_self
      iapply BigSepL.bigSepL_mono_of_forall (fun {_ x} => trPoolE_mono R T y x) $$ H
    · have h' : id ∈ L := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hy
        · exact h
      ihave ⟨HR, H⟩ := trPoolL_take R T id hn L h' $$ H
      iframe HR
      isplitl [Hy]
      · iapply trPoolE_mono $$ Hy
      iexact H

/-- **The four `R`s of `id`'s remote, from the pool** (`AddRemote`, under the write lock, the
remotes' record without `id`, which is in `L`): the record's taken ids gain `id`. -/
theorem trStop_pool_take (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64)
    (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (T : List w64) (id : w64)
    (hn : id ∉ T) (hL : id ∈ L) :
    ⊢ trStopInv Rh R γs L -∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, T) : trRec) -∗ £ 1 ={⊤}=∗
      ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, id :: T) : trRec) ∗ R ∗ R ∗ R ∗ R := by
  iintro #Hinv Hg Hlc
  unfold trStopInv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  icases Hi with ⟨%pm', %rm', %PM', %RM', %T', Hg', Hps, Hrs, Hpool⟩
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  cases Hag
  imod ghostVar_update_halves ((pm, rm, PM, RM, id :: T) : trRec) γs _ _ $$ Hg Hg'
    with ⟨Hg, Hg'⟩
  iunfold trPool at Hpool
  icases Hpool with ⟨%HTL, Hpool⟩
  ihave ⟨HR, Hpool⟩ := trPoolL_take R T id hn L hL $$ Hpool
  imod Hclose $$ [Hg' Hps Hrs Hpool] with -
  · inext
    iexists pm, rm, PM, RM, id :: T
    iframe Hg' Hps Hrs
    iunfold trPool
    iframe Hpool
    ipureintro
    intro x hx
    rcases List.mem_cons.1 hx with hx | hx
    · subst hx; exact hL
    · exact HTL x hx
  imodintro
  iframe

/-- **The taken ids are among `L`** (any share of the record): a remote is only started for an id
of `L`. -/
theorem trStop_taken_sub (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64)
    (r : trRec) (q : Qp) :
    ⊢ trStopInv Rh R γs L -∗ ghostVar γs q r ={⊤}=∗ ghostVar γs q r ∗ ⌜∀ id ∈ r.2.2.2.2, id ∈ L⌝ := by
  iintro #Hinv Hg
  unfold trStopInv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%pm', %rm', %PM', %RM', %T', Hg', Hps, Hrs, Hpool⟩
  imod Hg' with Hg'
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  iunfold trPool at Hpool
  icases Hpool with ⟨HTL, Hpool⟩
  imod HTL with %HTL
  imod Hclose $$ [Hg' Hps Hrs Hpool] with -
  · inext
    iexists pm', rm', PM', RM', T'
    iframe Hg' Hps Hrs
    iunfold trPool
    iframe Hpool
    ipureintro; exact HTL
  imodintro
  iframe Hg
  ipureintro
  subst Hag
  exact HTL

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
