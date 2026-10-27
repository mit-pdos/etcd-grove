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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The record of the transport's maps: their pointers and contents, and the ids whose remotes
took their `R`s from the pool (D43 M5c). -/
abbrev trRec := Loc × Loc × GMap w64 GoInterface × GMap w64 Loc × List w64

/-- The peers' ids (D43 M5c; stage 6d until then: the remotes' and the peers'). -/
abbrev trIds := List w64

/-- **A member's no-remote token** at the fraction `q` (D22 J-T; `q = 1` the token, exclusive). -/
def trTokAt (γk : GName) (f : w64) (q : Qp) : IProp GF :=
  ghostMapElem γk f (DFrac.own q) ()

/-- An entry of the pool of `R`s (D43 M5c; its token, D22 J-T): once a remote of `id` took its
`R`s (`id ∈ T`), `id`'s no-remote token; until then four `R`s and the token unless `id` is a peer
(the token's holder, `CutPeer`'s caller, knows `id` has no remote), or the transport stopped. -/
def trPoolE (R : IProp GF) (γk : GName) (rm : Loc) (PM : GMap w64 GoInterface) (T : List w64)
    (id : w64) : IProp GF :=
  iprop((⌜id ∈ T⌝ ∗ trTokAt γk id 1) ∨
    (⌜id ∉ T⌝ ∗ ((R ∗ R ∗ R ∗ R ∗ (trTokAt γk id 1 ∨ ⌜(PM !! id).isSome⌝)) ∨ ⌜rm = null⌝)))

/-- **The pool of `R`s for the remotes** (D43 M5c): an entry for each id of `L` (no repeats; D22
J-T), `T` the ids whose remotes took theirs, among `L`. -/
def trPool (R : IProp GF) (γk : GName) (rm : Loc) (PM : GMap w64 GoInterface) (L T : List w64) :
    IProp GF :=
  iprop(⌜(∀ id ∈ T, id ∈ L) ∧ L.Nodup⌝ ∗ [∗list] id ∈ L, trPoolE (GF := GF) R γk rm PM T id)

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
    ⌜(sb = false → pm ≠ null ∧ rm ≠ null) ∧ (rm ≠ null → ∀ id, id ∈ rs ↔ (PM !! id).isSome) ∧
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

/-- **The transport's stop rights** (see the file header); (D22 J-T) the no-remote tokens' map
`γk` (one token per id of `L`, each in its pool entry or given out) and the opening flag `γo`:
while not opened (`trUnopened`, the owner's, `NewServer`'s until its `AddPeer`s are done) no
remote took its `R`s, so `AddPeer` of an id of `L` gives its token out; once opened
(`trOpened`, persistent, what `AddRemote` and `Handler` take) remotes may be started. -/
def trStopInv (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64) (γk γo : GName) :
    IProp GF :=
  inv trStopN iprop(∃ (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc)
      (T : List w64) (b : Bool),
    ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, T) : trRec) ∗
    ([∗map] id ↦ pi ∈ PM, ∃ p : Loc,
      ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗ peerStop Rh id R p) ∗
    ([∗map] id ↦ g ∈ RM, remoteStop Rh id R g) ∗ trPool R γk rm PM L T ∗
    ghostMapAuth γk 1 (GMap.listToSet L) ∗ dghostVar γo (DFrac.own (1 : Qp).half) b ∗
    ⌜b = false → T = []⌝ ∗ (if b then dghostVar γo DFrac.discard true else iprop(True)))

instance trStopInv_persistent (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64)
    (γk γo : GName) : Persistent (trStopInv Rh R γs L γk γo) := by
  unfold trStopInv; infer_instance

/-- **Not yet opened** (exclusive; D22 J-T): no remote has taken its `R`s yet. -/
def trUnopenedAt (γo : GName) : IProp GF := dghostVar γo (DFrac.own (1 : Qp).half) false

/-- **Opened** (persistent; D22 J-T): a remote may take its `R`s. -/
def trOpenedAt (γo : GName) : IProp GF := dghostVar γo DFrac.discard true

instance trOpenedAt_persistent (γo : GName) : Persistent (trOpenedAt (GF := GF) γo) := by
  unfold trOpenedAt; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-! ### The pool's entries (D22 J-T) -/

/-- An entry at a new record: the same taken state, the id a peer if it was, the remotes `nil`
if they were. -/
theorem trPoolE_mono (R : IProp GF) (γk : GName) (rm rm' : Loc) (PM PM' : GMap w64 GoInterface)
    (T T' : List w64) (x : w64) (hT : x ∈ T' ↔ x ∈ T)
    (hPM : (PM !! x).isSome → (PM' !! x).isSome) (hrm : rm = null → rm' = null) :
    trPoolE (GF := GF) R γk rm PM T x ⊢ trPoolE R γk rm' PM' T' x := by
  unfold trPoolE
  iintro (⟨%Hin, Htok⟩ | ⟨%Hn, (⟨HR1, HR2, HR3, HR4, (Htok | %Hp)⟩ | %Hnull)⟩)
  · ileft; iframe; ipureintro; exact hT.2 Hin
  · iright; isplitr; · ipureintro; exact fun h => Hn (hT.1 h)
    ileft; iframe
  · iright; isplitr; · ipureintro; exact fun h => Hn (hT.1 h)
    ileft; iframe; iright; ipureintro; exact hPM Hp
  · iright; isplitr; · ipureintro; exact fun h => Hn (hT.1 h)
    iright; ipureintro; exact hrm Hnull

/-- The entries of a duplicate-free list, one member's out, the others' changed by `h`. -/
theorem bigSepL_nodup_split {Φ Ψ : w64 → IProp GF} (L : List w64) (hnd : L.Nodup) (f : w64)
    (hf : f ∈ L) (h : ∀ x ∈ L, x ≠ f → Φ x ⊢ Ψ x) :
    ([∗list] x ∈ L, Φ x) ⊢ Φ f ∗ (Ψ f -∗ [∗list] x ∈ L, Ψ x) := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hf
  have hnd' := hnd
  rw [List.nodup_append] at hnd'
  obtain ⟨-, hn2, hdisj⟩ := hnd'
  have hf1 : f ∉ l₁ := fun h => hdisj f h f List.mem_cons_self rfl
  have hf2 : f ∉ l₂ := (List.nodup_cons.1 hn2).1
  have h1 : ([∗list] x ∈ l₁, Φ x) ⊢ [∗list] x ∈ l₁, Ψ x :=
    BigSepL.bigSepL_mono (fun {_ x} hk => h x (List.mem_append_left _ (List.mem_of_getElem? hk))
      (fun e => hf1 (e ▸ List.mem_of_getElem? hk)))
  have h2 : ([∗list] x ∈ l₂, Φ x) ⊢ [∗list] x ∈ l₂, Ψ x :=
    BigSepL.bigSepL_mono (fun {_ x} hk => h x
      (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_of_getElem? hk)))
      (fun e => hf2 (e ▸ List.mem_of_getElem? hk)))
  iintro H
  icases BigSepL.bigSepL_append.1 $$ H with ⟨H1, H2⟩
  icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨Hf, H2⟩
  ihave H1 := h1 $$ H1
  ihave H2 := h2 $$ H2
  iframe Hf
  iintro Hf
  iapply BigSepL.bigSepL_append.2
  iframe H1
  iapply BigSepL.bigSepL_cons.2
  iframe

/-- A pool at a new record where every entry is as `trPoolE_mono`'s. -/
theorem trPool_mono (R : IProp GF) (γk : GName) (rm rm' : Loc) (PM PM' : GMap w64 GoInterface)
    (L T : List w64) (hPM : ∀ x, (PM !! x).isSome → (PM' !! x).isSome)
    (hrm : rm = null → rm' = null) :
    trPool (GF := GF) R γk rm PM L T ⊢ trPool R γk rm' PM' L T := by
  unfold trPool
  iintro ⟨%Hp, H⟩
  iframe %Hp
  iapply BigSepL.bigSepL_mono (fun {_ x} _ =>
    trPoolE_mono R γk rm rm' PM PM' T T x Iff.rfl (hPM x) hrm) $$ H

/-- An entry after the transport stopped. -/
theorem trPoolE_stopped (R : IProp GF) (γk : GName) (rm : Loc) (PM PM' : GMap w64 GoInterface)
    (T : List w64) (x : w64) :
    trPoolE (GF := GF) R γk rm PM T x ⊢ trPoolE R γk null PM' T x := by
  unfold trPoolE
  iintro (⟨%Hin, Htok⟩ | ⟨%Hn, -⟩)
  · ileft; iframe; ipureintro; exact Hin
  · iright; isplitr; · ipureintro; exact Hn
    iright; ipureintro; rfl

/-- A pool after the transport stopped. -/
theorem trPool_stopped (R : IProp GF) (γk : GName) (rm : Loc) (PM PM' : GMap w64 GoInterface)
    (L T : List w64) :
    trPool (GF := GF) R γk rm PM L T ⊢ trPool R γk null PM' L T := by
  unfold trPool
  iintro ⟨%Hp, H⟩
  iframe %Hp
  iapply BigSepL.bigSepL_mono (fun {_ x} _ => trPoolE_stopped R γk rm PM PM' T x) $$ H

/-! ### The ghost steps -/

/-- **A peer added** (`AddPeer`, under the write lock, its half of the record): the record gets
it, and the stop invariant its stop right; (D22 J-T) the peer's no-remote token given out if its
entry holds it, or, if a remote of it took its `R`s, the transport opened. -/
theorem trStop_add_peer (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64)
    (γk γo : GName) (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (T : List w64)
    (id : w64) (p : Loc) (hn : PM !! id = none) :
    ⊢ trStopInv Rh R γs L γk γo -∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, T) : trRec) -∗
      peerStop Rh id R p -∗ £ 1 ={⊤}=∗
      ghostVar γs (1 : Qp).half ((pm, rm,
        <[id := interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p]> PM, RM, T) : trRec) ∗
      (⌜id ∉ L⌝ ∨ trTokAt γk id 1 ∨ trOpenedAt γo ∨ ⌜rm = null⌝) := by
  iintro #Hinv Hg Hst Hlc
  unfold trStopInv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  icases Hi with ⟨%pm', %rm', %PM', %RM', %T', %b, Hg', Hps, Hrs, Hpool, Hak, Hob, %Hb,
    Hbw⟩
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  cases Hag
  imod ghostVar_update_halves ((pm, rm,
      <[id := interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p]> PM, RM, T) : trRec) γs _ _
    $$ Hg Hg' with ⟨Hg, Hg'⟩
  iunfold trPool at Hpool
  icases Hpool with ⟨%HTL, Hpool⟩
  have hPM : ∀ x, (PM !! x).isSome →
      ((<[id := interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p]> PM) !! x).isSome := by
    intro x hx
    by_cases hxi : x = id
    · subst hxi; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxi)]; exact hx
  by_cases hL : id ∈ L
  · icases bigSepL_nodup_split (Φ := fun x => trPoolE R γk rm PM T x)
        (Ψ := fun x => trPoolE R γk rm
          (<[id := interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p]> PM) T x) L HTL.2 id hL
        (fun x _ _ => trPoolE_mono R γk rm rm PM _ T T x Iff.rfl (hPM x) (fun h => h)) $$ Hpool
      with ⟨He, Hpool⟩
    iunfold trPoolE at He
    icases He with (⟨%Hin, Htok⟩ | ⟨%Hn, He⟩)
    · -- a remote took its `R`s: the transport opened
      have hb : b = true := by
        cases b with
        | true => rfl
        | false => rw [Hb rfl] at Hin; simp at Hin
      subst hb
      ihave #Hbw' : iprop(dghostVar γo DFrac.discard true) $$ [Hbw]
      · simp only [↓reduceIte]; iexact Hbw
      imod Hclose $$ [Hg' Hps Hrs Hpool Hst Htok Hak Hob] with -
      · inext
        iexists pm, rm, _, RM, T, true
        iframe Hg' Hrs Hak Hob
        isplitl [Hps Hst]
        · iapply (BigSepM.bigSepM_insert hn).2
          iframe Hps
          iexists p
          iframe Hst
          ipureintro; rfl
        isplitl [Hpool Htok]
        · iunfold trPool
          isplitr
          · ipureintro; exact HTL
          iapply Hpool
          iunfold trPoolE; ileft; iframe; ipureintro; exact Hin
        isplitr
        · ipureintro; exact Hb
        simp only [↓reduceIte]; iexact Hbw'
      imodintro
      iframe
      iright; iright; ileft
      simp only [↓reduceIte]
      iunfold trOpenedAt; iexact Hbw'
    · icases He with (⟨HR1, HR2, HR3, HR4, (Htok | %Hp)⟩ | %Hnull)
      · imod Hclose $$ [Hg' Hps Hrs Hpool Hst HR1 HR2 HR3 HR4 Hak Hob Hbw] with -
        · inext
          iexists pm, rm, _, RM, T, b
          iframe Hg' Hrs Hak Hob Hbw
          isplitl [Hps Hst]
          · iapply (BigSepM.bigSepM_insert hn).2
            iframe Hps
            iexists p
            iframe Hst
            ipureintro; rfl
          isplitl [Hpool HR1 HR2 HR3 HR4]
          · iunfold trPool
            isplitr
            · ipureintro; exact HTL
            iapply Hpool
            iunfold trPoolE; iright
            isplitr
            · ipureintro; exact Hn
            ileft; iframe; (try (iright; ipureintro; simp))
          ipureintro; exact Hb
        imodintro
        iframe
      · rw [hn] at Hp; exact absurd Hp (by simp)
      · imod Hclose $$ [Hg' Hps Hrs Hpool Hst Hak Hob Hbw] with -
        · inext
          iexists pm, rm, _, RM, T, b
          iframe Hg' Hrs Hak Hob Hbw
          isplitl [Hps Hst]
          · iapply (BigSepM.bigSepM_insert hn).2
            iframe Hps
            iexists p
            iframe Hst
            ipureintro; rfl
          isplitl [Hpool]
          · iunfold trPool
            isplitr
            · ipureintro; exact HTL
            iapply Hpool
            iunfold trPoolE; iright
            isplitr
            · ipureintro; exact Hn
            iright; ipureintro; exact Hnull
          ipureintro; exact Hb
        imodintro
        iframe
        iright; iright; iright; ipureintro; exact Hnull
  · imod Hclose $$ [Hg' Hps Hrs Hpool Hst Hak Hob Hbw] with -
    · inext
      iexists pm, rm, _, RM, T, b
      iframe Hg' Hrs Hak Hob Hbw
      isplitl [Hps Hst]
      · iapply (BigSepM.bigSepM_insert hn).2
        iframe Hps
        iexists p
        iframe Hst
        ipureintro; rfl
      isplitl [Hpool]
      · iapply trPool_mono R γk rm rm PM _ L T hPM (fun h => h)
        iunfold trPool
        iframe Hpool
        ipureintro; exact HTL
      ipureintro; exact Hb
    imodintro
    iframe
    ileft; ipureintro; exact hL

/-- **A remote added** (`AddRemote`, under the write lock): the record gets it, the stop invariant
its stop right. -/
theorem trStop_add_remote (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64)
    (γk γo : GName) (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (T : List w64)
    (id : w64) (g : Loc) (hn : RM !! id = none) :
    ⊢ trStopInv Rh R γs L γk γo -∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, T) : trRec) -∗
      remoteStop Rh id R g ={⊤}=∗
      ghostVar γs (1 : Qp).half ((pm, rm, PM, <[id := g]> RM, T) : trRec) := by
  iintro #Hinv Hg Hst
  unfold trStopInv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%pm', %rm', %PM', %RM', %T', %b, >Hg', Hps, Hrs, Hpool, Hak, Hob, Hb, Hbw⟩
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  cases Hag
  imod ghostVar_update_halves ((pm, rm, PM, <[id := g]> RM, T) : trRec) γs _ _ $$ Hg Hg'
    with ⟨Hg, Hg'⟩
  imod Hclose $$ [Hg' Hps Hrs Hst Hpool Hak Hob Hb Hbw] with -
  · inext
    iexists pm, rm, PM, _, T, b
    iframe Hg' Hps Hpool Hak Hob Hb Hbw
    iapply (BigSepM.bigSepM_insert hn).2
    iframe
  imodintro
  iexact Hg

/-- **The transport stopped** (`Stop`, under the write lock): the peers' and remotes' stop rights
leave the stop invariant, whose record (and the lock's half) becomes the empty one. -/
theorem trStop_take (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64) (γk γo : GName)
    (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (T : List w64) :
    ⊢ trStopInv Rh R γs L γk γo -∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, T) : trRec) -∗
      £ 1 -∗ £ 1 ={⊤}=∗
      ghostVar γs (1 : Qp).half (((null : Loc), (null : Loc), ∅, ∅, T) : trRec) ∗
      ([∗map] id ↦ pi ∈ PM, ∃ p : Loc,
        ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗ peerStop Rh id R p) ∗
      ([∗map] id ↦ g ∈ RM, remoteStop Rh id R g) := by
  iintro #Hinv Hg Hlc1 Hlc2
  unfold trStopInv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%pm', %rm', %PM', %RM', %T', %b, >Hg', Hps, Hrs, Hpool, Hak, Hob, Hb, Hbw⟩
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  cases Hag
  imod ghostVar_update_halves (((null : Loc), (null : Loc), ∅, ∅, T) : trRec) γs _ _ $$ Hg Hg'
    with ⟨Hg, Hg'⟩
  imod Hclose $$ [Hg' Hpool Hak Hob Hb Hbw] with -
  · inext
    iexists null, null, ∅, ∅, T, b
    iframe Hg' Hak Hob Hb Hbw
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    iapply trPool_stopped R γk rm PM ∅ L T $$ Hpool
  imod lc_fupd_elim_later $$ Hlc1 Hps with Hps
  imod lc_fupd_elim_later $$ Hlc2 Hrs with Hrs
  imodintro
  iframe

/-- **The four `R`s of `id`'s remote, from the pool** (`AddRemote`, under the write lock of a
transport not stopped and opened, the remotes' record without `id`, which is in `L` and no peer):
the record's taken ids gain `id`, its entry its token. -/
theorem trStop_pool_take (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64)
    (γk γo : GName) (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (T : List w64)
    (id : w64) (hn : id ∉ T) (hL : id ∈ L) (hrm : rm ≠ null) (hpm : PM !! id = none) :
    ⊢ trStopInv Rh R γs L γk γo -∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, T) : trRec) -∗
      trOpenedAt γo -∗ £ 1 ={⊤}=∗
      ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, id :: T) : trRec) ∗ R ∗ R ∗ R ∗ R := by
  iintro #Hinv Hg #Hop Hlc
  unfold trStopInv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  icases Hi with ⟨%pm', %rm', %PM', %RM', %T', %b, Hg', Hps, Hrs, Hpool, Hak, Hob, %Hb, Hbw⟩
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  cases Hag
  iunfold trOpenedAt at Hop
  ihave %Hbt := dghostVar_agree γo _ _ _ _ $$ Hop Hob
  subst Hbt
  imod ghostVar_update_halves ((pm, rm, PM, RM, id :: T) : trRec) γs _ _ $$ Hg Hg'
    with ⟨Hg, Hg'⟩
  iunfold trPool at Hpool
  icases Hpool with ⟨%HTL, Hpool⟩
  icases bigSepL_nodup_split (Φ := fun x => trPoolE R γk rm PM T x)
      (Ψ := fun x => trPoolE R γk rm PM (id :: T) x) L HTL.2 id hL
      (fun x _ hx => trPoolE_mono R γk rm rm PM PM T (id :: T) x
        (by simp only [List.mem_cons, hx, false_or]) (fun h => h) (fun h => h)) $$ Hpool
    with ⟨He, Hpool⟩
  iunfold trPoolE at He
  icases He with (⟨%Hin, -⟩ | ⟨-, (⟨HR1, HR2, HR3, HR4, (Htok | %Hp)⟩ | %Hnull)⟩)
  · exact absurd Hin hn
  · imod Hclose $$ [Hg' Hps Hrs Hpool Htok Hak Hob Hbw] with -
    · inext
      iexists pm, rm, PM, RM, id :: T, true
      iframe Hg' Hps Hrs Hak Hob Hbw
      isplitl [Hpool Htok]
      · iunfold trPool
        isplitr
        · ipureintro
          refine ⟨fun x hx => ?_, HTL.2⟩
          rcases List.mem_cons.1 hx with hx | hx
          · subst hx; exact hL
          · exact HTL.1 x hx
        iapply Hpool
        iunfold trPoolE; ileft; iframe; ipureintro; exact List.mem_cons_self
      ipureintro; intro h; cases h
    imodintro
    iframe
  · rw [hpm] at Hp; exact absurd Hp (by simp)
  · exact absurd Hnull hrm

/-- **The taken ids are among `L`** (any share of the record): a remote is only started for an id
of `L`. -/
theorem trStop_taken_sub (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64)
    (γk γo : GName) (r : trRec) (q : Qp) :
    ⊢ trStopInv Rh R γs L γk γo -∗ ghostVar γs q r ={⊤}=∗
      ghostVar γs q r ∗ ⌜∀ id ∈ r.2.2.2.2, id ∈ L⌝ := by
  iintro #Hinv Hg
  unfold trStopInv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%pm', %rm', %PM', %RM', %T', %b, >Hg', Hps, Hrs, Hpool, Hak, Hob, Hb, Hbw⟩
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  iunfold trPool at Hpool
  icases Hpool with ⟨>%HTL, Hpool⟩
  imod Hclose $$ [Hg' Hps Hrs Hpool Hak Hob Hb Hbw] with -
  · inext
    iexists pm', rm', PM', RM', T', b
    iframe Hg' Hps Hrs Hak Hob Hb Hbw
    iunfold trPool
    iframe Hpool
    ipureintro; exact HTL
  imodintro
  iframe Hg
  ipureintro
  subst Hag
  exact HTL.1

/-- **The token's holder knows its id has no remote** (D22 J-T; `CutPeer`, `MendPeer`, under the
read lock: any share of the record): the id is not among the taken ones. -/
theorem trTok_noRemote (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64)
    (γk γo : GName) (r : trRec) (q : Qp) (f : w64) :
    ⊢ trStopInv Rh R γs L γk γo -∗ ghostVar γs q r -∗ trTokAt γk f 1 -∗ £ 1 ={⊤}=∗
      ghostVar γs q r ∗ trTokAt γk f 1 ∗ ⌜f ∉ r.2.2.2.2⌝ := by
  iintro #Hinv Hg Htok Hlc
  unfold trStopInv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  icases Hi with ⟨%pm', %rm', %PM', %RM', %T', %b, Hg', Hps, Hrs, Hpool, Hak, Hob, Hb, Hbw⟩
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  subst Hag
  iunfold trTokAt at Htok
  ihave %Hlk := ghost_map_lookup $$ Hak Htok
  have hf : f ∈ L := (GMap.elem_of_list_to_set f L).1 (by rw [GMap.mem_iff]; simp [Hlk])
  iunfold trPool at Hpool
  icases Hpool with ⟨%HTL, Hpool⟩
  icases BigSepL.bigSepL_mem_acc (Φ := fun x => trPoolE R γk rm' PM' T' x) hf $$ Hpool
    with ⟨He, Hpool⟩
  iunfold trPoolE at He
  icases He with (⟨%Hin, Htok'⟩ | ⟨%Hn, He⟩)
  · iunfold trTokAt at Htok'
    ihave %Hv := ghostMapElem_valid_2 f γk _ _ _ _ $$ Htok Htok'
    exact absurd Hv.1 (dfrac_own_one_op_invalid _)
  imod Hclose $$ [Hg' Hps Hrs Hpool He Hak Hob Hb Hbw] with -
  · inext
    iexists pm', rm', PM', RM', T', b
    iframe Hg' Hps Hrs Hak Hob Hb Hbw
    iunfold trPool
    isplitr
    · ipureintro; exact HTL
    iapply Hpool
    iunfold trPoolE; iright; iframe; ipureintro; exact Hn
  imodintro
  iunfold trTokAt
  iframe
  ipureintro; exact Hn

/-- **No remote for `f`** (D22 J-T; `CutPeer`, `MendPeer`, under the read lock): not one of the
budgeted ids, or its token held. -/
theorem trTokOr_noRemote (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64)
    (γk γo : GName) (r : trRec) (q : Qp) (f : w64) :
    ⊢ trStopInv Rh R γs L γk γo -∗ ghostVar γs q r -∗ (⌜f ∉ L⌝ ∨ trTokAt γk f 1) -∗ £ 1 ={⊤}=∗
      ghostVar γs q r ∗ (⌜f ∉ L⌝ ∨ trTokAt γk f 1) ∗ ⌜f ∉ r.2.2.2.2⌝ := by
  iintro #Hinv Hg Htk Hlc
  icases Htk with (%HnL | Htok)
  · imod trStop_taken_sub Rh R γs L γk γo r q $$ Hinv Hg with ⟨Hg, %HTL⟩
    imodintro
    iframe
    isplitr
    · ileft; ipureintro; exact HnL
    ipureintro; exact fun h => HnL (HTL f h)
  · imod trTok_noRemote Rh R γs L γk γo r q f $$ Hinv Hg Htok Hlc with ⟨Hg, Htok, %Hn⟩
    imodintro
    iframe
    ipureintro; exact Hn

/-- **The transport opened** (D22 J-T; the owner's, once its `AddPeer`s are done): remotes may
take their `R`s from now on. -/
theorem trOpen (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64) (γk γo : GName) :
    ⊢ trStopInv Rh R γs L γk γo -∗ trUnopenedAt γo ={⊤}=∗ trOpenedAt γo := by
  iintro #Hinv Hu
  unfold trStopInv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%pm', %rm', %PM', %RM', %T', %b, Hg', Hps, Hrs, Hpool, Hak, >Hob, Hb, Hbw⟩
  iunfold trUnopenedAt at Hu
  imod dghostVar_update_halves true γo _ _ $$ Hu Hob with ⟨Hu, Hob⟩
  imod dghostVar_persist γo _ _ $$ Hu with #Hu
  imod Hclose $$ [Hg' Hps Hrs Hpool Hak Hob] with -
  · inext
    iexists pm', rm', PM', RM', T', true
    iframe Hg' Hps Hrs Hpool Hak Hob
    isplitr
    · ipureintro; intro h; cases h
    simp only [↓reduceIte]
    iexact Hu
  imodintro
  iunfold trOpenedAt
  iexact Hu

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
