/-
**The transport's lock and its stop rights** (rafthttp stage 6c; D34). Lean-first.
* `trLockP` (fractional, `t.mu`'s, an `RWMutex`): the `peers` and `remotes` maps (each `nil` once
  `Stop` ran: `mapOrNil`), their entries' facts (`peerOk`, `remoteOk`, persistent), and half of a
  ghost record `γs` of the maps (`trRec`).
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
def trLockP (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs : GName)
    (q : Qp) : IProp GF :=
  iprop(∃ (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc),
    t.[rafthttp.Transport, go!"peers"] ↦{DFrac.own q} pm ∗
    t.[rafthttp.Transport, go!"remotes"] ↦{DFrac.own q} rm ∗
    mapOrNil pm q PM ∗ mapOrNil rm q RM ∗ ghostVar γs q.half ((pm, rm, PM, RM) : trRec) ∗
    □ peersOk Rh lid γd R PM ∗ □ remotesOk Rh lid R RM)

/-- **A reader's token of the transport's mutex** (exclusive): what `RLock` takes; `Start` gives a
supply of them (`Send`'s caller, each handler invocation's `Get`, `CutPeer`'s and `MendPeer`'s). -/
def trReadTok (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs : GName) :
    IProp GF :=
  sync.ownRWMutex (t.[rafthttp.Transport, go!"mu"]) (trLockP Rh t lid γd R γs)

def trStopN : Namespace := nroot.@"rafthttp_tr_stop"

/-- **The transport's stop rights** (see the file header). -/
def trStopInv (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) : IProp GF :=
  inv trStopN iprop(∃ (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc),
    ghostVar γs (1 : Qp).half ((pm, rm, PM, RM) : trRec) ∗
    ([∗map] id ↦ pi ∈ PM, ∃ p : Loc,
      ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗ peerStop Rh id R p) ∗
    ([∗map] id ↦ g ∈ RM, remoteStop Rh id R g))

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
    (γs : GName) : Fractional (trLockP Rh t lid γd R γs) where
  fractional q1 q2 := by
    have hpt : ∀ v : Loc, ∀ f : GoString,
        (t.[rafthttp.Transport, f] ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢
        t.[rafthttp.Transport, f] ↦{DFrac.own q1} v ∗ t.[rafthttp.Transport, f] ↦{DFrac.own q2} v :=
      fun v f => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1)
        (DFrac.own q2)
    have hgv := fun (x : trRec) => (ghostVar_fractional (GF := GF) γs x).fractional q1.half q2.half
    unfold trLockP
    rw [Qp_half_add]
    refine ⟨?_, ?_⟩
    · iintro ⟨%pm, %rm, %PM, %RM, Hp, Hr, Hpm, Hrm, Hg, #Hpo, #Hro⟩
      icases (hpt pm _).1 $$ Hp with ⟨Hp1, Hp2⟩
      icases (hpt rm _).1 $$ Hr with ⟨Hr1, Hr2⟩
      icases (mapOrNil_fractional pm PM q1 q2).1 $$ Hpm with ⟨Hpm1, Hpm2⟩
      icases (mapOrNil_fractional rm RM q1 q2).1 $$ Hrm with ⟨Hrm1, Hrm2⟩
      icases (hgv (pm, rm, PM, RM)).1 $$ Hg with ⟨Hg1, Hg2⟩
      isplitl [Hp1 Hr1 Hpm1 Hrm1 Hg1]
      · iexists pm, rm, PM, RM; iframe; iframe #
      · iexists pm, rm, PM, RM; iframe; iframe #
    · iintro ⟨⟨%pm, %rm, %PM, %RM, Hp1, Hr1, Hpm1, Hrm1, Hg1, #Hpo, #Hro⟩,
        ⟨%pm', %rm', %PM', %RM', Hp2, Hr2, Hpm2, Hrm2, Hg2, -, -⟩⟩
      ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg1 Hg2
      cases Hag
      iexists pm, rm, PM, RM
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
      iframe #

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

end lemmas

end EtcdGrove
end Perennial
