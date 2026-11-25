/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Start.lean (run gryff-bump-1, lab master
915f964; notes/dsv-gryff.md), redesigned for `Net/`'s listeners and `examples/lib/remote`.

**The start** (`gryff_start`): from the registry (`regCtx`) and the kit's seven wildcard
listeners unset (`gryffLas`: the master's net/rpc listener `":7501"`, the replicas' peer-and-client
ports `":7502".."7504"`, their net/rpc listeners `":8502".."8504"`), the run's names `γ`, the
register's half at `0` (the far side's store's state: remote's pending library holds it), each
client machine's share and each server machine's share.

Proof (U6): allocate stage 2's names (`proto2_alloc`) and the protocol's (`proto_alloc`: Gryff's
ghost maps and lists at the initial state, `StartInit.lean`), the registry (`deploy_alloc`), the
rpc world built directly (its services `rpcServicesDef`, a fresh connection registry, HTTP's
handshake at every address: `worldOk` by `rfl`), the placers', Gryff's and the rpc registry's
invariants; set the replica ports' listener protocols (`lis_set_proto`, Gryff's wire protocols)
and the rpc listeners' (`RpcHttpAddr.rpcLisP_set`); split the shares machine by machine.

Port: the lab's address tokens, `addrs_set_proto` over every address and `rpcWorld_alloc` are
gone; `ProtoNames.placed` (the placers' invariant's placed map) is new; Gryff client ids' unused
connection elements are `none : Option Nat` (`idTok`).
-/
module

public import Dsverify.Proof.gryff.Shares
public import Dsverify.Proof.gryff.StartInit
public import Dsverify.Proof.gryff.Proto2P.Init
public import Dsverify.Proof.gryff.Proto2P.Ghost
public import Dsverify.Proof.gryff.examples.gryffnet.KitSpecs
public import GooseLang.Ext.Net.Decide

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto dsverify_lab.harness

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## The listeners -/

/-- The kit's wildcard listeners: the master's net/rpc listener, the replicas' ports, the
replicas' net/rpc listeners. -/
def gryffLas : List GoString :=
  [masterRpcLis, lisAddrOf (portAddr 0), lisAddrOf (portAddr 1), lisAddrOf (portAddr 2),
   replicaRpcLis 0, replicaRpcLis 1, replicaRpcLis 2]

/-- Two wildcard listeners with different ports take no address in common. -/
theorem lisAccepts_disj (l1 l2 : GoString)
    (h1 : (wildPort l1).isSome = true ∧ wildPort l1 = portOf l1)
    (h2 : (wildPort l2).isSome = true ∧ wildPort l2 = portOf l2)
    (hne : portOf l1 ≠ portOf l2) :
    ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a := by
  intro a ha hb
  have port : ∀ l, (wildPort l).isSome = true ∧ wildPort l = portOf l → lisAccepts l a →
      portOf a = portOf l := by
    intro l ⟨hs, he⟩ h
    rcases h with rfl | ⟨p, hw, hp⟩
    · rfl
    · rw [hp, ← he, hw]
  exact hne ((port l1 h1 ha).symm.trans (port l2 h2 hb))

theorem gryffLas_wild : ∀ l ∈ gryffLas, (wildPort l).isSome = true ∧ wildPort l = portOf l := by
  decide

theorem gryffLas_ports : (gryffLas.map portOf).Nodup := by
  decide

theorem gryffLas_pairwise :
    gryffLas.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a) := by
  have h : gryffLas.Pairwise (fun l1 l2 => portOf l1 ≠ portOf l2) :=
    List.pairwise_map.mp gryffLas_ports
  refine h.imp_of_mem ?_
  intro l1 l2 hl1 hl2 hne
  exact lisAccepts_disj l1 l2 (gryffLas_wild l1 hl1) (gryffLas_wild l2 hl2) hne

theorem gryffLas_disjB :
    ∀ a ∈ examples.gryffnet.clientAddrs, ∀ la ∈ gryffLas, lisAcceptsB la a = false := by
  decide

theorem gryffLas_disj :
    ∀ a ∈ examples.gryffnet.clientAddrs, ∀ la ∈ gryffLas, ¬ lisAccepts la a := by
  intro a ha la hla h
  have := gryffLas_disjB a ha la hla
  rw [lisAcceptsB_iff.2 h] at this
  cases this

theorem listenOk_gryffLas : ∀ la ∈ gryffLas, listenOk la = true := by
  decide

/-! ## Generic plumbing -/

theorem bigSepL6_intro' {PROP : Type _} [BI PROP] (Φ : Nat → PROP) :
    Φ 0 ∗ Φ 1 ∗ Φ 2 ∗ Φ 3 ∗ Φ 4 ∗ Φ 5 ⊢ [∗list] x ∈ [0, 1, 2, 3, 4, 5], Φ x := by
  iintro ⟨H0, H1, H2, H3, H4, H5⟩
  iframe H0 H1 H2 H3 H4 H5
  iempintro

theorem bigSepL4_intro' {PROP : Type _} [BI PROP] (Φ : Nat → PROP) :
    Φ 0 ∗ Φ 1 ∗ Φ 2 ∗ Φ 3 ⊢ [∗list] x ∈ [0, 1, 2, 3], Φ x := by
  iintro ⟨H0, H1, H2, H3⟩
  iframe H0 H1 H2 H3
  iempintro

section ghost
variable {GF : BundledGFunctors} [AllG GF]
variable {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]

/-- Insert fresh keys `ps.map kf` (values `f p`) into a ghost map, getting their elements. -/
theorem ghost_map_insert_list {α : Type} (γn : GName) (kf : α → K) (f : α → V) :
    ∀ (ps : List α) (m : GMap K V), (ps.map kf).Nodup → (∀ p ∈ ps, m.lookup (kf p) = none) →
    (ghostMapAuth γn 1 m : IProp GF) ⊢ |==> ∃ m' : GMap K V, ghostMapAuth γn 1 m' ∗
      [∗list] p ∈ ps, ghostMapElem γn (kf p) (DFrac.own 1) (f p)
  | [], m, _, _ => by
    iintro H
    imodintro
    iexists m
    iframe H
    iapply BigSepL.bigSepL_nil.2; iempintro
  | p :: ps, m, hnd, hfr => by
    iintro H
    imod ghost_map_insert (kf p) (f p) (hfr p (by simp)) $$ H with ⟨H, Hp⟩
    rw [List.map_cons, List.nodup_cons] at hnd
    have hfr' : ∀ q ∈ ps, (m.insert (kf p) (f p)).lookup (kf q) = none := by
      intro q hq
      have hne : kf p ≠ kf q := fun e => hnd.1 (e ▸ List.mem_map_of_mem hq)
      simp only [GMap.insert, hne, ite_false]
      exact hfr q (by simp [hq])
    imod ghost_map_insert_list γn kf f ps _ hnd.2 hfr' $$ H with ⟨%m', H, Hs⟩
    imodintro
    iexists m'
    iframe H
    iapply BigSepL.bigSepL_cons.2
    iframe Hp Hs

/-- Insert the keys `L` (values `f k`) into an empty ghost map, getting their elements; the map is
`L.foldr` of the inserts (stage 2's initial maps, `StartInit.lean`). -/
theorem ghost_map_insert_foldr (γn : GName) (f : K → V) :
    ∀ (L : List K), L.Nodup →
    (ghostMapAuth γn 1 (∅ : GMap K V) : IProp GF) ⊢ |==>
      (ghostMapAuth γn 1 (L.foldr (fun x m => GMap.insert x (f x) m) ∅) ∗
        [∗list] k ∈ L, ghostMapElem γn k (DFrac.own 1) (f k))
  | [], _ => by
    rw [List.foldr_nil]
    iintro H
    imodintro
    iframe H
    iapply BigSepL.bigSepL_nil.2; iempintro
  | x :: L, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.foldr_cons]
    iintro H
    imod ghost_map_insert_foldr γn f L hnd.2 $$ H with ⟨H, Hs⟩
    have hfr : (L.foldr (fun x m => GMap.insert x (f x) m) ∅).lookup x = none := by
      rw [p2.foldr_insert_lookup f L x, if_neg hnd.1]
    imod ghost_map_insert x (f x) hfr $$ H with ⟨H, Hx⟩
    imodintro
    iframe H
    iapply BigSepL.bigSepL_cons.2
    iframe Hx Hs

end ghost

/-! ## The protocol's names -/

/-- The client ids' (client machine, generation) pairs. -/
def idPairs : List (Nat × Nat) :=
  (List.range 6).flatMap (fun c => (List.range' 0 (5 - 0)).map (fun g => (c, g)))

theorem idPairs_gid_nodup : (idPairs.map (fun p => gid p.1 p.2)).Nodup := by
  decide

theorem idPairs_turn_nodup : (idPairs.map (fun p => ((p.1 : Int) + 6 * (p.2 : Int)))).Nodup := by
  decide

theorem idPairs_split {PROP : Type _} [BI PROP] (X : Nat → Nat → PROP) :
    ([∗list] p ∈ idPairs, X p.1 p.2) ⊢
      [∗list] c ∈ List.range 6, [∗list] g ∈ List.range' 0 (5 - 0), X c g := by
  unfold idPairs
  rw [BigSepL.bigSepL_flatMap]
  refine BigSepL.bigSepL_mono (fun _ => ?_)
  rw [BigSepL.bigSepL_map]

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- Stage 2's ghost state at the start (D9, D13, D14): the authorities of `gryffInv2Body` at the
initial state that stage 2 adds. -/
def inv2Init (γp : ProtoNames) : IProp GF :=
  iprop(monoListAuthOwn (γp.s2.trace 0) (1 : Qp).half ([] : List model.Ev) ∗
    monoListAuthOwn (γp.s2.trace 1) (1 : Qp).half ([] : List model.Ev) ∗
    monoListAuthOwn (γp.s2.trace 2) (1 : Qp).half ([] : List model.Ev) ∗
    monoListAuthOwn γp.s2.hist 1 ([] : List pure.Label) ∗
    ghostMapAuth γp.s2.pred 1 preds0 ∗ ghostMapAuth γp.s2.nodePred 1 preds0 ∗
    ghostMapAuth γp.s2.budget 1 budget0 ∗ ghostMapAuth γp.s2.rxCur 1 cur0 ∗
    ghostMapAuth γp.s2.rx 1 (∅ : GMap (Nat × Nat × Nat) model.Msg) ∗
    ghostMapAuth γp.s2.reqs 1 (∅ : GMap OpId (Nat × RegInput w64)) ∗
    ghostMapAuth γp.s2.connRep 1 (∅ : GMap Nat Nat) ∗ ghostMapAuth γp.s2.claim 1 claims0)

/-- Stage 2's start resources: the replica ids' slots (to the registry's invariant,
`deploy_alloc`), the replica nodes' prediction and claim tokens (`replicaBootRes`), the 24 budget
units (4 per client machine), and the invariant's authorities (`inv2Init`). -/
def start2Res (γp : ProtoNames) : IProp GF :=
  iprop(([∗list] i ∈ [0, 1, 2], predSlot γp i ∗ idSlotResN γp i) ∗
    ([∗list] k ∈ [0, 1, 2], predTok γp k ∗ slotClaimTok γp k) ∗
    budget γp 24 ∗ inv2Init γp)

/-- Allocate stage 2's names (fresh ghost maps and lists at `inv2Init`'s values, with the
elements `start2Res` hands out). -/
theorem proto2_alloc :
    ⊢@{IProp GF} |==> ∃ s2 : Proto2Names, ∀ γp : ProtoNames, ⌜γp.s2 = s2⌝ -∗
      start2Res γp := by
  imod mono_list_own_alloc (GF := GF) ([] : List model.Ev) with ⟨%g0, H0, -⟩
  imod mono_list_own_alloc (GF := GF) ([] : List model.Ev) with ⟨%g1, H1, -⟩
  imod mono_list_own_alloc (GF := GF) ([] : List model.Ev) with ⟨%g2, H2, -⟩
  imod mono_list_own_alloc (GF := GF) ([] : List pure.Label) with ⟨%gh, Hh, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Option (List w64)) with ⟨%gp, Hp⟩
  imod ghost_map_insert_foldr gp (fun _ => (none : Option (List w64))) [0, 1, 2] (by decide)
    $$ Hp with ⟨Hp, Hps⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Option (List w64)) with ⟨%gn, Hn⟩
  imod ghost_map_insert_foldr gn (fun _ => (none : Option (List w64))) [0, 1, 2] (by decide)
    $$ Hn with ⟨Hn, Hns⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%gc, Hc⟩
  imod ghost_map_insert_foldr gc (fun _ => ()) [0, 1, 2] (by decide) $$ Hc with ⟨Hc, Hcs⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%gb, Hb⟩
  imod ghost_map_insert_foldr gb (fun _ => ()) (List.range 24) List.nodup_range $$ Hb
    with ⟨Hb, Hbs⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat × Nat) (V := Nat) with ⟨%gcur, Hcur⟩
  imod ghost_map_insert_foldr gcur (fun _ => (0 : Nat))
    ((List.range 3).flatMap fun k => (List.range 3).map fun q => (k, q)) (by decide) $$ Hcur
    with ⟨Hcur, Hcurs⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat × Nat × Nat) (V := model.Msg)
    with ⟨%grx, Hrx⟩
  imod ghost_map_alloc_empty (GF := GF) (K := OpId) (V := Nat × RegInput w64)
    with ⟨%grq, Hrq⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Nat) with ⟨%gcr, Hcr⟩
  icases (monoList_halves (GF := GF) g0 ([] : List model.Ev)).1 $$ H0 with ⟨H0, H0'⟩
  icases (monoList_halves (GF := GF) g1 ([] : List model.Ev)).1 $$ H1 with ⟨H1, H1'⟩
  icases (monoList_halves (GF := GF) g2 ([] : List model.Ev)).1 $$ H2 with ⟨H2, H2'⟩
  imodintro
  let tr : Fin 3 → GName := fun k => if k.val = 0 then g0 else if k.val = 1 then g1 else g2
  iexists ⟨gp, gn, gc, gb, tr, gh, gcur, grx, grq, gcr⟩
  iintro %γp %hγ
  have e0 : γp.s2.trace 0 = g0 := by rw [hγ]; rfl
  have e1 : γp.s2.trace 1 = g1 := by rw [hγ]; rfl
  have e2 : γp.s2.trace 2 = g2 := by rw [hγ]; rfl
  have ep : γp.s2.pred = gp := by rw [hγ]
  have en : γp.s2.nodePred = gn := by rw [hγ]
  have ec : γp.s2.claim = gc := by rw [hγ]
  have eb : γp.s2.budget = gb := by rw [hγ]
  have eh : γp.s2.hist = gh := by rw [hγ]
  have ecur : γp.s2.rxCur = gcur := by rw [hγ]
  have erx : γp.s2.rx = grx := by rw [hγ]
  have erq : γp.s2.reqs = grq := by rw [hγ]
  have ecr : γp.s2.connRep = gcr := by rw [hγ]
  unfold start2Res inv2Init
  unfold predSlot predTok slotClaimTok budget
  rw [ep, en, ec, eb, eh, erx, erq, ecr]
  rw [show preds0 = List.foldr (fun x m => GMap.insert x (none : Option (List w64)) m) ∅ [0, 1, 2]
    from rfl, show claims0 = List.foldr (fun x m => GMap.insert x () m) ∅ [0, 1, 2] from rfl,
    show budget0 = List.foldr (fun x m => GMap.insert x () m) ∅ (List.range 24) from rfl,
    show cur0 = List.foldr (fun x m => GMap.insert x (0 : Nat) m) ∅
      ((List.range 3).flatMap fun k => (List.range 3).map fun q => (k, q)) from rfl]
  rw [show ((List.range 3).flatMap fun k => (List.range 3).map fun q => (k, q)) =
    [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)] from rfl]
  icases Hps with ⟨P0, P1, P2, -⟩
  icases Hns with ⟨N0, N1, N2, -⟩
  icases Hcs with ⟨C0, C1, C2, -⟩
  icases Hcurs with ⟨R00, R01, R02, R10, R11, R12, R20, R21, R22, -⟩
  have e0' : γp.s2.trace ⟨0, by decide⟩ = g0 := e0
  have e1' : γp.s2.trace ⟨1, by decide⟩ = g1 := e1
  have e2' : γp.s2.trace ⟨2, by decide⟩ = g2 := e2
  isplitl [P0 P1 P2 H0' H1' H2' R00 R01 R02 R10 R11 R12 R20 R21 R22]
  · iapply BigSepL.bigSepL_cons.2
    isplitl [P0 H0' R00 R10 R20]
    · iframe P0
      iapply (idSlotResN_lt γp 0 (by decide)).2
      unfold idSlotRes traceHalf rxCurTok
      rw [e0', ecur]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
      iframe H0' R00 R10 R20
    iapply BigSepL.bigSepL_cons.2
    isplitl [P1 H1' R01 R11 R21]
    · iframe P1
      iapply (idSlotResN_lt γp 1 (by decide)).2
      unfold idSlotRes traceHalf rxCurTok
      rw [e1', ecur]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
      iframe H1' R01 R11 R21
    iapply BigSepL.bigSepL_cons.2
    isplitl [P2 H2' R02 R12 R22]
    · iframe P2
      iapply (idSlotResN_lt γp 2 (by decide)).2
      unfold idSlotRes traceHalf rxCurTok
      rw [e2', ecur]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
      iframe H2' R02 R12 R22
    iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [N0 N1 N2 C0 C1 C2]
  · iframe N0 N1 N2 C0 C1 C2
    iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hbs]
  · iexists List.range 24
    iframe Hbs
    ipureintro; simp
  rw [e0, e1, e2, ecur]
  iframe

/-- Stage 1's names that `gryffInv2` shares, at the start: the register's invariant half at `0`,
the empty linearization and registrations, the client ids' turns and connections, the invariant's
half of the placers. -/
def inv1Init (γp : ProtoNames) : IProp GF :=
  iprop(ghostVar γp.reg (1 : Qp).half (W64 0) ∗
    monoListAuthOwn γp.lin 1 ([] : List (OpId × RegOutput w64)) ∗
    ghostMapAuth γp.ops 1 (∅ : GMap OpId OpInfo) ∗
    (∃ (mt : GMap Int (Int × Bool)) (mc : GMap w32 (Option Nat)),
      ghostMapAuth γp.turns 1 mt ∗ ghostMapAuth γp.conns 1 mc) ∗
    ghostMapAuth γp.placers (1 : Qp).half (∅ : GMap Nat Int))

/-- The ids' list of `gryffInv2Body` with no registered replica id. -/
theorem ids_none (γp : ProtoNames) (M : GMap Nat Nat) (hM : ∀ i, M.lookup i = none) :
    ⊢@{IProp GF} [∗list] i ∈ List.range 3,
      gryffInv2Body.match_1 (fun _ => IProp GF) (M.lookup i)
        (fun n => nodeIdIs γp n (W64 i)) (fun _ => iprop(True)) := by
  refine BigSepL.bigSepL_intro (P := iprop(emp)) (fun k x _ => ?_)
  rw [hM x]
  exact BI.true_intro

/-- Allocate the protocol's names at the initial state (stage 2's names `s2` given): Gryff's
invariant's stage-1 part, the client's half of the register, the empty node-id authority (for
`deploy_alloc`), the placers' other half and the placed map, and the client ids' and turns'
elements. -/
theorem proto_alloc (s2 : Proto2Names) :
    ⊢@{IProp GF} |==> ∃ γp : ProtoNames, ⌜γp.s2 = s2⌝ ∗ inv1Init γp ∗
      regHalf γp (W64 0) ∗
      ghostMapAuth (K := Nat) (V := w64) γp.nodeIds 1 ∅ ∗
      ghostMapAuth (K := Nat) (V := Int) γp.placers (1 : Qp).half ∅ ∗
      ghostMapAuth (K := Nat) (V := Unit) γp.placed 1 ∅ ∗
      [∗list] p ∈ idPairs, ghostMapElem γp.conns (gid p.1 p.2) (DFrac.own 1) (none : Option Nat) ∗
        ghostMapElem γp.turns ((p.1 : Int) + 6 * (p.2 : Int)) (DFrac.own 1) ((0 : Int), false) := by
  imod ghostVar_alloc (GF := GF) (W64 0) with ⟨%γreg, Hreg⟩
  icases (ghostVar_split_half γreg 1 (W64 0)).1 $$ Hreg with ⟨Hreg1, Hreg2⟩
  imod mono_list_own_alloc (GF := GF) ([] : List (OpId × RegOutput w64)) with ⟨%γlin, Hlin, -⟩
  imod mono_list_own_alloc (GF := GF) ([] : List ExecEntry) with ⟨%γex, -, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := PTag) (V := w64) with ⟨%γtv, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := w64 × PTag) with ⟨%γst, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat × PTag) (V := Unit) with ⟨%γlb, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := OpId) (V := OpInfo) with ⟨%γops, Hops⟩
  imod ghost_map_alloc_empty (GF := GF) (K := OpId) (V := Placement) with ⟨%γpl, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Int × Int) (V := InstAttrs) with ⟨%γin, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := List ExecEntry) with ⟨%γpr, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := w64) with ⟨%γni, Hni⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Int) with ⟨%γpc, Hpc⟩
  icases (ghostMapAuth_halves γpc (∅ : GMap Nat Int)).1 $$ Hpc with ⟨Hpc1, Hpc2⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%γpd, Hpd⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w32) (V := Option Nat) with ⟨%γcn, Hcn⟩
  imod ghost_map_insert_list γcn (fun p : Nat × Nat => gid p.1 p.2)
    (fun _ => (none : Option Nat)) idPairs ∅ idPairs_gid_nodup (fun _ _ => rfl) $$ Hcn
    with ⟨%mc, Hcn, Hcs⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Int) (V := Int × Bool) with ⟨%γtu, Htu⟩
  imod ghost_map_insert_list γtu (fun p : Nat × Nat => ((p.1 : Int) + 6 * (p.2 : Int)))
    (fun _ => ((0 : Int), false)) idPairs ∅ idPairs_turn_nodup (fun _ _ => rfl) $$ Htu
    with ⟨%mt, Htu, Hts⟩
  imodintro
  iexists ⟨γreg, γlin, γtv, γst, γlb, γops, γin, γex, γpr, γtu, γni, γpl, γcn, γpc, γpd, s2⟩
  isplitr
  · ipureintro; rfl
  isplitr [Hreg2 Hni Hpc2 Hpd Hcs Hts]
  · unfold inv1Init
    iframe Hreg1 Hlin Hops Hpc1
    iexists mt, mc
    iframe Htu Hcn
  unfold regHalf
  iframe Hreg2 Hni Hpc2 Hpd
  iapply BigSepL.bigSepL_sep_eqv.2
  iframe Hcs Hts

end alloc

/-! ## The start -/

section start
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]
variable [RA : RpcHttpAddr GF]

/-- The rpc world of the deployment's names: the deployment's services, the connection registry
`γw`, net/rpc's HTTP handshake at every address. -/
def gryffWorld (δ : DeployNames) (γp : ProtoNames) (γw : GName) : net.rpc.RpcWorld GF where
  SS := rpcServicesDef δ (regCarry γp)
  reg := γw
  hs := fun _ => net.rpc.connectReq net.rpc.defaultRPCPath
  hsAns := fun _ => net.rpc.connectAns

theorem gryffWorld_ok (δ : DeployNames) (γp : ProtoNames) (γw : GName) :
    worldOk (GF := GF) ⟨δ, γp, gryffWorld δ γp γw⟩ :=
  ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

/-- **The start**: see the file header. -/
theorem gryff_start :
    ⊢ regCtx (Gg := G) -∗ ([∗list] la ∈ gryffLas, lisUnset la) ={⊤}=∗
      ∃ γ : GryffNames GF, regHalf γ.proto (W64 0) ∗
        ([∗list] c ∈ [0, 1, 2, 3, 4, 5], clientNodeShare γ c) ∗
        ([∗list] i ∈ [0, 1, 2, 3], serverShare γ i) := by
  iintro #Hreg Hl
  imod proto2_alloc (GF := GF) with ⟨%s2, H2⟩
  imod (proto_alloc (GF := GF) s2) with ⟨%γp, %Hs2, Hi1, HregH, Hni, Hpc, Hpd, Hids⟩
  ihave H2 := H2 $$ %γp %Hs2
  iunfold start2Res at H2
  icases H2 with ⟨Hslots, Hnodes, Hbud, Hi2⟩
  imod deploy_alloc γp ⊤ $$ [Hni Hslots] with ⟨%δ, Hda, #Hdinv⟩
  · iframe Hni Hslots
  -- the rpc world's connection registry
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := net.rpc.RpcConnNames) with ⟨%γw, Hw⟩
  let W : net.rpc.RpcWorld GF := gryffWorld δ γp γw
  let γ : GryffNames GF := ⟨δ, γp, W⟩
  imod inv_alloc net.rpc.regN' ⊤ (net.rpc.regInv (Gg := G) W) $$ [Hw] with #HregW
  · inext
    unfold net.rpc.regInv
    iexists ∅
    have hreg : W.reg = γw := rfl
    rw [hreg]
    iframe Hw
    iapply BigSepM.bigSepM_empty.2; iempintro
  -- the placers' invariant
  imod inv_alloc placersN ⊤ (placersInv γ) $$ [Hpc Hpd] with #Hpinv
  · inext
    unfold placersInv
    iexists ∅, ∅
    iframe Hpc Hpd
    isplitr
    · ipureintro; intro c; rfl
    iapply BigSepM.bigSepM_empty.2; iempintro
  -- Gryff's invariant
  unfold inv1Init inv2Init
  icases Hi1 with ⟨HregI, Hlin, Hops, ⟨%mt, %mc, Htu, Hcn⟩, HpcI⟩
  icases Hi2 with ⟨T0, T1, T2, Hh, HP, HNP, HB, Hcur, Hrx, Hrq, HcR, -⟩
  ihave #Hids0 := ids_none (GF := GF) γp (p2.inv0 mt mc).idNode (fun _ => rfl)
  imod inv_alloc gryffN ⊤ (gryffInv2Body γp) $$ [HregI Hlin Hops Htu Hcn HpcI T0 T1 T2 Hh HP HNP
    HB Hcur Hrx Hrq HcR] with #Hginv
  · inext
    unfold gryffInv2Body
    iexists p2.inv0 mt mc
    simp only [p2.inv0]
    iframe HregI Hlin Hops Htu Hcn HpcI T0 T1 T2 Hh HP HNP HB Hcur Hrx Hrq HcR Hids0
    isplitr
    · ipureintro; exact p2.facts_init mt mc
    iapply BigSepM.bigSepM_empty.2; iempintro
  ihave #Hsh : sharedInvs γ $$ []
  · unfold sharedInvs protoInvs gryffInv2
    iframe Hginv Hpinv HregW
  ihave #Hpi : □ protoInvs γ $$ []
  · iintro !>; unfold protoInvs gryffInv2; iframe Hginv Hpinv
  -- the listeners
  unfold gryffLas
  icases Hl with ⟨Lm, L0, L1, L2, R0, R1, R2, -⟩
  have hok : ∀ la ∈ gryffLas, listenOk la = true := listenOk_gryffLas
  imod lis_set_proto ⊤ (lisAddrOf (portAddr 0)) (gryffWireP γ (portAddr 0))
    (gryffWireQ γ (portAddr 0)) (hok _ (by simp [gryffLas])) $$ Hreg L0 with #HL0
  imod lis_set_proto ⊤ (lisAddrOf (portAddr 1)) (gryffWireP γ (portAddr 1))
    (gryffWireQ γ (portAddr 1)) (hok _ (by simp [gryffLas])) $$ Hreg L1 with #HL1
  imod lis_set_proto ⊤ (lisAddrOf (portAddr 2)) (gryffWireP γ (portAddr 2))
    (gryffWireQ γ (portAddr 2)) (hok _ (by simp [gryffLas])) $$ Hreg L2 with #HL2
  have hhs : ∀ la : GoString, ∀ a, addrOk a = true ∧ lisAccepts la a →
      W.hs a = net.rpc.connectReq net.rpc.defaultRPCPath ∧ W.hsAns a = net.rpc.connectAns :=
    fun _ _ _ => ⟨rfl, rfl⟩
  imod RA.rpcLisP_set ⊤ W masterRpcLis _ _ (hok _ (by simp [gryffLas])) (hhs _)
    $$ Hreg HregW Lm with #HRm
  imod RA.rpcLisP_set ⊤ W (replicaRpcLis 0) _ _ (hok _ (by simp [gryffLas])) (hhs _)
    $$ Hreg HregW R0 with #HR0
  imod RA.rpcLisP_set ⊤ W (replicaRpcLis 1) _ _ (hok _ (by simp [gryffLas])) (hhs _)
    $$ Hreg HregW R1 with #HR1
  imod RA.rpcLisP_set ⊤ W (replicaRpcLis 2) _ _ (hok _ (by simp [gryffLas])) (hhs _)
    $$ Hreg HregW R2 with #HR2
  ihave #Hns : netShare γ $$ []
  · unfold netShare rpcLises replicaLis
    iframe HL0 HL1 HL2 HRm HR0 HR1 HR2
    isplit <;> (iapply BigSepL.bigSepL_nil.2; iempintro)
  -- the client machines' resources
  ihave Hids := idPairs_split (fun c g => iprop(ghostMapElem γp.conns (gid c g) (DFrac.own 1)
      (none : Option Nat) ∗
    ghostMapElem γp.turns ((c : Int) + 6 * (g : Int)) (DFrac.own 1) ((0 : Int), false)))
    $$ Hids
  rw [show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
  icases Hids with ⟨I0, I1, I2, I3, I4, I5, -⟩
  icases budget_split γp 4 20 $$ Hbud with ⟨B0, Hbud⟩
  icases budget_split γp 4 16 $$ Hbud with ⟨B1, Hbud⟩
  icases budget_split γp 4 12 $$ Hbud with ⟨B2, Hbud⟩
  icases budget_split γp 4 8 $$ Hbud with ⟨B3, Hbud⟩
  icases budget_split γp 4 4 $$ Hbud with ⟨B4, B5⟩
  icases Hnodes with ⟨⟨P0, C0⟩, ⟨P1, C1⟩, ⟨P2, C2⟩, -⟩
  have hW := gryffWorld_ok (GF := GF) δ γp γw
  imodintro
  iexists γ
  iframe HregH
  isplitl [I0 I1 I2 I3 I4 I5 B0 B1 B2 B3 B4 B5]
  · iapply bigSepL6_intro'
    unfold clientNodeShare clientStartRes unusedIds idTok turnTok
    simp only [Nat.sub_zero]
    iframe I0 I1 I2 I3 I4 I5 B0 B1 B2 B3 B4 B5 Hns Hsh
  iapply bigSepL4_intro'
  unfold serverShare
  isplitl [Hda]
  · iframe Hns Hsh
    simp only [↓reduceIte]
    unfold masterStartRes deployStartDef
    iframe Hda Hdinv
    ipureintro; exact hW
  isplitl [P0 C0]
  · iframe Hns Hsh
    simp only [show ((1 : Nat) = 0) = False by decide, ↓reduceIte]
    unfold replicaStartRes deployRegResDef replicaBootRes
    iframe P0 C0 Hdinv
    ipureintro; exact hW
  isplitl [P1 C1]
  · iframe Hns Hsh
    simp only [show ((2 : Nat) = 0) = False by decide, ↓reduceIte]
    unfold replicaStartRes deployRegResDef replicaBootRes
    iframe P1 C1 Hdinv
    ipureintro; exact hW
  · iframe Hns Hsh
    simp only [show ((3 : Nat) = 0) = False by decide, ↓reduceIte]
    unfold replicaStartRes deployRegResDef replicaBootRes
    iframe P2 C2 Hdinv
    ipureintro; exact hW

end start

end Perennial.gryff
