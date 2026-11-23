/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto/Inv.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Gryff's invariant (`gryffInv γ`, namespace `gryffN`): the register protocol's shared ghost state,
allocated by the start, opened by every replica's run loop and by the client node's adapter.
Design: `notes/stage1-interface.md`; decisions D2 (prophecies) and D3.

**What it holds** (`gryffInvBody`):
* the abstract register `σ` (`ghostVar reg (1/2) σ`; the other half is the client's
  `own_state`, which the driver keeps and lends through each operation's atomic update);
* each replica's register `(v, t)` (`stores`, a ghost map `r ↦ (v, t)` for `r ∈ {0, 1, 2}`;
  replica `r`'s lock invariant owns the element);
* every tag ever stored and its value (`tagVal`, append-only; its elements are persistent
  witnesses carried by messages);
* the client operations in flight (`ops`: `id ↦ OpMeta`), each with its (prophesied) place in
  the tag order and its atomic update while it is pending (a saved proposition, `opRes`); `ops`
  is the join of the registrations (`γ.ops`, fixed) and the places (`γ.places`, fixed once);
* the client ids' turns and connection bindings, and each connection's placing counter;
* the linearized operations, in order (`lin`), whose replay from the initial state gives `σ`;
* the EPaxos instances' committed attributes (`insts`, persistent elements) and the agreed chain
  of executed RMWs (`execSeq`, `execOk`).

**Pure facts** (`invFacts` = `invFactsB` (`invFactsCore` ∧ `extraFacts` ∧ `bookFacts`) ∧
`chainReg` ∧ `placeShapes`): `tagVal 0 = 0`;
every store's value is its tag's; the abstract value is the value of the stores' frontier
(`median3`); an operation is linearized iff its place is at most the frontier; the replay of `lin`
gives `σ`; the RMW chain is the executor's; stored tags' producers and chain bases (H-U4-2); the
stores' keys, current lower bounds, and the turns' history (`bookFacts`); chain entries'
operations are registered (H-U4-9); placed writes' and RMWs' tag shapes (H-U4-10).

**Laws** (statements here and in `ClientLaws.lean`, `WireLaws.lean`; proved by the protocol
unit): `storeIs_lb`, `tagValIs_agree`, `nodeIdIs_agree`, `store_update` (the helping step),
`op_begin`, `op_end`, `op_place`, `opDone_intro_*`.
-/
module

public import Dsverify.Proof.gryff.Proto.InvDefs
public import Dsverify.Proof.gryff.Proto.InvPure
public import Dsverify.Proof.gryff.Proto.Fire
public import Dsverify.Proof.gryff.Proto.InvSteps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode proto dsverify_lab.harness

section defs
variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [InvGS_gen .hasLC GF]

/-! ## Laws (proved in the protocol unit, U4) -/

/-- A store's tag only grows: its element gives a lower bound. -/
theorem storeIs_lb (γ : ProtoNames) (k : Nat) (v : w64) (t : PTag) (E : CoPset)
    (hE : ↑gryffN ⊆ E) :
    gryffInvP γ ∗ storeIs γ k v t ⊢ |={E}=> storeIs γ k v t ∗ storeLb γ k t := by
  unfold gryffInvP storeIs storeLb
  iintro ⟨#Hinv, Hs⟩
  iinv Hinv with Hi Hclose
  unfold gryffInvBody
  icases Hi with ⟨%σ, %stores, %tv, %lbs, %ops, %info, %places, %lin, %insts, %execS, %preds,
    %turns, %conns, %placers, Hreg, Hst, Htv, Hlbs, Hops, Hpl, Hlin, Hinsts, Hexec, Hpreds,
    Hturns, Hconns, Hplacers, >%Hf, >%Hj, >%Hc, Hcopy, Hres⟩
  obtain ⟨Hf, Hrg⟩ := Hf
  imod Hst
  ihave %hk := ghost_map_lookup $$ Hst Hs
  have hlb : lbs.lookup (k, t) = some () := Hf.2.2.2.1 k (v, t) hk
  imod Hcopy
  ihave #Hlb := (BigSepM.bigSepM_lookup (Φ := fun kt (_ : Unit) =>
    ghostMapElem (GF := GF) γ.storeLbs kt DFrac.discard ()) (show get? lbs (k, t) = some () from hlb))
    $$ Hcopy
  imod Hclose $$ [Hreg Hst Htv Hlbs Hops Hpl Hlin Hinsts Hexec Hpreds Hturns Hconns Hplacers Hcopy Hres] with -
  · inext
    iexists σ, stores, tv, lbs, ops, info, places, lin, insts, execS, preds, turns, conns, placers
    iframe
    ipureintro; exact ⟨⟨Hf, Hrg⟩, Hj, Hc⟩
  imodintro
  iframe Hs
  iexact Hlb

/-- Witnesses of a tag's value agree. -/
theorem tagValIs_agree (γ : ProtoNames) (t : PTag) (v1 v2 : w64) :
    tagValIs (GF := GF) γ t v1 ∗ tagValIs γ t v2 ⊢ ⌜v1 = v2⌝ := by
  unfold tagValIs
  iintro ⟨H1, H2⟩
  iapply ghostMapElem_agree $$ H1 H2

/-- Node ids agree. -/
theorem nodeIdIs_agree (γ : ProtoNames) (k : Nat) (id1 id2 : w64) :
    nodeIdIs (GF := GF) γ k id1 ∗ nodeIdIs γ k id2 ⊢ ⌜id1 = id2⌝ := by
  unfold nodeIdIs
  iintro ⟨H1, H2⟩
  iapply ghostMapElem_agree $$ H1 H2

/-- The helping step: replica node `k`'s store moves to a greater tag `t'` with its value `v'`;
every operation whose place the frontier passes is linearized (in place order), its client's
atomic update fired. Two later credits pay for the invariant's and the updates' laters. -/
theorem store_update (γ : ProtoNames) (k : Nat) (v v' : w64) (t t' : PTag) (E : CoPset)
    (hE : ↑gryffN ∪ ↑clientN ⊆ E) (hlt : tagLt t t') :
    gryffInvP γ ∗ storeIs γ k v t ∗ tagValIs γ t' v' ∗ £ 2 ⊢
      |={E}=> storeIs γ k v' t' ∗ storeLb γ k t' := by
  have hE1 : (↑gryffN : CoPset) ⊆ E := fun x hx => hE x (Iris.Std.mem_union.2 (Or.inl hx))
  have hE2 : (↑clientN : CoPset) ⊆ E := fun x hx => hE x (Iris.Std.mem_union.2 (Or.inr hx))
  unfold gryffInvP storeIs tagValIs storeLb
  iintro ⟨#Hinv, Hs, #Hv, ⟨Hlc1, Hlc2⟩⟩
  iinv Hinv with Hi Hclose
  unfold gryffInvBody
  icases Hi with ⟨%σ, %stores, %tv, %lbs, %ops, %info, %places, %lin, %insts, %execS, %preds,
    %turns, %conns, %placers, Hreg, Hst, Htv, Hlbs, Hops, Hpl, Hlin, Hinsts, Hexec, Hpreds,
    Hturns, Hconns, Hplacers, >%Hf, >%Hj, >%Hc, Hcopy, Hres⟩
  obtain ⟨Hf, Hrg⟩ := Hf
  imod Hst; imod Htv; imod Hlbs; imod Hlin; imod Hreg; imod Hcopy
  ihave %hk := ghost_map_lookup $$ Hst Hs
  ihave %htv := ghost_map_lookup $$ Htv Hv
  obtain ⟨new, σ', h1, h2, h3, hall⟩ := store_update_all ⟨Hf, Hj, Hc⟩ hk htv hlt
  obtain ⟨Hf2, Hj2, Hc2⟩ := hall
  ihave Hres := BI.later_mono (opRes_map_to_NL γ ops lin) $$ Hres
  imod lc_fupd_elim_later $$ Hlc1 Hres with Hres
  imod lc_fupd_elim_later $$ Hlc2 Hres with Hres
  ihave Hres : [∗map] k ↦ x ∈ ops, psiRes (GF := GF) γ lin (lin ++ new) [] k x $$ [Hres]
  · iapply (BigSepM.bigSepM_mono (fun {k x} _ => by
      unfold psiRes; rw [if_neg List.not_mem_nil])) $$ Hres
  imod fire_all γ ops lin (lin ++ new) (E \ ↑gryffN) (clientN_sub_diff E hE2) new [] σ σ' h3
    (fun x hx => ⟨(h1 x hx).1, List.mem_append_right _ hx, (h1 x hx).2, List.not_mem_nil⟩) h2
    $$ [Hreg Hres] with ⟨Hreg, Hres⟩
  · iframe
  ihave Hres : [∗map] k ↦ x ∈ ops, opRes (GF := GF) γ (lin ++ new) k x $$ [Hres]
  · iapply (BigSepM.bigSepM_mono (fun {k x} _ => by
      unfold psiRes
      by_cases hkn : k ∈ [] ++ new.map Prod.fst
      · rw [if_pos hkn]
      · rw [if_neg hkn]
        refine (NL_to_opRes γ lin k x).trans (opRes_lin_grow γ lin _ k x
          (fun y hy => List.mem_append_left _ hy) (fun o ho => ?_))
        rcases List.mem_append.1 ho with ho | ho
        · exact ho
        · exact absurd (by simpa using List.mem_map_of_mem (f := Prod.fst) ho) hkn)) $$ Hres
  imod ghost_map_update (v', t') $$ Hst Hs with ⟨Hst, Hs⟩
  imod lbs_add γ lbs (k, t') (E \ ↑gryffN) $$ [Hlbs Hcopy] with ⟨Hlbs, Hcopy, #Hlb⟩
  · iframe
  imod monoListAuthOwn_update_app new $$ Hlin with ⟨Hlin, -⟩
  imod Hclose $$ [Hreg Hst Htv Hlbs Hops Hpl Hlin Hinsts Hexec Hpreds Hturns Hconns Hplacers
    Hcopy Hres] with -
  · inext
    iexists σ', stores.insert k (v', t'), tv, lbs.insert (k, t') (), ops, info, places,
      lin ++ new, insts, execS, preds, turns, conns, placers
    iframe
    ipureintro; exact ⟨⟨Hf2, Hrg⟩, Hj2, Hc2⟩
  imodintro
  iframe Hs
  iexact Hlb

end defs

end Perennial.gryff
