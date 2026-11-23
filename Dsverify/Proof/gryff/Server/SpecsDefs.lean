/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Server/SpecsDefs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The sealed predicates of the server side's cross-package specs (stage 1 interface; the specs are
in `Server/Specs.lean`, which imports this module and `Server/SpecsReq.lean`).

* `registeredAs γ k id nodes` (persistent): replica node `k` (0, 1, 2 for nodes 2, 3, 4)
  registered with the master, which made it replica `id` of the deployment whose replica list
  (registration order) is `nodes`; every replica agrees on `nodes` (`registeredAs_agree`).
* `masterOk γ m`, `replicaOk γ rep` (persistent): a master, a replica, as their packages build
  them.
* `replicaRegRes γ k`: replica node `k`'s registration slot (from the start: `replicaStartRes`).
* `gryffGlobals`: Gryff's package variables' points-to (D3).
* D13: `nodeProph γ k` (replica node `k`'s package prophecy, its words recorded: `node_proph_intro`
  at its boot, before registering) and `replicaReady γ id` (what `NewReplica` needs for replica
  id `id`: the prophecy as the lock invariant's at the empty trace, the replica id's start
  resources, every prediction: `replica_ready_intro` after registration).
-/
module

public import Dsverify.Proof.gryff.Shares
public import Dsverify.Proof.gryff.Server.Deploy
public import Dsverify.Proof.gryff.Server.MasterDefs
public import Dsverify.Proof.gryff.Proto2.Replica
public import Dsverify.Proof.gryff.Boot.Defs

@[expose] public section

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open gryff.boot (gryffGlobals bootProph)

attribute [local instance] GooseGlobalGS.gooseInvGS

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

@[irreducible] def registeredAs (_γ : GryffNames GF) (_k : Nat) (_id : w64)
    (_nodes : List GoString) : IProp GF := registeredAsDef _γ _k _id _nodes
@[irreducible] def replicaRegRes (_γ : GryffNames GF) (_k : Nat) : IProp GF :=
  deployRegResDef _γ _k

instance registeredAs_persistent (γ : GryffNames GF) (k : Nat) (id : w64)
    (nodes : List GoString) : Persistent (registeredAs γ k id nodes) := by
  unfold registeredAs; infer_instance

/-- Every replica registered as `id` with the replica list `nodes` agrees on `nodes`; `nodes`
is the three replicas' addresses in some order, `nodes[id]` is the caller's own, and the
registration fixes the node's id (R11: Gryff's per-replica ghost state is keyed by node). -/
theorem registeredAs_facts (γ : GryffNames GF) (k : Nat) (id : w64)
    (nodes : List GoString) :
    registeredAs γ k id nodes ⊢
      ⌜nodes.Perm replicaAddrs ∧ nodes[uint.nat id]? = replicaAddrs[k]?⌝ ∗
      nodeIdIs γ.proto k id := by
  unfold registeredAs registeredAsDef regReady
  iintro ⟨%hk, ⟨-, %Hf⟩, #Hid, -⟩
  iframe Hid
  ipureintro
  have h1 : replicaAddrs = [addrOf 0, addrOf 1, addrOf 2] := rfl
  have h2 : replicaAddrs[k]? = some (addrOf k) := by
    rcases k with _|_|_|k
    · rfl
    · rfl
    · rfl
    · omega
  rw [h2, h1]
  exact Hf

/-- D13: a registered replica knows every replica id's prediction (`predsSet`), its own being its
node's recorded one (`regPred`: `predIs γ k ws ∗ predIdIs γ id ws`), and the registry's witness
(for `deploy_claim`). -/
theorem registeredAs_preds (γ : GryffNames GF) (k : Nat) (id : w64)
    (nodes : List GoString) :
    registeredAs γ k id nodes ⊢
      ⌜k < 3⌝ ∗ regReady γ.deploy k id nodes ∗ predsSet γ.proto ∗
        regPred γ.proto (uint.nat id) k := by
  unfold registeredAs registeredAsDef
  iintro ⟨%hk, #Hr, -, #Hps, #Hrp⟩
  iframe #
  ipureintro; exact hk

theorem registeredAs_agree (γ : GryffNames GF) (k1 k2 : Nat) (id1 id2 : w64)
    (n1 n2 : List GoString) :
    registeredAs γ k1 id1 n1 ∗ registeredAs γ k2 id2 n2 ⊢ ⌜n1 = n2⌝ := by
  unfold registeredAs
  exact registeredAsDef_agree γ k1 k2 id1 id2 n1 n2

end preds

section specdefs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [RA : RpcHttpAddr GF] [H : RpcHttpHyp GF]

@[irreducible] def masterOk (_γ : GryffNames GF) (_m : Loc) : IProp GF := masterOkDef _γ _m

instance masterOk_persistent (γ : GryffNames GF) (m : Loc) : Persistent (masterOk γ m) := by
  unfold masterOk; infer_instance

/-- A replica (U5's body; for now its rpc receiver's facts, H-U2-4): the replica as a net/rpc
receiver of the `"Replica"` service for the kit's codec (`Server.Register.spec`'s, and
`RpcHttpHyp.Register_spec`'s, precondition). -/
@[irreducible] def replicaOk (_γ : GryffNames GF) (_rep : Loc) : IProp GF :=
  gryffCodec.rcv (ptrIface src.gryff.Replica.ty _rep)
    (net.rpc.rcvrIs gryffCodec (ptrIface src.gryff.Replica.ty _rep) replicaSvc go!"Replica" false)

/-- H-U2-4: a replica is a receiver of the `"Replica"` service. -/
theorem replicaOk_rcvr (γ : GryffNames GF) (rep : Loc) :
    replicaOk γ rep ⊢ gryffCodec.rcv (ptrIface src.gryff.Replica.ty rep)
      (net.rpc.rcvrIs gryffCodec (ptrIface src.gryff.Replica.ty rep) replicaSvc go!"Replica"
        false) := by
  unfold replicaOk; exact .rfl

open github_com.goose_lang.primitive (ProphId) in
/-- Replica node `k`'s trace prophecy (D13): the package variable `traceProph` holds `p` (for
good: only `NewReplica` reads it), `p`'s values are unresolved, and node `k` recorded their words
(`predIs`, its registration carries them). -/
def nodeProph (γ : GryffNames GF) (k : Nat) : IProp GF :=
  iprop(∃ (p : ProphId) (pvs : List val),
    globalAddr gryff.src.gryff.traceProph ↦□ p ∗ proph p pvs ∗ predIs γ.proto k (wordsOf pvs))

open github_com.goose_lang.primitive (ProphId) in
/-- What `NewReplica` needs for replica id `id` from D13: `traceProph`'s prophecy as replica id
`id`'s lock invariant holds it at the empty trace, the replica id's start resources (its trace's
half at `[]`, its receiving cursors), and all three predictions. -/
def replicaReady (γ : GryffNames GF) (id : w64) : IProp GF :=
  iprop(∃ (p : ProphId) (hid : uint.nat id < 3),
    globalAddr gryff.src.gryff.traceProph ↦□ p ∗ replicaProph γ.proto ⟨uint.nat id, hid⟩ p [] [] ∗
      idSlotRes γ.proto ⟨uint.nat id, hid⟩ ∗ predsSet γ.proto)

open github_com.goose_lang.primitive (ProphId) in
/-- **A replica node's boot, before registering** (D13): with the prophecy the gryff package's
initialization created (`gryffnet_wp_initialize_server`, `Server/Boot.lean`), record its words
(`pred_set`) and keep `traceProph` for good. -/
theorem node_proph_intro (γ : GryffNames GF) (k : Nat) (p : ProphId) (pvs : List val) :
    gryffInv2 γ.proto ∗ predTok γ.proto k ∗ globalAddr gryff.src.gryff.traceProph ↦ p ∗
        proph p pvs ⊢ |={⊤}=> nodeProph γ k ∗ ∃ ws, predIs γ.proto k ws := by
  iintro ⟨#Hg, Ht, Hpt, Hp⟩
  imod pred_set γ.proto k p pvs ⊤ (by simp) $$ [Hg Ht Hp] with ⟨Hp, #Hpi⟩
  · iframe Ht Hp; iframe #
  ipersist Hpt
  imodintro
  isplitl [Hp]
  · unfold nodeProph
    iexists p, pvs
    iframe Hp; iframe #
  iexists wordsOf pvs; iframe #

/-- **A replica node's boot, after registering as `id`** (D13): claim the replica id's start
resources and turn the node's prophecy into replica id `id`'s (`replicaProph_intro`: the
registry's answer says `id`'s prediction is the node's). -/
theorem replica_ready_intro (γ : GryffNames GF) (k : Nat) (id : w64)
    (nodes : List GoString) :
    inv deployN (deployInv γ.deploy γ.proto) ∗ registeredAs γ k id nodes ∗
        slotClaimTok γ.proto k ∗ nodeProph γ k ⊢ |={⊤}=> replicaReady γ id := by
  iintro ⟨#Hdep, #Hreg, Hc, Hnp⟩
  icases registeredAs_preds γ k id nodes $$ Hreg with ⟨%hk, #Hr, #Hps, #Hrp⟩
  ihave %Hrf : ⌜nodes.length = 3 ∧ nodes[uint.nat id]? = some (addrOf k)⌝ $$ []
  · unfold regReady
    icases Hr with ⟨-, %Hf⟩
    ipureintro; exact ⟨Hf.1.length_eq, Hf.2⟩
  have hid : uint.nat id < 3 := by
    have h := Hrf.2
    rw [← Hrf.1]
    exact (List.getElem?_eq_some_iff.mp h).1
  imod deploy_claim γ.deploy γ.proto k hk id nodes ⊤ (by simp) $$ [Hdep Hr Hc] with Hres
  · iframe Hc; iframe #
  ihave Hres := (idSlotResN_lt γ.proto (uint.nat id) hid).1 $$ Hres
  unfold nodeProph
  icases Hnp with ⟨%p, %pvs, #Hpt, Hp, #Hpi⟩
  unfold regPred
  icases Hrp with ⟨%ws, #H1, #H2⟩
  imodintro
  unfold replicaReady
  iexists p, hid
  iframe Hpt Hres Hps
  iapply replicaProph_intro γ.proto ⟨uint.nat id, hid⟩ k p pvs ws
  iframe Hp; iframe #

end specdefs

end Perennial.gryff
