/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto/InvDefs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The definitions of Gryff's invariant (split from `Proto/Inv.lean`, which re-exports them with
the laws, so that the laws' proofs can use `Proto/InvPure.lean`). See `Proto/Inv.lean`.
-/
module

public import Dsverify.Proof.gryff.Names
public import Dsverify.Proof.gryff.Proto.Model
public import Dsverify.Proof.gryff.Lab.ModelsCas
public import Dsverify.Proof.gryff.Lab.ClientSpec
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode proto dsverify_lab.harness

/-- The namespace of Gryff's invariant. -/
def gryffN : Namespace := ndot nroot "gryff"

instance regInput.countable : Pos.Countable (RegInput w64) :=
  .ofInjective (fun
      | .read => Pos.Countable.encode ((0 : Nat), W64 0, W64 0)
      | .write v => Pos.Countable.encode ((1 : Nat), v, W64 0)
      | .cas o n => Pos.Countable.encode ((2 : Nat), o, n))
    (by rintro (_|_|_) (_|_|_) h <;> have h := Pos.encode_inj h <;> simp_all)

instance regOutput.countable : Pos.Countable (RegOutput w64) :=
  .ofInjective (fun
      | .value v => Pos.Countable.encode ((0 : Nat), v)
      | .done => Pos.Countable.encode ((1 : Nat), W64 0)
      | .swapped b => Pos.Countable.encode ((if b then 2 else 3 : Nat), W64 0))
    (by rintro (_|_|(_|_)) (_|_|(_|_)) h <;> have h := Pos.encode_inj h <;> simp_all)

/-- An operation's place in the tag order: not fixed yet (its coordinator has not started it),
or fixed by its prophecy (D2) when the frontier was `freg`: the tag it writes or whose value it
returns (`some t`), or `none`: it never takes effect (its prophecy is never resolved). -/
inductive Placement where
  | unplaced
  | placed (p : Option PTag) (freg : PTag)
deriving DecidableEq

instance placement.countable : Pos.Countable Placement :=
  .ofInjective (fun
      | .unplaced => Pos.Countable.encode ((0 : Nat), (none : Option PTag), tag0)
      | .placed p f => Pos.Countable.encode ((1 : Nat), p, f))
    (by rintro (_|_) (_|_) h <;> have h := Pos.encode_inj h <;> simp_all)

/-- A client operation: its input, its place, and its client's saved propositions: `au` the
pending atomic update, `rcpt` the receipt (a predicate on the output), `claim` the token its
client trades for the receipt. -/
structure OpMeta where
  input : RegInput w64
  place : Placement
  au : GName
  rcpt : GName
  claim : GName

instance OpMeta.countable : Pos.Countable OpMeta :=
  .ofInjective (fun m => Pos.Countable.encode (m.input, m.place, m.au, m.rcpt, m.claim))
    (by rintro ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ h; have h := Pos.encode_inj h; simp_all)

/-- What is fixed of an operation at its registration (H-U4-7): its input and its client's names
(the `γ.ops` ghost map's values, persistent elements). Its place is recorded separately
(`γ.places`); `OpMeta` is their join (`opsJoin`). -/
structure OpInfo where
  input : RegInput w64
  au : GName
  rcpt : GName
  claim : GName

instance OpInfo.countable : Pos.Countable OpInfo :=
  .ofInjective (fun m => Pos.Countable.encode (m.input, m.au, m.rcpt, m.claim))
    (by rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h; have h := Pos.encode_inj h; simp_all)

/-- An EPaxos instance's committed attributes: the compare-and-swap (old, new), the client
operation it serves, seq, deps (one per replica), base. -/
structure InstAttrs where
  old : Int
  new : Int
  op : OpId
  seq : Int
  deps : List Int
  base : Int × PTag
deriving DecidableEq

instance InstAttrs.countable : Pos.Countable InstAttrs :=
  .ofInjective (fun a => Pos.Countable.encode (a.old, a.new, a.op, a.seq, a.deps, a.base))
    (by rintro ⟨_, _, _, _, _, _⟩ ⟨_, _, _, _, _, _⟩ h; have h := Pos.encode_inj h; simp_all)

instance ExecEntry.countable : Pos.Countable ExecEntry :=
  .ofInjective (fun e => Pos.Countable.encode (e.inst, e.base, e.old, e.new, e.res))
    (by rintro ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ h; have h := Pos.encode_inj h; simp_all)

/-! ## The pure facts -/

/-- A tag as a `w64` register value's place: the order is `tagLe`; at an equal place, a write or
an RMW comes before the reads of its tag (`rank`). -/
def rank : RegInput w64 → Nat
  | .read => 1
  | _ => 0

/-- The place of a placed operation. -/
def Placement.tag? : Placement → Option PTag
  | .placed (some t) _ => some t
  | _ => none

/-- Replaying `l`'s inputs from `s` with the model's step gives each recorded output and ends at
`s'`. -/
def replayOk : w64 → List (RegInput w64 × RegOutput w64) → w64 → Prop
  | s, [], s' => s' = s
  | s, (i, o) :: l, s' => (casApply s i).2 = o ∧ replayOk (casApply s i).1 l s'

/-- The pure facts of the invariant as first frozen (the turn fact adapted to H-U4-4's turns):
`σ` the abstract register, `stores` the replica nodes' registers, `tv` the tags' values, `lbs` the
stores' lower bounds, `ops` the operations, `lin` the linearized operations with their outputs,
`execS` the agreed RMW chain, `preds` the replica nodes' predicted execution sequences, `insts` the
committed instances, `turns` each client id's turn (next request id, last request pending). -/
def invFactsCore (σ : w64) (stores : GMap Nat (w64 × PTag)) (tv : GMap PTag w64)
    (lbs : GMap (Nat × PTag) Unit) (ops : GMap OpId OpMeta)
    (lin : List (OpId × RegOutput w64)) (insts : GMap (Int × Int) InstAttrs)
    (execS : List ExecEntry) (preds : GMap Nat (List ExecEntry))
    (turns : GMap Int (Int × Bool)) : Prop :=
  ∃ a b c : w64 × PTag,
    stores.lookup 0 = some a ∧ stores.lookup 1 = some b ∧ stores.lookup 2 = some c ∧
    let F := median3 a.2 b.2 c.2
    -- tags and stores
    tv.lookup tag0 = some (W64 0) ∧
    (∀ k vt, stores.lookup k = some vt → tv.lookup vt.2 = some vt.1) ∧
    (∀ k t, lbs.lookup (k, t) = some () → ∃ vt, stores.lookup k = some vt ∧ tagLe t vt.2) ∧
    tv.lookup F = some σ ∧
    -- placement and linearization: an operation is linearized iff it is placed at a tag at or
    -- below the frontier and not below the frontier of its placement
    -- (a read also needs its tag's producer linearized, or its tag to be tag0)
    (∀ id m, ops.lookup id = some m →
      ((∃ o, (id, o) ∈ lin) ↔
        ∃ t freg, m.place = .placed (some t) freg ∧ tagLe freg t ∧ tagLe t F ∧
          (rank m.input = 0 ∨ t = tag0 ∨ ∃ id' m' o', ops.lookup id' = some m' ∧
            rank m'.input = 0 ∧ m'.place.tag? = some t ∧ (id', o') ∈ lin))) ∧
    -- client ids: one operation in flight per id (its turn is past every registered request,
    -- and every request but the last is linearized)
    (∀ cid r b r', turns.lookup cid = some (r, b) → (ops.lookup (cid, r')).isSome → r' < r) ∧
    (∀ cid r1 r2, r1 < r2 → (ops.lookup (cid, r1)).isSome → (ops.lookup (cid, r2)).isSome →
      ∃ o, ((cid, r1), o) ∈ lin) ∧
    -- producers: a stored tag other than tag0 is a write's of its value, or an RMW's result in
    -- the chain
    (∀ t v, tv.lookup t = some v → t ≠ tag0 →
      ∃ id m, ops.lookup id = some m ∧ m.place.tag? = some t ∧
        (m.input = .write v ∨ ∃ e a, e ∈ execS ∧ e.res.2 = t ∧ W64 e.res.1 = v ∧
          insts.lookup e.inst = some a ∧ a.op = id)) ∧
    (∀ id o, (id, o) ∈ lin → ∃ m, ops.lookup id = some m) ∧
    (lin.map Prod.fst).Nodup ∧
    -- `lin` in place order (writes and RMWs before the reads of their tag), and its replay
    List.Pairwise (fun x y => ∃ mx my tx ty, ops.lookup x.1 = some mx ∧ ops.lookup y.1 = some my ∧
        mx.place.tag? = some tx ∧ my.place.tag? = some ty ∧
        (tagLt tx ty ∨ (tx = ty ∧ rank mx.input ≤ rank my.input))) lin ∧
    replayOk (W64 0) (lin.filterMap (fun x => (ops.lookup x.1).map (fun m => (m.input, x.2)))) σ ∧
    -- history: a stored tag at or below the frontier holds the replay of the operations placed at
    -- or below it
    (∀ t v, tv.lookup t = some v → tagLe t F →
      replayOk (W64 0) ((lin.filter (fun x => match (ops.lookup x.1).bind (fun m => m.place.tag?) with
          | some tx => decide (tagLe tx t) | none => false)).filterMap
        (fun x => (ops.lookup x.1).map (fun m => (m.input, x.2)))) v) ∧
    -- producers: a write's or an RMW's place is its own; a read's place is a stored tag
    (∀ id1 id2 m1 m2 t, ops.lookup id1 = some m1 → ops.lookup id2 = some m2 →
      m1.place.tag? = some t → m2.place.tag? = some t → rank m1.input = 0 →
      rank m2.input = 0 → id1 = id2) ∧
    -- the RMW chain: the executor's, each result stored, each entry's operation placed at its
    -- result's tag; every replica node's predicted sequence agrees with it (one is a prefix of
    -- the other)
    execOk none execS ∧
    (∀ e, e ∈ execS → tv.lookup e.res.2 = some (W64 e.res.1)) ∧
    (∀ e a m, e ∈ execS → insts.lookup e.inst = some a → ops.lookup a.op = some m →
      m.place.tag? = some e.res.2) ∧
    (∀ k p, preds.lookup k = some p → execS <+: p ∨ p <+: execS) ∧
    (∀ k1 k2 p1 p2, preds.lookup k1 = some p1 → preds.lookup k2 = some p2 → p1 <+: p2 ∨ p2 <+: p1)

/-- A signed 64-bit integer. -/
def inRange (x : Int) : Prop := -2 ^ 63 ≤ x ∧ x < 2 ^ 63

/-- H-U4-2's facts (X1-X4): every stored tag is at least `tag0`; a stored tag's producer was
placed at it from a frontier at or below it (and an RMW producer's input is its chain entry's
CAS); every chain entry's base is a stored (value, tag), and its values are signed 64-bit. -/
def extraFacts (tv : GMap PTag w64) (ops : GMap OpId OpMeta) (insts : GMap (Int × Int) InstAttrs)
    (execS : List ExecEntry) : Prop :=
  (∀ t v, tv.lookup t = some v → tagLe tag0 t) ∧
  (∀ t v, tv.lookup t = some v → t ≠ tag0 → ∃ id m freg, ops.lookup id = some m ∧
    m.place = .placed (some t) freg ∧ tagLe freg t ∧
    (m.input = .write v ∨ ∃ e a, e ∈ execS ∧ e.res.2 = t ∧ W64 e.res.1 = v ∧
      insts.lookup e.inst = some a ∧ a.op = id ∧ m.input = .cas (W64 e.old) (W64 e.new))) ∧
  (∀ e ∈ execS, tv.lookup e.base.2 = some (W64 e.base.1) ∧ inRange e.base.1 ∧ inRange e.old ∧
    inRange e.new)

/-- The facts added with H-U4-2 (X5), H-U4-5 and H-U4-4: the stores map has only the keys 0, 1,
2; each store's current tag is a recorded lower bound (the invariant keeps a copy of every lower
bound's element: `storeIs_lb`); a client id whose last request is not pending (`(r, false)`)
has all its registered requests linearized. -/
def bookFacts (stores : GMap Nat (w64 × PTag)) (lbs : GMap (Nat × PTag) Unit)
    (ops : GMap OpId OpMeta) (lin : List (OpId × RegOutput w64)) (turns : GMap Int (Int × Bool)) :
    Prop :=
  (∀ k vt, stores.lookup k = some vt → k < 3) ∧
  (∀ k vt, stores.lookup k = some vt → lbs.lookup (k, vt.2) = some ()) ∧
  (∀ cid r r', turns.lookup cid = some (r, false) → (ops.lookup (cid, r')).isSome →
    ∃ o, ((cid, r'), o) ∈ lin)

/-- The facts of the first interface change: `invFactsCore`, H-U4-2's `extraFacts`, and
`bookFacts`. -/
def invFactsB (σ : w64) (stores : GMap Nat (w64 × PTag)) (tv : GMap PTag w64)
    (lbs : GMap (Nat × PTag) Unit) (ops : GMap OpId OpMeta)
    (lin : List (OpId × RegOutput w64)) (insts : GMap (Int × Int) InstAttrs)
    (execS : List ExecEntry) (preds : GMap Nat (List ExecEntry))
    (turns : GMap Int (Int × Bool)) : Prop :=
  invFactsCore σ stores tv lbs ops lin insts execS preds turns ∧ extraFacts tv ops insts execS ∧
    bookFacts stores lbs ops lin turns

/-- H-U4-9's fact: every chain entry's operation is registered. -/
def chainReg (ops : GMap OpId OpMeta) (insts : GMap (Int × Int) InstAttrs)
    (execS : List ExecEntry) : Prop :=
  ∀ e a, e ∈ execS → insts.lookup e.inst = some a → (ops.lookup a.op).isSome

/-- H-U4-10's fact: placed writes are at their own client's tags with `rmwc = 0`, placed RMWs at
`rmwc ≥ 1`. -/
def placeShapes (ops : GMap OpId OpMeta) : Prop :=
  ∀ id m t, ops.lookup id = some m → m.place.tag? = some t →
    (∀ v, m.input = .write v → t.2.1 = id.1 ∧ t.2.2 = 0) ∧ (∀ o n, m.input = .cas o n → 1 ≤ t.2.2)

/-- The pure facts of the invariant: `invFactsB` (`invFactsCore`, H-U4-2's `extraFacts`,
`bookFacts`), H-U4-9's `chainReg` and H-U4-10's `placeShapes`. -/
def invFacts (σ : w64) (stores : GMap Nat (w64 × PTag)) (tv : GMap PTag w64)
    (lbs : GMap (Nat × PTag) Unit) (ops : GMap OpId OpMeta)
    (lin : List (OpId × RegOutput w64)) (insts : GMap (Int × Int) InstAttrs)
    (execS : List ExecEntry) (preds : GMap Nat (List ExecEntry))
    (turns : GMap Int (Int × Bool)) : Prop :=
  invFactsB σ stores tv lbs ops lin insts execS preds turns ∧ chainReg ops insts execS ∧
    placeShapes ops

/-- The operations (`OpMeta`) are the registrations (`info`, fixed) joined with the places
(`places`, fixed once; H-U4-7); only registered operations are placed. -/
def opsJoin (ops : GMap OpId OpMeta) (info : GMap OpId OpInfo) (places : GMap OpId Placement) :
    Prop :=
  (∀ id, ops.lookup id = (info.lookup id).map
    (fun n => ⟨n.input, (places.lookup id).getD .unplaced, n.au, n.rcpt, n.claim⟩)) ∧
  (∀ id, (places.lookup id).isSome → (info.lookup id).isSome)

/-- Client-id and connection bindings (H-U4-8): a placed operation is of a client id bound to a
connection, and its request id is at most the last one that connection's placer placed. -/
def connFacts (conns : GMap w32 (Option Nat)) (placers : GMap Nat Int)
    (places : GMap OpId Placement) : Prop :=
  (∀ id, (places.lookup id).isSome → ∃ (hs : w32) (cid : Nat), id.1 = sint.Z hs ∧
    conns.lookup hs = some (some cid)) ∧
  (∀ (hs : w32) (cid : Nat) r, conns.lookup hs = some (some cid) →
    (places.lookup (sint.Z hs, r)).isSome → ∃ n, placers.lookup cid = some n ∧ r ≤ n)

/-! ## The resources -/

section defs
variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [InvGS_gen .hasLC GF]

/-- The client's half of the abstract register (`own_state`). -/
def regHalf (γ : ProtoNames) (σ : w64) : IProp GF := ghostVar γ.reg (1 : Qp).half σ

/-- The client's update for an operation with input `i`, commit postcondition `Q`: a one-shot
fancy update from the mask outside Gryff's invariant (where a replica's step fires it, the
invariant open) that takes the register `σ` to `casApply σ i`. Port: the lab's was an Iris atomic
update at `clientN` (its driver's); here it is the one-shot form of remote's linearization point
(`remote.linF`, which `remote.lin_linF` gives from `remote.lin` of the kit's store `casR`, whose `Eop`
is `gryffN`, `Kit.lean`'s `lin_opAU`), which cannot abort (the proof never aborts it: `opAU_fire`
commits once). -/
def opAU (γ : ProtoNames) (i : RegInput w64) (Q : w64 → w64 → RegOutput w64 → IProp GF) :
    IProp GF :=
  iprop(|={⊤ \ ↑gryffN, ∅}=> ∃ σ, regHalf γ σ ∗
    (regHalf γ (casApply σ i).1 ={∅, ⊤ \ ↑gryffN}=∗ Q σ (casApply σ i).1 (casApply σ i).2))

/-- An operation's commit postcondition, saved (over `(σ, σ', o)`). -/
def savedQ (γq : GName) (Q : w64 → w64 → RegOutput w64 → IProp GF) : IProp GF :=
  savedPredOwn γq DFrac.discard (fun x : w64 × w64 × RegOutput w64 => Q x.1 x.2.1 x.2.2)

/-- An operation's resources in the invariant: its client's atomic update (for the commit
postcondition `Q` saved under `rcpt`) while it is not linearized; once linearized with output
`o`, the commit's `Q σ σ' o` until its client claims it with the token `claim`. -/
def opRes (γ : ProtoNames) (lin : List (OpId × RegOutput w64)) (id : OpId) (m : OpMeta) :
    IProp GF :=
  iprop((⌜∀ o, (id, o) ∉ lin⌝ ∗ ∃ Q, savedQ m.rcpt Q ∗ ▷ opAU γ m.input Q) ∨
    (∃ (o : RegOutput w64) (Q : w64 → w64 → RegOutput w64 → IProp GF) (σ σ' : w64),
      ⌜(id, o) ∈ lin⌝ ∗ savedQ m.rcpt Q ∗ (▷ Q σ σ' o ∨ token m.claim)))

/-- The invariant's body. `ops` is not a ghost map's value: it is the join (`opsJoin`) of the
registrations `info` (`γ.ops`) and the places `places` (`γ.places`). The invariant keeps a copy
of every store lower bound's (persistent) element (H-U4-5). It holds half of the placers map's
authority; the other half is `placersInv`'s (`Proto/Wire.lean`, H-U4-12). -/
def gryffInvBody (γ : ProtoNames) : IProp GF :=
  iprop(∃ (σ : w64) (stores : GMap Nat (w64 × PTag)) (tv : GMap PTag w64)
      (lbs : GMap (Nat × PTag) Unit) (ops : GMap OpId OpMeta) (info : GMap OpId OpInfo)
      (places : GMap OpId Placement)
      (lin : List (OpId × RegOutput w64)) (insts : GMap (Int × Int) InstAttrs)
      (execS : List ExecEntry) (preds : GMap Nat (List ExecEntry))
      (turns : GMap Int (Int × Bool)) (conns : GMap w32 (Option Nat)) (placers : GMap Nat Int),
    ghostVar γ.reg (1 : Qp).half σ ∗ ghostMapAuth γ.stores 1 stores ∗
    ghostMapAuth γ.tagVal 1 tv ∗ ghostMapAuth γ.storeLbs 1 lbs ∗ ghostMapAuth γ.ops 1 info ∗
    ghostMapAuth γ.places 1 places ∗
    monoListAuthOwn γ.lin 1 lin ∗ ghostMapAuth γ.insts 1 insts ∗
    monoListAuthOwn γ.execSeq 1 execS ∗ ghostMapAuth γ.preds 1 preds ∗
    ghostMapAuth γ.turns 1 turns ∗ ghostMapAuth γ.conns 1 conns ∗
    ghostMapAuth γ.placers (1 : Qp).half placers ∗
    ⌜invFacts σ stores tv lbs ops lin insts execS preds turns⌝ ∗
    ⌜opsJoin ops info places⌝ ∗ ⌜connFacts conns placers places⌝ ∗
    ([∗map] kt ↦ _u ∈ lbs, ghostMapElem γ.storeLbs kt DFrac.discard ()) ∗
    [∗map] id ↦ m ∈ ops, opRes γ lin id m)

/-- Gryff's invariant. -/
def gryffInvP (γ : ProtoNames) : IProp GF := iprop(inv gryffN (gryffInvBody γ))

/-- Tag `t`'s value is `v` (persistent witness). -/
def tagValIs (γ : ProtoNames) (t : PTag) (v : w64) : IProp GF :=
  ghostMapElem γ.tagVal t DFrac.discard v

/-- Replica node `k`'s register is `(v, t)` (its lock invariant's element). -/
def storeIs (γ : ProtoNames) (k : Nat) (v : w64) (t : PTag) : IProp GF :=
  ghostMapElem γ.stores k (DFrac.own 1) (v, t)

/-- Replica node `k`'s register's tag is at least `t`, for good (persistent). -/
def storeLb (γ : ProtoNames) (k : Nat) (t : PTag) : IProp GF :=
  ghostMapElem γ.storeLbs (k, t) DFrac.discard ()

/-- Instance `i`'s committed attributes are `a` (persistent). -/
def instIs (γ : ProtoNames) (i : Int × Int) (a : InstAttrs) : IProp GF :=
  ghostMapElem γ.insts i DFrac.discard a

/-- Replica node `k` has registration id `id` (persistent; the registry sets it). -/
def nodeIdIs (γ : ProtoNames) (k : Nat) (id : w64) : IProp GF :=
  ghostMapElem γ.nodeIds k DFrac.discard id

instance gryffInvP_persistent (γ : ProtoNames) : Persistent (gryffInvP (GF := GF) γ) := by
  unfold gryffInvP; infer_instance

end defs

end Perennial.gryff
