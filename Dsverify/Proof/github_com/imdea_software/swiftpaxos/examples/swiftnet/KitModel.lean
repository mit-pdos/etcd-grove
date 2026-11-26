/-
# The swiftpaxos kit's store, porcupine model, codec and generator (kit.go; notes/dsv-swiftpaxos.md,
"The kit over remote"; as dsv-rabia's `KitModel.lean` and dsv-paxos's `Kit.lean`)

* **The store** `swB` (`ModelSet.lean`): linkv's pending-writes store of the key-value map over the
  kit's inputs `KIn` and bounded outputs `BStr`.
* **The far side's store** `swR sys E` (`remote.RBase`), for any base state `sys` of the map and
  mask `E` of its update: the Go values and bytes are kit.go's `In`, `Out` and `Codec()`'s. The
  client step instantiates `sys`/`E` with the SwiftPaxos invariant's (as rabia's `kvR γ`); nothing
  here depends on them.
* **porcupine's model** `swS0`/`swS`: `pSeq swB` through the decoder `swDec`; a model value (kit.go's
  `State{Cur, Pend}`, read-only) simulates its set (`Sim`, `ModelSet.lean`).
* **The specs** of `Model()` (porcupine's `isModel swS`), `Codec()` and `Gen`. kit.go's `Equal` is
  always `false`: a model value does not determine its set (`ModelSet.equal_unsound`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ModelSet
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote

/-! ## Countability -/

instance KIn.countable : Pos.Countable KIn :=
  .ofInjective (fun x : KIn => Pos.Countable.encode x.1)
    (fun _ _ h => Subtype.ext (Pos.encode_inj h))

instance BStr.countable : Pos.Countable BStr :=
  .ofInjective (fun x : BStr => Pos.Countable.encode x.1)
    (fun _ _ h => Subtype.ext (Pos.encode_inj h))

/-! ## The Go values and bytes -/

section vals
variable [GooseExts] [GoGlobalContext]

/-- kit.go's `In` of an input. -/
def inVal (i : KIn) : In := In.mk i.put (W64 i.key) i.val

/-- An input, boxed (`any` holding an `In`). -/
abbrev inV (i : KIn) : GoInterface := interface.mkOk In.ty #(inVal i)

/-- An output `Out{u, w}`, boxed. -/
abbrev outV (u : Bool) (w : GoString) : GoInterface := interface.mkOk Out.ty #(Out.mk u w)

/-- A call's answer, boxed: `Out{false, w}`, or the unknown output `Out{true, ""}`. -/
def ansV : Ans BStr → GoInterface
  | .ok w => outV false w.1
  | .err => outV true []

/-- `Codec()`'s bytes of an input: the put flag, the key's byte, the value. -/
def encInB (i : KIn) : List w8 := (if i.put then W8 1 else W8 0) :: W8 i.key :: i.val

/-- `Codec()`'s bytes of an output `Out{u, w}`: the unknown flag, the value. -/
def encOutB (u : Bool) (w : GoString) : List w8 := (if u then W8 1 else W8 0) :: w

open Classical in
/-- `Codec()`'s bytes of a value: a bounded `Out`'s, or nothing for any other value (never
encoded). -/
def encOutV (v : GoInterface) : List w8 :=
  if h : ∃ p : Bool × BStr, v = outV p.1 p.2.1 then encOutB (Classical.choose h).1 (Classical.choose h).2.1 else []

theorem encInB_len (i : KIn) : (encInB i).length < 2 ^ 63 := by
  have h : i.val.length < 2 ^ 48 := i.2.2
  simp only [encInB, List.length_cons]
  omega

theorem encOutV_len (v : GoInterface) : (encOutV v).length < 2 ^ 63 := by
  unfold encOutV
  split
  · rename_i h
    have := (Classical.choose h).2.2
    simp only [encOutB, List.length_cons]
    omega
  · simp

end vals

/-! ## The far side's store -/

section base
variable [GooseExts] [GoGlobalContext] {GF : BundledGFunctors}

/-- **The far side's store** over the base state `sys` of the map and the mask `E` of its update
(see the file header). -/
def swR (sys : St → IProp GF) (E : CoPset) : RBase GF St KIn KIn BStr where
  B := swB
  sysState := sys
  Eop := E
  iv := inV
  ov o := outV false o.1
  unk _ := outV true []
  encIn := encInB
  encOut := encOutV
  reads_stay i st h := by rw [swB_get i h]
  encIn_len := encInB_len
  encOut_len := encOutV_len

end base

/-! ## porcupine's model -/

section model
variable [GooseExts] [GoGlobalContext]

open Classical in
/-- porcupine's operations as the store's: a boxed input and a boxed answer; anything else decodes
to nothing. -/
def swDec (io : OpV) : Option (KIn × Ans BStr) :=
  if h : ∃ (i : KIn) (a : Ans BStr), io = (inV i, ansV a) then
    some (Classical.choose h, Classical.choose (Classical.choose_spec h))
  else none

/-- **The store's porcupine model**, as the pending library's invariant sees it (its sequential
model only, made at the start): `pSeq swB` through `swDec`. -/
def swS0 {GF : BundledGFunctors} : ModelSpec GF (PSet St KIn) where
  M := pM swB swDec
  rep _ _ _ := iprop(True)
  ioOk i o := iprop(⌜(∃ x : KIn, i = inV x) ∧ ∃ a : Ans BStr, o = ansV a⌝)
  ioOk_pers _ _ := by infer_instance

end model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- kit.go's `State{Cur, Pend}` holding `cur` and `pend`, read-only: `Cur` holds `cur`, `Pend` the
slices `psl`, the `i`-th holding `pend`'s `i`-th list. -/
def stateOwn (cs ps : GoSlice) (cur : List GoString) (pend : List (List GoString)) : IProp GF :=
  iprop(cs ↦*□ cur ∗ ∃ psl : List GoSlice, ⌜psl.length = pend.length⌝ ∗ ps ↦*□ psl ∗
    □ ∀ (i : Nat) (sl : GoSlice), ⌜psl[i]? = some sl⌝ → sl ↦*□ pend.getD i [])

instance stateOwn_persistent (cs ps : GoSlice) (cur : List GoString)
    (pend : List (List GoString)) : Persistent (stateOwn (GF := GF) cs ps cur pend) := by
  unfold stateOwn; infer_instance

/-- A model value of index `n`: the boxed `State{cs, ps}`, read-only, holding two keys' values
`cur` and pending puts `pend` (each list of at most `n`), which simulate the set `s`. -/
def swRep (n : Nat) (v : GoInterface) (s : PSet St KIn) : IProp GF :=
  iprop(∃ (cs ps : GoSlice) (cur : List GoString) (pend : List (List GoString)),
    ⌜v = interface.mkOk State.ty #(State.mk cs ps) ∧ cur.length = 2 ∧ pend.length = 2 ∧
      (∀ k, (pend.getD k []).length ≤ n) ∧ Sim cur pend s⌝ ∗ stateOwn cs ps cur pend)

instance swRep_persistent (n : Nat) (v : GoInterface) (s : PSet St KIn) :
    Persistent (swRep (GF := GF) n v s) := by
  unfold swRep; infer_instance

/-- **The store's porcupine model** (pending puts): `pSeq swB` through `swDec`. -/
def swS : ModelSpec GF (PSet St KIn) where
  M := (swS0 (GF := GF)).M
  rep n v s := swRep n v s
  ioOk := (swS0 (GF := GF)).ioOk
  ioOk_pers := (swS0 (GF := GF)).ioOk_pers

end spec

/-! ## The specs -/

section specs

attribute [local instance] Dsv.netShaExts Dsv.netShaExtsSemantics Dsv.netShaExtsInterp
  Dsv.netShaExts_has

variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

variable [SwiftNetPkgState GF]
variable [package_sem' : github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]

local notation "kpkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

/-- `Model()`: the key-value map's porcupine model. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! github_com.imdea_software.swiftpaxos.examples.swiftnet.Model)) (Val #()))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m; isModel (swS (GF := GF)) m }}

/-- `Codec()`: the key-value map's codec, for any base state and mask of the far side. -/
abbrev Codec.spec : Prop :=
  ∀ (sys : St → IProp GF) (E : CoPset),
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec)) (Val #()))
  {{ (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec), RET #cd;
      codecOk (swR sys E) cd }}

/-- `Gen`: a client's input, one of the store's. -/
abbrev Gen.spec : Prop :=
  ⊢ EtcdGrove.lintest.genSpec (GF := GF)
      (functions github_com.imdea_software.swiftpaxos.examples.swiftnet.Gen [])
      (fun x => iprop(∃ i : KIn, ⌜x = inV i⌝))

end specs

end github_com.imdea_software.swiftpaxos.examples.swiftnet
end Perennial
