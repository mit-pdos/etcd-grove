/-
# The craq kit on `examples/lib/remote` (notes/dsv-craq.md): vocabulary

* **The far side's store** `kvR γ` (`remote.RBase`) over `ModelSet.lean`'s `kvB` (the key-value map
  with failed puts, on bounded strings): its state is the CRAQ protocol's abstract state
  (`ownState γ`, the client spec's `own_state`) of the lifted map (`lift`), the mask of the update
  is `craqEop` (the protocol's invariants), the Go values and bytes are kit.go's `In`, `Out` and
  `Codec()`'s. Its linearization point is the protocol's client update: `lin_opAU` (paxos's
  `lin_opAU`; notes/dsv-craq.md, P1).
* **porcupine's model** `kvS0`/`kvS`: `pM kvB kvDec` (porcupine's operations decoded as the
  store's), with `Model()`'s state `State{M, Pend}` standing for a set it brackets (`kvRep`,
  `ModelSet.lean`'s `Sim`).
* **The deployment's addresses** (kit.go's `ServerAddrs`, `ClientAddrs`, `ConfAddrs`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.ModelSet
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.despreston.go_craq.examples.craqnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.despreston.go_craq

/-! ## The store's state as the protocol's -/

/-- The store's state as the protocol's abstract map. -/
def lift (a : St) : KvM.State := fun k => (a k).map Subtype.val

/-- An output as the protocol's. -/
def liftOut : KOut → KvM.Output
  | .got v => .got (v.map Subtype.val)
  | .done => .done

theorem lift_init : lift kvB.init = KvM.init := rfl

/-- The protocol's step on the lifted state is the store's, lifted. -/
theorem lift_step (i : KIn) (a : St) :
    KvM.stepF i.1 (lift a) = (lift (kvB.step i a).1, liftOut (kvB.step i a).2) := by
  obtain ⟨k | ⟨k, x⟩, h⟩ := i
  · rfl
  · simp only [KvM.stepF, step_put, liftOut, Prod.mk.injEq, and_true]
    funext k'
    simp only [lift, upd]
    by_cases hk : k' = k <;> simp [hk]

/-! ## Go values and bytes -/

section vals
variable [GooseExts] [GoGlobalContext]

/-- An input, boxed (`any` holding an `In`). -/
abbrev inV (p : Bool) (k v : GoString) : GoInterface := interface.mkOk In.ty #(In.mk p k v)

/-- An output, boxed (`any` holding an `Out`). -/
abbrev outV (u f : Bool) (v : GoString) : GoInterface := interface.mkOk Out.ty #(Out.mk u f v)

/-- The store's input `i` as kit.go's `In`. -/
def ivK : KIn → GoInterface
  | ⟨.get k, _⟩ => inV false k []
  | ⟨.put k x, _⟩ => inV true k x

/-- The store's output `o` as kit.go's `Out` (a get's not found and a put's success are both
`Out{}`). -/
def ovK : KOut → GoInterface
  | .got none => outV false false []
  | .got (some x) => outV false true x.1
  | .done => outV false false []

/-- `encStr`'s bytes: the length (one byte), then the string. -/
def encS (s : GoString) : List w8 := W8 s.length :: s

/-- `flag`'s byte. -/
def flagB (b : Bool) : w8 := if b then W8 1 else W8 0

/-- `Codec().EncIn`'s bytes of an input. -/
def encInB : KIn → List w8
  | ⟨.get k, _⟩ => flagB false :: (encS k ++ encS [])
  | ⟨.put k x, _⟩ => flagB true :: (encS k ++ encS x)

/-- `Codec().EncOut`'s bytes of an `Out{u, f, v}`. -/
def encOutB (u f : Bool) (v : GoString) : List w8 := flagB u :: flagB f :: encS v

open Classical in
/-- `Codec().EncOut`'s bytes of a value: a bounded `Out`'s, or nothing for any other value (never
encoded). -/
def encOutV (v : GoInterface) : List w8 :=
  if h : ∃ p : Bool × Bool × Str8, v = outV p.1 p.2.1 p.2.2.1 then
    encOutB (Classical.choose h).1 (Classical.choose h).2.1 (Classical.choose h).2.2.1
  else []

end vals

/-! ## The far side's store -/

section base
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

/-- **The far side's store**: the key-value map (see the file header). -/
def kvR (γ : CraqNames) : RBase GF St KIn KOut where
  B := kvB
  sysState a := ownState γ (lift a)
  Eop := craqEop
  iv := ivK
  ov := ovK
  unk _ := outV true false []
  encIn := encInB
  encOut := encOutV
  reads_stay i st h := by
    obtain ⟨k | ⟨k, x⟩, hi⟩ := i
    · rfl
    · simp [kvB, isPut] at h
  encIn_len i := by
    obtain ⟨k | ⟨k, x⟩, hi⟩ := i
    · simp only [encInB, encS, List.cons_append, List.length_cons, List.length_append,
        List.length_nil]
      simp only [inOk] at hi
      omega
    · simp only [encInB, encS, List.cons_append, List.length_cons, List.length_append]
      simp only [inOk] at hi
      omega
  encOut_len v := by
    unfold encOutV
    split
    · rename_i h
      have := (Classical.choose h).2.2.2
      simp only [encOutB, encS, List.length_cons]
      omega
    · simp

instance kvR_timeless (γ : CraqNames) (a : St) :
    Timeless ((kvR (GF := GF) γ).sysState a) := by
  unfold kvR ownState; simp only; infer_instance

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The store's linearization point is the protocol's client update** (for the caller's
postcondition read on the store's output). -/
theorem lin_opAU [NetProtoGS] [RemoteGS] (γ : CraqNames) (i : KIn) (Φ : KOut → IProp GF) :
    lin (Gg := Gg) (kvR γ) i Φ ⊢
      opAU γ i.1 (fun o => iprop(∃ o' : KOut, ⌜o = liftOut o'⌝ ∗ Φ o')) := by
  unfold lin opAU clientMask
  simp only [kvR]
  iintro Hl
  imod Hl with ⟨%a, Hs, Hk⟩
  imodintro
  iexists lift a
  iframe Hs
  rw [lift_step]
  iintro Hs'
  imod Hk $$ Hs' with HΦ
  imodintro
  iexists _
  iframe HΦ
  ipureintro
  rfl

end base

/-! ## porcupine's model -/

section model
variable [GooseExts] [GoGlobalContext]

/-- An answer `Out{u, f, w}` to input `i`, decoded: unknown is an error; for a get, found is
`w`'s value, not found (with an empty `w`) is none, and anything else an answer no get gives
(`done`); for a put, `Out{}` is its success, anything else an answer no put gives. -/
def decAns (i : KIn) (u f : Bool) (w : Str8) : linkv.Ans KOut :=
  if u then .err else
  match i.1 with
  | .get _ => if f then .ok (.got (some w)) else if w.1 = [] then .ok (.got none) else .ok .done
  | .put _ _ => if !f && w.1 = [] then .ok .done else .ok (.got none)

open Classical in
/-- porcupine's operations as the store's: a boxed input and a boxed bounded `Out`; anything else
decodes to nothing. -/
def kvDec (io : OpV) : Option (KIn × linkv.Ans KOut) :=
  if h : ∃ (i : KIn) (u f : Bool) (w : Str8), io = (ivK i, outV u f w.1) then
    let i := Classical.choose h
    let u := Classical.choose (Classical.choose_spec h)
    let f := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
    let w := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)))
    some (i, decAns i u f w)
  else none

/-- **The store's porcupine model**, as the pending library's invariant sees it (its sequential
model only, as paxos's `woS0`). -/
def kvS0 {GF : BundledGFunctors} : ModelSpec GF (linkv.PSet St KIn) where
  M := linkv.pM kvB kvDec
  rep _ _ _ := iprop(True)
  ioOk i o := iprop(⌜(∃ x : KIn, i = ivK x) ∧ ∃ (u f : Bool) (w : Str8), o = outV u f w.1⌝)
  ioOk_pers _ _ := by infer_instance

end model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A pending put as kit.go's `pend`. -/
def pendOf : KIn → pend
  | ⟨.get k, _⟩ => pend.mk k []
  | ⟨.put k x, _⟩ => pend.mk k x

/-- A model value: the boxed `State{M, Pend}`, its map read-only and holding `a` (lowered), its
slice read-only and holding the puts `P`; `(a, P)` brackets the set `s` (`Sim`); `P` has at most
`k` entries (a step adds at most one). -/
def kvRep (k : Nat) (v : GoInterface) (s : linkv.PSet St KIn) : IProp GF :=
  iprop(∃ (mp : GoMap) (sl : GoSlice) (m : GMap GoString GoString) (a : St) (P : List KIn),
    ⌜v = interface.mkOk State.ty #(State.mk mp sl) ∧ Sim a P s ∧
      (∀ x, m.lookup x = (a x).map Subtype.val) ∧ (∀ i ∈ P, isPut i = true) ∧ P.length ≤ k⌝ ∗
    ownMap mp DFrac.discard m ∗ sl ↦*□ P.map pendOf)

/-- **The store's porcupine model**: `pM kvB kvDec`, over `Model()`'s values. -/
def kvS : ModelSpec GF (linkv.PSet St KIn) where
  M := (kvS0 (GF := GF)).M
  rep k v s := kvRep k v s
  ioOk := (kvS0 (GF := GF)).ioOk
  ioOk_pers := (kvS0 (GF := GF)).ioOk_pers

end spec

/-! ## The deployment -/

/-- The server machines' net/rpc addresses (`ServerAddrs()`): the coordinator's, then chain
machines 2..6's. -/
def serverAddrs : List GoString :=
  [go!"127.0.0.1:7501", go!"127.0.0.1:7502", go!"127.0.0.1:7503", go!"127.0.0.1:7504",
   go!"127.0.0.1:7505", go!"127.0.0.1:7506"]

/-- The client machines' addresses (`ClientAddrs()`), for the orchestrator's calls. -/
def clientAddrs : List GoString :=
  [go!"127.0.0.1:7511", go!"127.0.0.1:7512", go!"127.0.0.1:7513", go!"127.0.0.1:7514",
   go!"127.0.0.1:7515"]

/-- The configuration addresses (`ConfAddrs()`): client machines 0..4's, then the coordinator's
(unused) and chain machines 2..6's. -/
def confAddrs : List GoString :=
  [go!"127.0.0.1:7521", go!"127.0.0.1:7522", go!"127.0.0.1:7523", go!"127.0.0.1:7524",
   go!"127.0.0.1:7525", go!"127.0.0.1:7530", go!"127.0.0.1:7531", go!"127.0.0.1:7532",
   go!"127.0.0.1:7533", go!"127.0.0.1:7534", go!"127.0.0.1:7535"]

/-! ## The kit's specs (KitProof.lean proves them) -/

section kitspecs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

/-- `Codec()`: the store's codec, for the store over the protocol's names `γ`. -/
abbrev Codec.spec : Prop :=
  ∀ γ : CraqNames,
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! github_com.despreston.go_craq.examples.craqnet.Codec)) (Val #()))
  {{ (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec), RET #cd;
      github_com.mit_pdos.etcd_grove.examples.lib.remote.codecOk
        (kvR (Gg := hG.goose_globalGS) γ) cd }}

/-- `Gen`: a client's next input, a boxed bounded put or get. -/
abbrev Gen.spec : Prop :=
  ⊢ EtcdGrove.lintest.genSpec (GF := GF)
      (functions github_com.despreston.go_craq.examples.craqnet.Gen [])
      (fun i => iprop(∃ x : KIn, ⌜i = ivK x⌝))

end kitspecs

end github_com.despreston.go_craq.examples.craqnet
end Perennial
