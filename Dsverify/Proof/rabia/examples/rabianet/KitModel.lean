/-
# The rabia kit's store, porcupine model, codec and generator (notes/dsv-rabia.md; as paxos's
`Kit.lean`)

* **The store** `kvB` (`ModelSet.lean`): linkv's pending-writes store of the key-value map `kv`
  (`Core/Model.lean`), on the workload's inputs `KIn` and bounded outputs `KOut`.
* **The far side's store** `kvR γ` (`remote.RBase`): the map's state is the Rabia invariant's
  client half (`kvState γ.rab`), the mask of the update is `rabiaE`, the Go values and bytes are
  kit.go's `In`, `Out` and `Codec()`'s. Its linearization point is the client's update `opAU`
  (`lin_opAU`, `slotUpd_opAU`).
* **porcupine's model** `kvS0`/`kvS`: `pSeq kvB` through the decoder `kvDec`; a model value
  (kit.go's `State`) stands for `kvSet es` (`ModelSet.lean`).
* **The specs** of `Model()`, `Codec()` and `gens()`.
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.ModelSet
public import Dsverify.Proof.rabia.examples.rabianet.Base
public import Dsverify.Proof.rabia.Core.Proto
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace rabia.examples.rabianet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote Perennial.rabia
  Perennial.rabia.model

/-! ## Countability -/

/-- An input as a triple. -/
def kinT (i : KvInput GoString GoString) : Bool × GoString × GoString := match i with
  | .put k v => (true, k, v)
  | .get k => (false, k, [])

theorem kinT_inj : Function.Injective kinT := by
  intro a b h
  cases a <;> cases b <;> simp_all [kinT]

instance KIn.countable : Pos.Countable KIn :=
  .ofInjective (fun x : KIn => Pos.Countable.encode (kinT x.1))
    (fun a b h => Subtype.ext (kinT_inj (Pos.encode_inj h)))

/-- An output as an optional optional string. -/
def koutT (o : KvOutput GoString) : Option (Option GoString) := match o with
  | .done => none
  | .got w => some w

theorem koutT_inj : Function.Injective koutT := by
  intro a b h
  cases a <;> cases b <;> simp_all [koutT]

instance KOut.countable : Pos.Countable KOut :=
  .ofInjective (fun x : KOut => Pos.Countable.encode (koutT x.1))
    (fun a b h => Subtype.ext (koutT_inj (Pos.encode_inj h)))

/-! ## The Go values and bytes -/

section vals
variable [GooseExts] [GoGlobalContext]

/-- kit.go's `In` of an input. -/
def inVal (i : KvInput GoString GoString) : In := match i with
  | .put k v => In.mk true k v
  | .get k => In.mk false k []

/-- kit.go's `Out` of an output. -/
def outVal (o : KvOutput GoString) : Out := match o with
  | .done => Out.mk false true false []
  | .got none => Out.mk false false false []
  | .got (some v) => Out.mk false false true v

/-- An input, boxed (`any` holding an `In`). -/
abbrev inV (i : KvInput GoString GoString) : GoInterface := interface.mkOk In.ty #(inVal i)

/-- An output, boxed. -/
abbrev outV (o : KvOutput GoString) : GoInterface := interface.mkOk Out.ty #(outVal o)

/-- The unknown output, boxed. -/
abbrev unkV : GoInterface := interface.mkOk Out.ty #(Out.mk true false false [])

/-- A call's answer, boxed. -/
def ansV : linkv.Ans KOut → GoInterface
  | .ok o => outV o.1
  | .err => unkV

/-- `x`'s little-endian bytes (kit.go's `putU64`). -/
def u64le (x : w64) : List w8 :=
  (List.range 8).map fun j : Nat => W8 (uint.Z (x >>> W64 (8 * (j : Int))))

/-- `Codec()`'s bytes of an input: the put flag, the key's length, the key, the value. -/
def encInB (i : KvInput GoString GoString) : List w8 := match i with
  | .put k v => W8 1 :: (u64le (W64 k.length) ++ k ++ v)
  | .get k => W8 0 :: (u64le (W64 k.length) ++ k)

/-- `Codec()`'s bytes of an `Out`: its kind (3 unknown, 2 a put's, 1 found, 0 not found), the
value. -/
def encOutB (o : Out) : List w8 :=
  (if o.Unknown' then W8 3 else if o.Put' then W8 2 else if o.Found' then W8 1 else W8 0) :: o.V'

open Classical in
/-- `Codec()`'s bytes of a value: a bounded `Out`'s, or nothing for any other value (never
encoded). -/
def encOutV (v : GoInterface) : List w8 :=
  if h : ∃ x : Out, v = interface.mkOk Out.ty #x ∧ x.V'.length + 9 < 2 ^ 63 then encOutB (Classical.choose h)
  else []

theorem encOutV_len (v : GoInterface) : (encOutV v).length < 2 ^ 63 := by
  unfold encOutV
  split
  · rename_i h
    have := (Classical.choose_spec h).2
    simp only [encOutB, List.length_cons]
    omega
  · simp

theorem encInB_len (i : KIn) : (encInB i.1).length < 2 ^ 63 := by
  rcases i with ⟨i, ⟨hok, hl⟩⟩
  cases i with
  | put k v =>
    simp only [inputOk] at hok
    simp only [valLen] at hl
    simp [encInB, u64le, hok.1, keyLen]; omega
  | get k =>
    simp only [inputOk] at hok
    simp [encInB, u64le, hok, keyLen]

end vals

/-! ## The store's step is `kv`'s -/

theorem kv_step_kvB (i : KIn) (σ σ' : KSt) (o : KvOutput GoString)
    (h : (kv GoString GoString).step σ i.1 σ' o) :
    σ' = (kvB.step i σ).1 ∧ clampO o = (kvB.step i σ).2 := by
  rcases i with ⟨i, hi⟩
  cases i with
  | get k =>
    obtain ⟨rfl, rfl⟩ := h
    simp [kvB]
  | put k v =>
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, by simp [kvB]⟩
    simp only [kvB]
    funext k'
    simp [upd]

/-! ## The far side's store -/

section base
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

/-- **The far side's store**: Rabia's key-value map (see the file header). -/
def kvR (γ : Names) : RBase GF KSt KIn KIn KOut where
  B := kvB
  sysState σ := kvState γ.rab σ
  Eop := rabiaE
  iv i := inV i.1
  ov o := outV o.1
  unk _ := unkV
  encIn i := encInB i.1
  encOut := encOutV
  reads_stay i st h := by
    rcases i with ⟨i, hi⟩
    cases i with
    | get k => simp [kvB]
    | put k v => simp [kvB] at h
  encIn_len i := encInB_len i
  encOut_len v := encOutV_len v

instance kvR_timeless (γ : Names) (σ : KSt) : Timeless ((kvR (GF := GF) γ).sysState σ) := by
  unfold kvR kvState kvHalf; simp only; infer_instance

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The store's linearization point is the client's update** (its postcondition read on the
bounded output). -/
theorem lin_opAU [NetProtoGS] [RemoteGS] (γ : Names) (i : KIn) (Φ : KOut → IProp GF) :
    lin (Gg := Gg) (kvR γ) i Φ ⊢ opAU (G := Gg) γ.rab i.1 (fun _ _ o => Φ (clampO o)) := by
  unfold lin opAU
  simp only [kvR]
  iintro Hlin
  have hE : (⊤ \ rabiaE : CoPset) = cliE := rfl
  rw [hE]
  imod Hlin with ⟨%st, Hst, Hcl⟩
  imodintro
  iexists st
  iframe Hst
  iintro %σ' %o ⟨Hst, %hstep⟩
  obtain ⟨rfl, ho⟩ := kv_step_kvB i st σ' o hstep
  rw [ho]
  iapply Hcl $$ Hst

/-- A slot's update gives the client's update (a write's `lin`, a read's `□ lin`). -/
theorem slotUpd_opAU [NetProtoGS] [RemoteGS] (γ : Names) (i : KIn) (Φ : KOut → IProp GF) :
    slotUpd (Gg := Gg) (kvR γ) i Φ ⊢ opAU (G := Gg) γ.rab i.1 (fun _ _ o => Φ (clampO o)) := by
  unfold slotUpd
  split
  · exact lin_opAU γ i Φ
  · iintro #H
    iapply lin_opAU γ i Φ $$ H

end base

/-! ## porcupine's model -/

section model
variable [GooseExts] [GoGlobalContext]

open Classical in
/-- porcupine's operations as the store's: a boxed input and a boxed answer; anything else
decodes to nothing. -/
def kvDec (io : OpV) : Option (KIn × linkv.Ans KOut) :=
  if h : ∃ (i : KIn) (a : linkv.Ans KOut), io = (inV i.1, ansV a) then
    some (Classical.choose h, Classical.choose (Classical.choose_spec h))
  else none

/-- **The store's porcupine model**, as the pending library's invariant sees it (its sequential
model only, made at the start): `pSeq kvB` through `kvDec`. -/
def kvS0 {GF : BundledGFunctors} : ModelSpec GF (linkv.PSet KSt KIn) where
  M := linkv.pM kvB kvDec
  rep _ _ _ := iprop(True)
  ioOk i o := iprop(⌜(∃ x : KIn, i = inV x.1) ∧ ∃ a : linkv.Ans KOut, o = ansV a⌝)
  ioOk_pers _ _ := by infer_instance

end model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- One entry: its key and value, its old and new pending values (read-only). -/
def entRep (ev : Entry) (e : EntV) : IProp GF :=
  iprop(⌜ev.K' = e.k ∧ ev.Cur' = e.cur⌝ ∗ ev.Old' ↦*□ e.old ∗ ev.Pend' ↦*□ e.new)

instance entRep_persistent (ev : Entry) (e : EntV) : Persistent (entRep (GF := GF) ev e) := by
  unfold entRep; infer_instance

/-- The entries `evs` (read-only) hold `es`: the same keys and values, the slices holding the
pending values. -/
def entsRep (evs : List Entry) (es : List EntV) : IProp GF :=
  iprop(⌜evs.map (·.K') = es.map (·.k) ∧ evs.map (·.Cur') = es.map (·.cur)⌝ ∗
    [∗list] p ∈ evs.zip es, p.1.Old' ↦*□ p.2.old ∗ p.1.Pend' ↦*□ p.2.new)

instance entsRep_persistent (evs : List Entry) (es : List EntV) :
    Persistent (entsRep (GF := GF) evs es) := by
  unfold entsRep; infer_instance

/-- A model value of index `n`: the boxed `State{esl}`, its entries read-only, holding `es` (well
formed, of size at most `n`, standing for a non-empty set); its set is `kvSet es`. -/
def kvRep (n : Nat) (v : GoInterface) (s : linkv.PSet KSt KIn) : IProp GF :=
  iprop(∃ (esl : GoSlice) (es : List EntV) (evs : List Entry),
    ⌜v = interface.mkOk State.ty #(State.mk esl) ∧ s = kvSet es ∧ WF es ∧ EB n es ∧
      ∃ c, kvSet es c⌝ ∗ esl ↦*□ evs ∗ entsRep evs es)

instance kvRep_persistent (n : Nat) (v : GoInterface) (s : linkv.PSet KSt KIn) :
    Persistent (kvRep (GF := GF) n v s) := by
  unfold kvRep; infer_instance

/-- **The store's porcupine model** (pending puts): `pSeq kvB` through `kvDec`. -/
def kvS : ModelSpec GF (linkv.PSet KSt KIn) where
  M := (kvS0 (GF := GF)).M
  rep n v s := kvRep n v s
  ioOk := (kvS0 (GF := GF)).ioOk
  ioOk_pers := (kvS0 (GF := GF)).ioOk_pers

end spec

/-! ## The specs -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : rabia.examples.rabianet.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

local notation "kpkg" => pkg_id.rabia.examples.rabianet

/-- `Model()`: the key-value map's porcupine model. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! rabia.examples.rabianet.Model)) (Val #()))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m; isModel (kvS (GF := GF)) m }}

/-- `Codec()`: the key-value map's codec. -/
abbrev Codec.spec : Prop :=
  ∀ γ : Names,
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! rabia.examples.rabianet.Codec)) (Val #()))
  {{ (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec), RET #cd;
      codecOk (kvR (Gg := hG.goose_globalGS) γ) cd }}

/-- `gens()`: a generator of inputs of the store. -/
abbrev gens.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! rabia.examples.rabianet.gens)) (Val #()))
  {{ (g : GoFunc), RET #g;
      EtcdGrove.lintest.genSpec (GF := GF) g (fun x => iprop(∃ i : KIn, ⌜x = inV i.1⌝)) }}

end specs

end rabia.examples.rabianet
end Perennial
