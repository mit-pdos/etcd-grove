/-
# The EPaxos kit on `examples/lib/remote` (notes/dsv-epaxos.md): vocabulary and specs

* **The far side's store** `epR γ` (`remote.RBase`) over `ModelSet.lean`'s `epB` (the key-value
  store with scans and pending puts, on `Gen`'s inputs `EIn`, its output an answer's bytes
  `BStr`): its state is the replicas' abstract store (`own_state γ`, `Interface/Client.lean`), the
  mask of the update is `epEop`, the Go values are `KitVals.lean`'s (`inOf`, `Out{V}`, `outUnk`)
  and the bytes `Codec()`'s. Its linearization point is the replicas' update: `lin_opU`.
* **porcupine's model** `epS0`/`epS`: `pM epB epDec` (porcupine's operations decoded as the
  store's), with `Model()`'s state (a slice of `Config{Kv, Pend}`) standing for a set it brackets
  (`epRep`, `ModelSet.lean`'s `Sim`).
* **The specs** of `Model()`, `Codec()` and `Gen` (`ModelProof.lean`, `KitProof.lean`), and the
  client machines' addresses (`ClientAddrs()`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ModelSet
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs
public import Perennial.Proof.encoding.binary.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote
  github_com.imdea_software.swiftpaxos_epaxos github_com.imdea_software.swiftpaxos_epaxos.kvs

/-! ## Countable inputs and outputs -/

/-- An input as a countable value. -/
def kvICode : KvI → w64 ⊕ (w64 × List w8) ⊕ (w64 × w64)
  | .get k => .inl k
  | .put k v => .inr (.inl (k, v))
  | .scan k n => .inr (.inr (k, n))

instance EIn.countable : Pos.Countable EIn :=
  .ofInjective (fun x : EIn => Pos.Countable.encode (kvICode x.1)) (by
    intro a b h
    have h' := Pos.encode_inj h
    obtain ⟨a, ha⟩ := a; obtain ⟨b, hb⟩ := b
    apply Subtype.ext
    cases a <;> cases b <;> simp_all [kvICode])

instance BStr.countable : Pos.Countable BStr :=
  .ofInjective (fun x : BStr => Pos.Countable.encode x.1)
    (fun a b h => Subtype.ext (Pos.encode_inj h))

/-! ## Go values and bytes -/

section vals
variable [GooseExts] [GoGlobalContext]

/-- An input, boxed (`any` holding an `In`). -/
abbrev inV (x : In) : GoInterface := interface.mkOk In.ty #x

/-- An output, boxed (`any` holding an `Out`). -/
abbrev outV (u : Bool) (v : GoString) : GoInterface := interface.mkOk Out.ty #(Out.mk u v)

/-- The store's input `i` as kit.go's `In` (`inOf`), boxed. -/
def ivE (i : EIn) : GoInterface := inV (inE i)

/-- `Codec().EncIn`'s bytes of an `In`: its kind, `K` and `N` (8 bytes little-endian each), `V`. -/
def encInB (x : In) : List w8 := x.Op' :: (u64Le x.K' ++ u64Le x.N' ++ x.V')

/-- `Codec().EncOut`'s bytes of an `Out{u, v}`. -/
def encOutB (u : Bool) (v : GoString) : List w8 := (if u then W8 1 else W8 0) :: v

open Classical in
/-- `Codec().EncOut`'s bytes of a value: a bounded `Out`'s, or nothing for any other value (never
encoded). -/
def encOutV (v : GoInterface) : List w8 :=
  if h : ∃ p : Bool × BStr, v = outV p.1 p.2.1 then encOutB (choose h).1 (choose h).2.1 else []

theorem encInB_len (i : EIn) : (encInB (inE i)).length < 2 ^ 63 := by
  obtain ⟨k | ⟨k, v⟩ | ⟨k, n⟩, hi⟩ := i <;>
    simp only [inE, inOf, encInB, List.length_cons, List.length_append, u64Le_length,
      List.length_nil] <;> simp only [inPre] at hi <;> omega

end vals

/-! ## The far side's store -/

section base
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [π : NetProtoGS]

/-- **The far side's store**: the replicas' key-value store (see the file header). -/
def epR (γ : EpNames) : RBase GF KvS EIn BStr where
  B := epB
  sysState σ := own_state γ σ
  Eop := epEop
  iv := ivE
  ov o := outV false o.1
  unk _ := outV true []
  encIn i := encInB (inE i)
  encOut := encOutV
  reads_stay i st h := step_nput i h st
  encIn_len := encInB_len
  encOut_len v := by
    unfold encOutV
    split
    · rename_i h
      have := (Classical.choose h).2.2
      simp only [encOutB, List.length_cons]
      omega
    · simp

instance epR_timeless (γ : EpNames) (σ : KvS) : Timeless ((epR (GF := GF) γ).sysState σ) := by
  unfold epR; simp only; infer_instance

/-- An unknown outcome is `outUnk`. -/
theorem epR_unk (γ : EpNames) (i : EIn) :
    (epR (GF := GF) γ).unk i = interface.mkOk Out.ty #outUnk := rfl

/-- An answer `o` is `outOk` of any store output whose bytes are `o`'s. -/
theorem epR_ov (γ : EpNames) (o : KvO) (h : (outBytes o).length < 2 ^ 63 - 1) :
    (epR (GF := GF) γ).ov (bnd (outBytes o)) = interface.mkOk Out.ty #(outOk o) := by
  simp only [epR, bnd_of h, outOk]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The store's linearization point is the replicas' update** `opU` (for the caller's
postcondition read on the output's bytes, bounded). -/
theorem lin_opU [RemoteGS] (γ : EpNames) (i : EIn) (Φ : BStr → IProp GF) :
    lin (Gg := Gg) (epR γ) i Φ ⊢ opU γ i.1 (fun o => Φ (bnd (outBytes o))) := by
  unfold lin opU
  simp only [epR, epB]
  exact .rfl

end base

/-! ## porcupine's model -/

section model
variable [GooseExts] [GoGlobalContext]

open Classical in
/-- porcupine's operations as the store's: a boxed input and a boxed bounded `Out`, unknown (an
error) or not; anything else decodes to nothing. -/
def epDec (io : OpV) : Option (EIn × Ans BStr) :=
  if h : ∃ (i : EIn) (u : Bool) (w : BStr), io = (ivE i, outV u w.1) then
    some (choose h, ansOf (choose (choose_spec h)) (choose (choose_spec (choose_spec h))))
  else none

/-- **The store's porcupine model**, as the pending library's invariant sees it (its sequential
model only, as paxos's `woS0`). -/
def epS0 {GF : BundledGFunctors} : ModelSpec GF (PSet KvS EIn) where
  M := pM epB epDec
  rep _ _ _ := iprop(True)
  ioOk i o := iprop(⌜(∃ x : EIn, i = ivE x) ∧ ∃ (u : Bool) (w : BStr), o = outV u w.1⌝)
  ioOk_pers _ _ := by infer_instance

end model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A Go configuration `Config{Kv, Pend}` holding `g`: its slices read-only. -/
def cfgRep (x : Config) (g : GC) : IProp GF :=
  iprop(x.Kv' ↦*□ g.1 ∗ x.Pend' ↦*□ g.2.map inE)

instance cfgRep_persistent (x : Config) (g : GC) : Persistent (cfgRep (GF := GF) x g) := by
  unfold cfgRep; infer_instance

/-- Each pair's `Config` holds its configuration (persistent). -/
def cfgsRep (P : List (Config × GC)) : IProp GF :=
  iprop(□ ∀ p, ⌜p ∈ P⌝ → cfgRep p.1 p.2)

instance cfgsRep_persistent (P : List (Config × GC)) : Persistent (cfgsRep (GF := GF) P) := by
  unfold cfgsRep; infer_instance

/-- The configurations' bounds after `k` steps (a step adds at most two entries, one pending
put). -/
def lenOk (k : Nat) (G : List GC) : Prop := ∀ g ∈ G, g.1.length ≤ 2 * k ∧ g.2.length ≤ k

/-- A model value: the boxed `State` slice, read-only, of `Config`s holding `G` (`P` pairs them);
`G` brackets the set `s` (`Sim`). -/
def epRep (k : Nat) (v : GoInterface) (s : PSet KvS EIn) : IProp GF :=
  iprop(∃ (sl : GoSlice) (P : List (Config × GC)),
    ⌜v = interface.mkOk State.ty #sl ∧ Sim (P.map Prod.snd) s ∧ lenOk k (P.map Prod.snd)⌝ ∗
    sl ↦*□ P.map Prod.fst ∗ cfgsRep P)

/-- **The store's porcupine model**: `pM epB epDec`, over `Model()`'s values. -/
def epS : ModelSpec GF (PSet KvS EIn) where
  M := (epS0 (GF := GF)).M
  rep k v s := epRep k v s
  ioOk := (epS0 (GF := GF)).ioOk
  ioOk_pers := (epS0 (GF := GF)).ioOk_pers

end spec

/-! ## The deployment -/

/-- The client machines' addresses (`ClientAddrs()`), for the orchestrator's calls. -/
def clientAddrs : List GoString :=
  [go!"127.0.0.1:7511", go!"127.0.0.1:7512", go!"127.0.0.1:7513", go!"127.0.0.1:7514",
   go!"127.0.0.1:7515", go!"127.0.0.1:7516", go!"127.0.0.1:7517", go!"127.0.0.1:7518",
   go!"127.0.0.1:7519", go!"127.0.0.1:7520"]

/-! ## The specs -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Assumptions]
variable [π : NetProtoGS]

local notation "kpkg" => pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

/-- `Model()`: the store's porcupine model. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Model)) (Val #()))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m; isModel (epS (GF := GF)) m }}

/-- `Codec()`: the store's codec. -/
abbrev Codec.spec : Prop :=
  ∀ γ : EpNames,
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Codec)) (Val #()))
  {{ (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec), RET #cd;
      codecOk (epR (Gg := hG.goose_globalGS) γ) cd }}

/-- `Gen`: client `c`'s input, one of the store's (`Gen`'s bounds, `inPre`). -/
abbrev Gen.spec : Prop :=
  ⊢ EtcdGrove.lintest.genSpec (GF := GF)
      (functions github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Gen [])
      (fun x => iprop(∃ i : EIn, ⌜x = ivE i⌝))

end specs

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial
