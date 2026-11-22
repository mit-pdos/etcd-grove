/-
# The paxos kit on `examples/lib/remote` (notes/dsv-paxos.md): vocabulary and specs

* **The register** `woB`: linkv's pending-writes store (`linkv.PendSpec`) of the write-once register,
  on bounded strings (`BStr`: an input is a proposal's value, `Propose`'s premise
  `len < 2^48`): a proposal of `i` at state `σ` decides `σ.getD i` and answers it. Every proposal is
  a write (one of unknown outcome is pending: it may take effect later, once, or never).
* **The far side's store** `woR Γ` (`remote.RBase`): the register's state is the paxos invariant's
  other half (`own_state Γ`), the mask of the update is `paxosEop` (the paxos invariant and the
  clients' slots), the Go values and bytes are `Codec()`'s. Its linearization point is the paxos
  client's update: `lin_opAU`.
* **The specs** of the kit's functions (`kit.go`): `Client` (client machine `c`: its paxos node and
  `remote.ServeClient`), `Orch` (`remote.Check`), `Server` (`paxos.RunServer`), and the codec, model
  and generator `Orch` and `Client` pass to remote.
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.Base
public import Dsverify.Proof.github_com.xiang90.paxos.Deploy
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.xiang90.paxos.examples.paxosnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

/-! ## The register -/

/-- A bounded string: the register's inputs and outputs. -/
abbrev BStr := {s : GoString // (s.length : Int) < 2 ^ 48}

/-- `w` as a bounded string, or `i` if it is not one. -/
instance BStr.countable : Pos.Countable BStr :=
  .ofInjective (fun x : BStr => Pos.Countable.encode x.1)
    (fun a b h => Subtype.ext (Pos.encode_inj h))

def bnd (w : GoString) (i : BStr) : BStr := if h : (w.length : Int) < 2 ^ 48 then ⟨w, h⟩ else i

theorem bnd_of {w : GoString} (h : (w.length : Int) < 2 ^ 48) (i : BStr) : bnd w i = ⟨w, h⟩ := by
  unfold bnd; rw [dif_pos h]

/-- The write-once register with failed proposals (linkv's pending-writes store). -/
def woB : linkv.PendSpec (Option GoString) BStr BStr where
  init := none
  step i σ := (some (σ.getD i.1), bnd (σ.getD i.1) i)
  isWrite _ := true

theorem woStep_eq (v : GoString) (σ : Option GoString) :
    woStep v σ = (some (σ.getD v), σ.getD v) := by
  cases σ <;> rfl

section vals
variable [GooseExts] [GoGlobalContext]

/-- An input, boxed (`any` holding a `string`). -/
abbrev strV (s : GoString) : GoInterface := interface.mkOk go.string #s

/-- An output, boxed (`any` holding an `Out`). -/
abbrev outV (u : Bool) (v : GoString) : GoInterface := interface.mkOk Out.ty #(Out.mk u v)

/-- `Codec()`'s bytes of an output `Out{u, v}`. -/
def encOutB (u : Bool) (v : GoString) : List w8 := (if u then W8 1 else W8 0) :: v

open Classical in
/-- `Codec()`'s bytes of a value: a bounded `Out`'s, or nothing for any other value (never
encoded). -/
def encOutV (v : GoInterface) : List w8 :=
  if h : ∃ p : Bool × BStr, v = outV p.1 p.2.1 then encOutB (choose h).1 (choose h).2.1 else []

end vals

/-! ## The far side's store -/

section base
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

/-- **The far side's store**: the paxos register (see the file header). -/
def woR (Γ : Names) : RBase GF (Option GoString) BStr BStr where
  B := woB
  sysState σ := own_state Γ σ
  Eop := paxosEop
  iv i := strV i.1
  ov o := outV false o.1
  unk _ := outV true []
  encIn i := i.1
  encOut := encOutV
  reads_stay i st h := by simp [woB] at h
  encIn_len i := by have := i.2; omega
  encOut_len v := by
    unfold encOutV
    split
    · rename_i h
      have := (Classical.choose h).2.2
      simp only [encOutB, List.length_cons]
      omega
    · simp

instance woR_timeless (Γ : Names) (σ : Option GoString) :
    Timeless ((woR (GF := GF) Γ).sysState σ) := by
  unfold woR; simp only; infer_instance

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The register's linearization point is the paxos client's update** (for the caller's
postcondition read on the bounded output). -/
theorem lin_opAU [NetProtoGS] [RemoteGS] (Γ : Names) (i : BStr) (Φ : BStr → IProp GF) :
    lin (Gg := Gg) (woR Γ) i Φ ⊢ opAU Γ i.1 (fun w => Φ (bnd w i)) := by
  unfold lin opAU
  simp only [woR, woB, woStep_eq]
  exact .rfl

end base

/-! ## porcupine's model -/

section model
variable [GooseExts] [GoGlobalContext]

/-- The configurations the model's `State{kn, val, pend}` stands for: without a known value,
nothing decided and `pend` all pending, or some `x` of `pend` decided and some of the others
pending; with `val` known, `val` decided and some of `pend` pending. -/
def woSet (kn : Bool) (val : GoString) (pend : List BStr) : linkv.PSet (Option GoString) BStr :=
  fun c => if kn then c.st = some val ∧ c.pend.Subperm pend
    else (c.st = none ∧ c.pend.Perm pend) ∨
      ∃ x ∈ pend, c.st = some x.1 ∧ c.pend.Subperm (pend.erase x)

open Classical in
/-- porcupine's operations as the register's: a boxed bounded `string` and a boxed bounded `Out`,
unknown (`err`) or not (`ok v`); anything else decodes to nothing. -/
def woDec (io : OpV) : Option (BStr × linkv.Ans BStr) :=
  if h : ∃ (i : BStr) (u : Bool) (w : BStr), io = (strV i.1, outV u w.1) then
    let i := choose h
    let u := choose (choose_spec h)
    let w := choose (choose_spec (choose_spec h))
    some (i, if u then .err else .ok w)
  else none

end model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A model value: the boxed `State{kn, val, sl}` with `sl` read-only, holding `pend`'s strings;
its set is `woSet kn val pend`; `pend` has at most `k` entries (a step adds at most one). -/
def woRep (k : Nat) (v : GoInterface) (s : linkv.PSet (Option GoString) BStr) : IProp GF :=
  iprop(∃ (kn : Bool) (val : GoString) (sl : GoSlice) (pend : List BStr),
    ⌜v = interface.mkOk State.ty #(State.mk kn val sl) ∧ s = woSet kn val pend ∧
      pend.length ≤ k⌝ ∗ sl ↦*□ pend.map Subtype.val)

/-- **The register's porcupine model** (pending proposals): `pSeq woB` through `woDec`. -/
def woS : ModelSpec GF (linkv.PSet (Option GoString) BStr) where
  M := linkv.pM woB woDec
  rep k v s := woRep k v s
  ioOk i o := iprop(⌜(∃ x : BStr, i = strV x.1) ∧ ∃ (u : Bool) (w : BStr), o = outV u w.1⌝)
  ioOk_pers _ _ := by infer_instance

end spec

/-! ## The deployment -/

/-- The client machines' addresses (`ClientAddrs()`), for the orchestrator's calls. -/
def clientAddrs : List GoString :=
  [go!"127.0.0.1:7411", go!"127.0.0.1:7412", go!"127.0.0.1:7413", go!"127.0.0.1:7414"]

/-! ## The specs -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.xiang90.paxos.examples.paxosnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

local notation "kpkg" => pkg_id.github_com.xiang90.paxos.examples.paxosnet

/-- `Model()`: the register's porcupine model. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! github_com.xiang90.paxos.examples.paxosnet.Model)) (Val #()))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m; isModel (woS (GF := GF)) m }}

/-- `Codec()`: the register's codec. -/
abbrev Codec.spec : Prop :=
  ∀ Γ : Names,
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! github_com.xiang90.paxos.examples.paxosnet.Codec)) (Val #()))
  {{ (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec), RET #cd; codecOk (woR (Gg := hG.goose_globalGS) Γ) cd }}

/-- `Gen`: client `c`'s input, a bounded string. -/
abbrev Gen.spec : Prop :=
  ⊢ EtcdGrove.lintest.genSpec (GF := GF)
      (functions github_com.xiang90.paxos.examples.paxosnet.Gen [])
      (fun x => iprop(∃ i : BStr, ⌜x = strV i.1⌝))

/-- `Orch()`: the orchestrator; it returns (porcupine accepts the history). -/
abbrev Orch.spec : Prop :=
  ∀ (Γ : Names) (γp : PendNames), receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗
      ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (woR Γ) a) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := BStr) ∗
      pendCtx (Gg := hG.goose_globalGS) (woR Γ) (woS (GF := GF)) γp ∗
      pendLib (Gg := hG.goose_globalGS) (woS (GF := GF)) γp (woS (GF := GF)).M.init }}
    (App (Val (@! github_com.xiang90.paxos.examples.paxosnet.Orch)) (Val #()))
  {{ RET #(); True }}

/-- `Client(c)`: client machine `c`; it never returns. -/
abbrev Client.spec : Prop :=
  ∀ (Γ : Names) (c : w64), uint.nat c < 4 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ isPaxos Γ ∗ allProtos Γ ∗ clientTok Γ c ∗
      remoteAddr (Gg := hG.goose_globalGS) (woR Γ) (clientAddrs.getD (uint.nat c) []) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := BStr) }}
    (App (Val (@! github_com.xiang90.paxos.examples.paxosnet.Client)) (Val #c))
  {{ RET #(); False }}

/-- `Server(id)`: server machine `id` (an acceptor, `id ≤ 3`, or a learner); it never returns. -/
abbrev Server.spec : Prop :=
  ∀ (Γ : Names) (id : w64), 1 ≤ uint.nat id ∧ uint.nat id ≤ 5 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ isPaxos Γ ∗ allProtos Γ ∗
      (if uint.nat id ≤ 3 then stOwn Γ id AccState.init else True) }}
    (App (Val (@! github_com.xiang90.paxos.examples.paxosnet.Server)) (Val #id))
  {{ RET #(); False }}

end specs

end github_com.xiang90.paxos.examples.paxosnet
end Perennial
