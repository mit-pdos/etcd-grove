/-
# The QuePaxa kit on `examples/lib/remote` (notes/dsv-quepaxa.md): vocabulary and specs

* **The store** `qB` (`Pure/QIn.lean`): linkv's pending-writes store of the key-value map `kvB` on
  the inputs the kit makes, `QIn` (`qInOk`: `inputOk`, short), and the outputs its codec encodes,
  `QOut` (`qOutOk`; remote's `Check` asks the codec to be injective on outputs within `2^63`
  bytes, so the outputs are bounded: `kvB`'s answers clamped, `outB`, which changes nothing on the
  short stores the kit's inputs make). A put is a write, a get a read.
* **The far side's store** `qR γ` (`remote.RBase`): the map's state is QuePaxa's abstract state
  (`ownState γ`, half of the SMR invariant's puts), the mask of the update is `raxosN` (QuePaxa's
  invariants), the Go values are the kit's boxed `In`/`Out`, the bytes `Codec()`'s (`EncIn`,
  `EncOut`). Its linearization point is QuePaxa's request update, its answer clamped: `lin_opAU`
  (definitional).
* **The start's shares** (`orchRes`, `clientRes`, `serverRes`, over `sharedRes`): what the
  orchestrator, client machine `c` and server machine `k` get of QuePaxa's ghost state.
* **The specs** of the kit's functions (`kit.go`): `Codec`, `Gen` (remote's codec and generator),
  `Orch` (`New`'s configuration, then `remote.Check` against `Model()`), `Client` (client
  machine `c`: its QuePaxa client, then `remote.ServeClient`), `Server` (server machine `k`: the
  configuration, then replica `k` if it is one).
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.Model
public import Dsverify.Proof.raxos.ReplicaDefs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure

/-! ## The kit's inputs -/

instance QIn.countable : Pos.Countable QIn :=
  .ofInjective (fun x : QIn => Pos.Countable.encode x.1)
    (fun a b h => Subtype.ext (Pos.encode_inj h))

instance QOut.countable : Pos.Countable QOut :=
  .ofInjective (fun x : QOut => Pos.Countable.encode x.1)
    (fun a b h => Subtype.ext (Pos.encode_inj h))

/-- `QIn`'s `BEq` is its decidable equality's (the instance linkv's pending lists erase with). -/
@[reducible] instance (priority := high) QIn.beq : BEq QIn := instBEqOfDecidableEq

/-! ## The codec's bytes -/

/-- A boolean's byte (`flag`). -/
def flagB (x : Bool) : w8 := if x then W8 1 else W8 0

/-- `appendStr`'s bytes of `s`: its length (8 bytes, little-endian), then its bytes. -/
def strB (s : GoString) : List w8 := u64Le (W64 s.length) ++ s

/-- `EncIn`'s bytes of an input: `Put`'s byte, then `K` and `V` (`appendStr`). -/
def encInB (i : KIn) : List w8 := flagB i.put :: (strB i.k ++ strB i.v)

theorem encInB_length (i : KIn) : (encInB i).length = 17 + i.k.length + i.v.length := by
  simp [encInB, strB, u64Le_length]; omega

/-- `EncOut`'s bytes of an output `Out{u, f, w}`: `Unknown`'s and `Found`'s bytes, then `V`'s. -/
def encOutB (u f : Bool) (w : GoString) : List w8 := flagB u :: flagB f :: w

section vals
variable [GooseExts] [GoGlobalContext]

/-- An input as the kit's boxed `In`. -/
abbrev qiv (i : QIn) : GoInterface := inV (In.mk i.1.put i.1.k i.1.v)

/-- An output as the kit's boxed `Out` (a known outcome). -/
abbrev qov (o : QOut) : GoInterface := outV (Out.mk false o.1.found o.1.v)

/-- The unknown output. -/
abbrev qunk : GoInterface := outV (Out.mk true false [])

open Classical in
/-- `Codec()`'s bytes of a value: a boxed `Out`'s (if they fit a slice), or nothing for any other
value (never encoded). -/
def encOutV (v : GoInterface) : List w8 :=
  if h : ∃ p : Bool × Bool × GoString, v = outV (Out.mk p.1 p.2.1 p.2.2) ∧
      (encOutB p.1 p.2.1 p.2.2).length < 2 ^ 63 then
    encOutB (Classical.choose h).1 (Classical.choose h).2.1 (Classical.choose h).2.2
  else []

theorem encOutV_len (v : GoInterface) : (encOutV v).length < 2 ^ 63 := by
  unfold encOutV
  split
  · rename_i h; exact (Classical.choose_spec h).2
  · simp

end vals

/-! ## The far side's store -/

section base
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

/-- **The far side's store**: QuePaxa's key-value map on the kit's inputs (see the file header). -/
def qR (γ : QNames) : RBase GF raxos.pure.Store QIn QOut where
  B := qB
  sysState σ := ownState γ σ
  Eop := ↑raxosN
  iv := qiv
  ov := qov
  unk _ := qunk
  encIn i := encInB i.1
  encOut := encOutV
  reads_stay i st h := by
    simp only [qB, outB, subB, kvB] at h ⊢
    rw [if_neg (by simpa using h)]
  encIn_len i := by
    have := i.2.2
    rw [encInB_length]
    omega
  encOut_len := encOutV_len

instance qR_timeless (γ : QNames) (σ : raxos.pure.Store) : Timeless ((qR (GF := GF) γ).sysState σ) := by
  unfold qR; simp only; infer_instance

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The store's linearization point is QuePaxa's request update** (definitionally), its answer
clamped into `QOut` (`clampO`: the answer itself for every answer the codec encodes). -/
theorem lin_opAU [NetProtoGS] [RemoteGS] (γ : QNames) (i : QIn) (Φ : QOut → IProp GF) :
    lin (Gg := Gg) (qR γ) i Φ ⊣⊢ opAU γ i.1 (fun o => Φ (clampO qOut0 o)) := .rfl

end base

/-! ## The start's shares -/

section shares
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]
variable [π : NetProtoGS] [qv : hyp.QpVocab GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The facts every machine shares (persistent): QuePaxa's invariants, the protocols, the
genesis batch's registration, the slots' bound's start. -/
def sharedRes (γ : QNames) : IProp GF :=
  iprop(inv consN (consInv γ) ∗ inv smrN (smrInv γ) ∗ netProtos γ ∗
    batchReg γ go!"nil" nilBatch ∗ spentLb γ 0)

instance sharedRes_persistent (γ : QNames) : Persistent (sharedRes (GF := GF) γ) := by
  unfold sharedRes spentLb; infer_instance

/-- The orchestrator's share: the configuration's choice, the shared facts. -/
def orchRes (γ : QNames) : IProp GF := iprop(confTok γ ∗ sharedRes γ)

/-- Client `c`'s tickets: one per replica `k` (1..5) and request `j` (< 20). -/
def ticketsOf (c : Nat) : List Ticket :=
  serverIds.flatMap (fun k => (List.range 20).map (fun j => (k, c, j)))

/-- Client machine `c`'s share: its request counter's half (at 0; the other half is `smrInv`'s),
its tickets, the shared facts. -/
def clientRes (γ : QNames) (c : Nat) : IProp GF :=
  iprop(ghostMapElem γ.cnt c (DFrac.own (1 : Qp).half) (0 : Nat) ∗
    ([∗list] t ∈ ticketsOf c, ticketTok γ t) ∗ sharedRes γ)

/-- Server machine `k`'s share (replica `k`'s, if the configuration has it): its proxy's network
token, its recorder's half (no slot yet), its proxy's init frontier (1), the shared facts
(`replicaRes` once the configuration is known). -/
def serverRes (γ : QNames) (k : Nat) : IProp GF :=
  iprop(netTok γ k ∗ recHalf γ k ∅ ∗ initFront γ k 1 ∗ sharedRes γ)

end shares

/-! ## The deployment -/

/-- The client machines' request addresses (`ClientAddrs()`), for the orchestrator's calls. -/
def clientAddrs : List GoString :=
  [go!"127.0.0.1:7661", go!"127.0.0.1:7662", go!"127.0.0.1:7663", go!"127.0.0.1:7664",
    go!"127.0.0.1:7665", go!"127.0.0.1:7666"]

/-! ## The specs -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

/-- `Codec()`: the map's codec. -/
abbrev Codec.spec : Prop :=
  ∀ γ : QNames,
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! raxos.examples.quepaxanet.Codec)) (Val #()))
  {{ (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec), RET #cd;
      codecOk (qR (Gg := hG.goose_globalGS) γ) cd }}

/-- `Gens()`: remote's generator, each call an input the kit makes. -/
abbrev Gens.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! raxos.examples.quepaxanet.Gens)) (Val #()))
  {{ (gen : GoFunc), RET #gen;
      EtcdGrove.lintest.genSpec (GF := GF) gen (fun x => iprop(∃ i : QIn, ⌜x = qiv i⌝)) }}

/-- `Orch()`: the orchestrator; it returns (porcupine accepts the history). -/
abbrev Orch.spec : Prop :=
  ∀ (γ : QNames) (γp : PendNames), receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ orchRes (Gg := hG.goose_globalGS) γ ∗
      ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (qR γ) a) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := QIn) ∗
      pendCtx (Gg := hG.goose_globalGS) (qR γ) (qS0 (GF := GF)) γp ∗
      pendLib (Gg := hG.goose_globalGS) (qS0 (GF := GF)) γp (qS0 (GF := GF)).M.init ∗
      [∗list] a ∈ clientAddrs, budUnits (Gg := hG.goose_globalGS) a 60 }}
    (App (Val (@! raxos.examples.quepaxanet.Orch)) (Val #()))
  {{ RET #(); True }}

/-- `Client(c)`: client machine `c`; it never returns. -/
abbrev Client.spec : Prop :=
  ∀ (γ : QNames) (c : w64), uint.nat c < 6 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ clientRes (Gg := hG.goose_globalGS) γ (uint.nat c) ∗
      remoteAddr (Gg := hG.goose_globalGS) (qR γ) (clientAddrs.getD (uint.nat c) []) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := QIn) }}
    (App (Val (@! raxos.examples.quepaxanet.Client)) (Val #c))
  {{ RET #(); False }}

/-- `Server(k)`: server machine `k` (`1 ≤ k ≤ 5`); it never returns. -/
abbrev Server.spec : Prop :=
  ∀ (γ : QNames) (k : w64), 1 ≤ uint.nat k ∧ uint.nat k ≤ 5 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ serverRes (Gg := hG.goose_globalGS) γ (uint.nat k) }}
    (App (Val (@! raxos.examples.quepaxanet.Server)) (Val #k))
  {{ RET #(); False }}

end specs

end raxos.examples.quepaxanet
end Perennial
