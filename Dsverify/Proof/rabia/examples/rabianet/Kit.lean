/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/examples/rabianet/Spec.lean`, run
`rabia-r1wake-1`, onto this kit's Go (`kit.go`, on `examples/lib/remote`) and `Net/`.)

The rabia kit's shared definitions and the specs of its configuration protocol and client side
(`ConfProof.lean`, `ClientProof.lean`; the porcupine model, codec and generator are
`KitModel.lean`'s):

* **The configuration** (`confV cf`, the Go `Conf` of a configuration): the orchestrator's `New`
  chooses one (`choose`), records it (`setCfg`, from `orchCore`'s key set) and sends it to the six
  client machines' and servers `1..n`'s configuration addresses (`send`, `sendConf`: `cfgP`);
  `waitConf` (`awaitConf` in a routine of its own, answering every configuration it reads) returns
  the recorded one (`cfgIs`). `configure` sets Rabia's `config.Conf` from `Conf`'s points-to,
  which a machine claims once with its package state (`Core/PkgState.lean`'s `confClaim`).
* **A client machine's system** `is_sys γ c l` (persistent): the `*Sys` at `l`, its endpoint `t`
  with client `c`'s channels, the shared state, the recorded configuration and `Conf` configured at
  it, and the mutex `mu` that guards the endpoint's mutable state (`clientAt`: the next sequence
  number, the send channel's producer token, client `c`'s key set). The lab kept that state in an
  invariant opened by the harness's exclusive client token; remote's `ServeClient` handed its
  `newClient` nothing (a triple with precondition `True`; now a one-shot WP, which could take
  exclusive state), so the kit's `Op` locks `mu` (notes/dsv-rabia.md).
* `Op` (`op1` under the lock): a sequence number below the budget `SeqBudget = opBudget`
  registers the request with the caller's update `opAU` and sends it; the reply with that number
  answers the update's output (`kvOutV`); a timeout, or a sequence number past the budget, answers
  `Out{Unknown: true}`.
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.GhostAux
public import Dsverify.Proof.rabia.examples.rabianet.Base
public import Dsverify.Proof.rabia.internal.tcp.Spec
public import Dsverify.Proof.rabia.internal.config.Spec
public import Dsverify.Proof.rabia.Core.PkgState
public import Dsverify.GeneratedProof.rabia.examples.rabianet
public import Perennial.Proof.sync.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.examples.rabianet

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.tcp rabia

/-- The kit's `Conf` value of a configuration. -/
def confV [GooseExts] (cf : RCfg) : _root_.Perennial.rabia.examples.rabianet.Conf :=
  ⟨W64 cf.n, W64 cf.f, W64 cf.batch, W64 cf.bms, W64 cf.blocks⟩

instance Conf.countable [GooseExts] : Pos.Countable _root_.Perennial.rabia.examples.rabianet.Conf :=
  countableOfLeftInverse (B := w64 × w64 × w64 × w64 × w64)
    (fun c => (c.N', c.F', c.Batch', c.BatchMs', c.Blocks'))
    (fun (a, b, c, d, e) => ⟨a, b, c, d, e⟩)
    (fun _ => rfl)

/-- An input as the kit's Go `In`. -/
def kvInV [GooseExts] : KvInput GoString GoString → In
  | .put k v => ⟨true, k, v⟩
  | .get k => ⟨false, k, []⟩

/-- An output as the kit's Go `Out` (a found value is never empty: puts' values are not). -/
def kvOutV [GooseExts] : KvOutput GoString → Out
  | .done => ⟨false, true, false, []⟩
  | .got none => ⟨false, false, false, []⟩
  | .got (some v) => ⟨false, false, true, v⟩

/-- The unknown output. -/
def unkOutV [GooseExts] : Out := ⟨true, false, false, []⟩

/-- An output `Op` answers: a found value is not empty, and nine bytes more than it fit a Go
string's length (it is the reply string's tail past `"1" + key`). -/
def outOk : KvOutput GoString → Prop
  | .got (some v) => v ≠ [] ∧ v.length + 9 < 2 ^ 63
  | _ => True

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

/-- What `awaitConf` sends on its channel: the recorded configuration. -/
def confChanP (γ : Names) (v : _root_.Perennial.rabia.examples.rabianet.Conf) : IProp GF :=
  iprop(∃ cf : RCfg, ⌜v = confV cf⌝ ∗ cfgIs γ.rab cf)

/-- Client `c`'s endpoint state, `mu`'s lock invariant (the `*Sys` at `l`, the endpoint's channel
names `e`): the next sequence number `n` (within the budget), the send channel's producer token
(`n` requests sent), client `c`'s key set (its requests below `n`). -/
def clientAt (γ : Names) (c : Nat) (l : Loc) (e : ClNames) : IProp GF :=
  iprop(∃ (n : Nat) (sent : List Command) (K : List FKey),
    ⌜sent.length = n ∧ n ≤ opBudget ∧ ∀ m, FKey.reg (c, m) ∈ K → m < n⌝ ∗
    structFieldRef Sys go!"next" l ↦ (W32 n) ∗ spscProducer e.send sent ∗
    keysOf γ.rab (.cli c) K)

/-- Client machine `c`'s system (see the file header; persistent). -/
def is_sys (γ : Names) (c : Nat) (l : Loc) : IProp GF :=
  iprop(∃ (t mu : Loc) (e : ClNames) (cf : RCfg),
    structFieldRef Sys go!"t" l ↦□ t ∗ structFieldRef Sys go!"mu" l ↦□ mu ∗
    clientChans γ c e t ∗ shared γ ∗ cfgIs γ.rab cf ∗ confRO cf ∗
    sync.isMutex mu (clientAt γ c l e))

instance is_sys_persistent (γ : Names) (c : Nat) (l : Loc) :
    Persistent (is_sys (GF := GF) γ c l) := by
  unfold is_sys; infer_instance

end defs

/-! ## The specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.examples.rabianet.Assumptions]

local notation "kpkg" => pkg_id.rabia.examples.rabianet

/-- `configure(ps, conf)` in configuration `cf` (`ps` the first `n` network addresses), from
`Conf`'s points-to (a machine claims it once, `confClaim`): `Conf` configured at `cf`. -/
abbrev configure.spec : Prop :=
  ∀ (ps : GoSlice) (cf : RCfg),
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ ⌜cf.Ok⌝ ∗
        (globalAddr rabia.internal.config.Conf ↦ (zeroValDef : rabia.internal.config.Config)) ∗
        ps ↦*□ peerStrs cf }}
      (App (App (Val (@! rabia.examples.rabianet.configure)) (Val #ps)) (Val #(confV cf)))
    {{ RET #(); confRO cf }}

/-- `awaitConf(a, ch)` at a configuration address `a`: every configuration it sends on `ch` is
the recorded one. It never returns. -/
abbrev awaitConf.spec : Prop :=
  ∀ (γ : Names) (a : GoString) (ch : GoChan) (γch : ChanNames),
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ addrProto (Gg := hG.goose_globalGS) a (cfgP γ) cfgQ ∗
        isChanBag γch ch (confChanP γ) }}
      (App (App (Val (@! rabia.examples.rabianet.awaitConf)) (Val #a)) (Val #ch))
    {{ RET #(); False }}

/-- `waitConf(a)` at a configuration address `a`: the recorded configuration. -/
abbrev waitConf.spec : Prop :=
  ∀ (γ : Names) (a : GoString),
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ addrProto (Gg := hG.goose_globalGS) a (cfgP γ) cfgQ }}
      (App (Val (@! rabia.examples.rabianet.waitConf)) (Val #a))
    {{ (v : _root_.Perennial.rabia.examples.rabianet.Conf), RET #v;
        ∃ cf : RCfg, ⌜v = confV cf⌝ ∗ cfgIs γ.rab cf }}

/-- `New()` on the orchestrator, from the shared state and the orchestrator's key set: it records
a configuration and sends it to every client machine and to servers `1..n`. -/
abbrev New.spec : Prop :=
  ∀ (γ : Names),
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ shared γ ∗ keysOf γ.rab .orch [] }}
      (App (Val (@! rabia.examples.rabianet.New)) (Val #()))
    {{ RET #(); ∃ cf : RCfg, cfgIs γ.rab cf }}

/-- `newClient(c)` on client machine `c`, from its share and its package state (with which it
claims `Conf`): client `c`'s system. -/
abbrev newClient.spec : Prop :=
  ∀ (γ : Names) (c : Nat) (σ : GMap GoString Bool), c < nC →
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ cliCore γ c ∗
        ownGoState (hG := hG.goose_localGS.goose_go_stateGS) σ }}
      (App (Val (@! rabia.examples.rabianet.newClient)) (Val #(W64 c)))
    {{ (l : Loc), RET #l; is_sys γ c l }}

/-- `Op(x, c, in)`, client `c`'s operation on its system, with the caller's update `opAU` of an
input the workload makes: the update's output and its postcondition, or the unknown output (the
update then may or may not have been fired: the request may take effect later). -/
abbrev Op.spec : Prop :=
  ∀ (γ : Names) (c : Nat) (l : Loc) (i : KvInput GoString GoString) (Q : OpQ GF),
    c < nC → inputOk i →
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ is_sys γ c l ∗ opAU γ.rab i Q }}
      (App (App (App (Val (@! rabia.examples.rabianet.Op)) (Val #l)) (Val #(W64 c)))
        (Val #(kvInV i)))
    {{ (o : Out), RET #o; ⌜o = unkOutV⌝ ∨
        ∃ σ σ' out, ⌜o = kvOutV out ∧ (kv GoString GoString).step σ i σ' out ∧ outOk out⌝ ∗
          Q σ σ' out }}

end spec

end Perennial.rabia.examples.rabianet
