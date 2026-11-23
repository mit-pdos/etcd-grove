/-
# The gryff kit's specs (`kit.go`; notes/dsv-gryff.md), dsv-paxos's `Kit.lean` pattern

* `Codec()` meets `codecOk (casR γ)` (`Codec.spec`); `Gen(c, j)` returns an `In` (`Gen.spec`).
* `Orch()`: remote's `Check` of the clients' operations against the register's porcupine model
  `casS` (`Orch.spec`; it returns: porcupine accepts the history).
* `op(sys, x)` (`op.spec`): client `c`'s operation under its lock, given remote's update of the
  input (`slotUpd (casR γ.proto)`: a write's one-shot `lin`, a read's `□ lin`), answers an
  output with `Φ` of it, or the unknown output `Out{Unknown: true}`; `Op` is it under `Sys.mu`.
* `Client(c)` (`Client.spec`): client machine `c`'s `*Sys`, made once from its start resources
  (`clientStartRes γ c`), served by remote's `ServeClient` with the persistent token `sysTok`; it
  never returns.
-/
module

public import Dsverify.Proof.gryff.examples.gryffnet.Kit
public import Dsverify.Proof.gryff.Client.Defs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace gryff.examples.gryffnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

instance In.countable [GooseExts] : Pos.Countable In :=
  .ofInjective (fun x => Pos.Countable.encode (x.Op', x.A', x.B'))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; have h := Pos.encode_inj h; simp_all)

/-- The client machines' addresses (`ClientAddrs()`). -/
def clientAddrs : List GoString :=
  [go!"127.0.0.1:7511", go!"127.0.0.1:7512", go!"127.0.0.1:7513", go!"127.0.0.1:7514",
   go!"127.0.0.1:7515", go!"127.0.0.1:7516"]

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : gryff.examples.gryffnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [AllG GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

local notation "kpkg" => pkg_id.gryff.examples.gryffnet

/-- `Codec()`: the register's codec. -/
abbrev Codec.spec : Prop :=
  ∀ γ : ProtoNames,
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! gryff.examples.gryffnet.Codec)) (Val #()))
  {{ (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec), RET #cd;
      codecOk (casR (GF := GF) γ) cd }}

/-- `Gen(c, j)`: an input. -/
abbrev Gen.spec : Prop :=
  ∀ c j : w64,
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (App (Val (@! gryff.examples.gryffnet.Gen)) (Val #c)) (Val #j))
  {{ (x : In), RET #x; True }}

/-- `Orch()`: the orchestrator; it returns (porcupine accepts the history). -/
abbrev Orch.spec : Prop :=
  ∀ (γ : ProtoNames) (γp : PendNames), receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗
      ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (casR γ) a) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := In) ∗
      pendCtx (Gg := hG.goose_globalGS) (casR γ) (casS0 (GF := GF)) γp ∗
      pendLib (Gg := hG.goose_globalGS) (casS0 (GF := GF)) γp (casS0 (GF := GF)).M.init }}
    (App (Val (@! gryff.examples.gryffnet.Orch)) (Val #()))
  {{ RET #(); True }}

/-- The replica ports' listener protocols a client dials (persistent; `Shares.replicaLis`). -/
def replicaLises (γ : GryffNames GF) : IProp GF :=
  [∗list] k ∈ [0, 1, 2], replicaLis γ k

instance replicaLises_persistent (γ : GryffNames GF) : Persistent (replicaLises γ) := by
  unfold replicaLises; infer_instance

/-- `op(sys, x)`: client `c`'s operation under its lock (see the file header). -/
abbrev op.spec : Prop :=
  ∀ (γ : GryffNames GF) (c : Nat) (sp mu cl : Loc) (i : In) (Φ : w64 → IProp GF), c < 6 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ □ protoInvs γ ∗ replicaLises γ ∗
      sysFixed c sp mu cl ∗ sysSt γ c sp cl ∗
      slotUpd (Gg := hG.goose_globalGS) (casR γ.proto) i Φ }}
    (App (App (Val (@! gryff.examples.gryffnet.op)) (Val #sp)) (Val #i))
  {{ (v : GoInterface), RET #v; sysSt γ c sp cl ∗
      ((∃ o, ⌜v = outV ⟨false, o⟩⌝ ∗ Φ o) ∨ ⌜v = outV ⟨true, W64 0⟩⌝) }}

/-- `Client(c)`: client machine `c`; it never returns. -/
abbrev Client.spec : Prop :=
  ∀ (γ : GryffNames GF) (c : Nat), c < 6 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ □ protoInvs γ ∗ replicaLises γ ∗ clientStartRes γ c ∗
      remoteAddr (Gg := hG.goose_globalGS) (casR γ.proto) (clientAddrs.getD c []) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := In) }}
    (App (Val (@! gryff.examples.gryffnet.Client)) (Val #(W64 c)))
  {{ RET #(); False }}

end specs

end gryff.examples.gryffnet

end Perennial
