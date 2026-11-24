/-
kitlibs-check's field tests (etc/kitlibs-check.py --selftest): elaborated over selftest.modules (rabia's
environment), with selftest.conf (rabia's packages are the system's). Every structure whose name
starts with `ok`/`bad` is checked as a KitLibs class declared here; `bad` ones must be refused, for
the reason their `expect:` names. Axioms `axOk*`/`axBad*` are checked as a non-vacuity module's
axioms (each must be about a library function).
-/
set_option linter.iris.style.nameCheck false
set_option autoImplicit false

noncomputable section

namespace Perennial.kitlibsCheckTest

open Iris Iris.BI Iris.ProgramLogic Net

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [GoGlobalContext]

/-! ## Accepted -/

/-- The empty class (paxos's: no library premise). -/
class okEmpty (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where

/-- rabia's landed premises, as fields: six `InitHyp`s, three library `Hyps` (unfolded: their
fields are triples about zerolog's, gogo proto's and math/rand's functions; proto's `RegisterEnum`
consumes `message.MsgType_value`'s points-to, a system global's address at negative polarity) and
the signal assumption (`Notify`'s triple). -/
class okRabiaLanded (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics]
    [github_com.rs.zerolog.Assumptions] : Prop where
  zerolog_init : github_com.rs.zerolog.InitHyp GF
  proto_init : github_com.gogo.protobuf.proto.InitHyp GF
  proto : github_com.gogo.protobuf.proto.Hyps GF
  gogoproto_init : github_com.gogo.protobuf.gogoproto.InitHyp GF
  redis_init : github_com.go_redis.redis.v8.InitHyp GF
  signal_init : os.signal.InitHyp GF
  rand_init : math.rand.InitHyp GF
  zerolog : github_com.rs.zerolog.Hyps GF
  rand : math.rand.Hyps GF
  no_signals : os.signal.NoSignals os.signal.quietSigs GF

/-- The agent's own spec definitions (a challenge ships no library `Spec.lean`): an abbrev for a
triple, a structure of triples over a data token, the token as a data field. -/
abbrev myNew.spec (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop :=
  ∀ (w : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
    (App (Val (@! github_com.rs.zerolog.New)) (Val #w))
  {{ (lg : github_com.rs.zerolog.Logger), RET #lg; True }}

structure MyRand (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics]
    (ownRand : Loc → IProp GF) : Prop where
  intn : ∀ (r : Loc) (n : w64), 0 < sint.Z n →
    {{ ownRand r }}
      (App (Val (r @!! go.GoType.PointerType math.rand.Rand.ty @!! go!"Intn")) (Val #n))
    {{ (x : w64), RET #x; ownRand r ∗ ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }}

class okOwnDefs (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Type where
  ownRand : Loc → IProp GF
  rand : MyRand GF ownRand
  new : myNew.spec GF
  rands : ∃ own : Loc → IProp GF, MyRand GF own

/-! ## Refused -/

/-- The conclusion itself. expect: rabia -/
class badConclusion (GF : BundledGFunctors) : Prop where
  concl : rabia.examples.rabianet.rabia_remote_robust.spec

/-- The conclusion restated. expect: Net.Statement -/
class badConclusionRestated (GF : BundledGFunctors) : Prop where
  concl : ∀ [lctx : GoLocalContext] [go.Semantics] (g : GlobalState) (σ : Nat → state),
    DistDeploy [] [] g → True

/-- `Robust` itself. expect: Robustness -/
class badRobust (GF : BundledGFunctors) [GoLocalContext] [go.Semantics] : Prop where
  r : ∀ g, Robustness.Robust [] [] g 0 0

/-- A triple about the system's own function. expect: system or driver package `rabia` -/
class badSystemTriple (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  getEnvInt : ∀ (s : GoString),
    {{ (⌜True⌝ : IProp GF) }} (App (Val (@! rabia.internal.config.getEnvInt)) (Val #s)) {{ (x : w64), RET #x; True }}

/-- A library triple whose precondition names the system's package state. expect: rabia -/
class badSystemInPre (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics]
    [IsPkgInit (IProp GF) pkg_id.rabia.internal.config] : Prop where
  new : ∀ (w : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.config }}
      (App (Val (@! github_com.rs.zerolog.New)) (Val #w))
    {{ (lg : github_com.rs.zerolog.Logger), RET #lg; True }}

/-- A system global's points-to given out by a library function (positive). expect: MsgType_value -/
class badSystemGlobalInPost (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  new : ∀ (w : GoInterface),
    {{ (⌜True⌝ : IProp GF) }}
      (App (Val (@! github_com.rs.zerolog.New)) (Val #w))
    {{ (lg : github_com.rs.zerolog.Logger), RET #lg;
       (globalAddr rabia.internal.message.MsgType_value ↦ (null : Loc) : IProp GF) }}

/-- The driver's function. expect: system or driver package -/
class badDriver (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  check : {{ (⌜True⌝ : IProp GF) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.Check)) (Val #()))
    {{ RET #(); True }}

/-- The net model's function (its specs are proved, never assumed). expect: model package `net` -/
class badNetModel (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  dial : ∀ (a b : GoString),
    {{ (⌜True⌝ : IProp GF) }} (App (App (Val (@! net.Dial)) (Val #a)) (Val #b)) {{ (v : val), RET v; True }}

/-- A pure fact. expect: not a library spec -/
class badFalse (GF : BundledGFunctors) : Prop where
  f : False

/-- An equation. expect: not a library spec -/
class badPure (GF : BundledGFunctors) : Prop where
  f : (1 : Nat) = 2

/-- A ghost update, no triple. expect: not a Hoare triple -/
class badGhost (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] : Prop where
  g : ∀ (P : IProp GF), ⊢ |==> P

/-- A triple about any function value. expect: subject -/
class badAnyFunc (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  f : ∀ (f : val), {{ (⌜True⌝ : IProp GF) }} (App (Val f) (Val #())) {{ RET #(); True }}

opaque hidden : Prop
/-- The agent's opaque predicate (kitlibs-check cannot see through it). expect: not a library spec -/
class badOpaque (GF : BundledGFunctors) : Prop where
  h : hidden

/-- A parameter of the system's. expect: rabia -/
class badParam (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics]
    [rabia.internal.config.Assumptions] : Prop where

/-- Library data whose type is the system's. expect: rabia -/
class badSystemData (GF : BundledGFunctors) : Type where
  d : rabia.internal.config.Config → Prop

/-- A library triple hidden in an agent definition that adds the system's state. expect: rabia -/
abbrev sneaky.spec (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics]
    [IsPkgInit (IProp GF) pkg_id.rabia.internal.config] : Prop :=
  ∀ (w : GoInterface),
  {{ (⌜True⌝ : IProp GF) }} (App (Val (@! github_com.rs.zerolog.New)) (Val #w))
  {{ (lg : github_com.rs.zerolog.Logger), RET #lg; isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.config }}
class badSneaky (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics]
    [IsPkgInit (IProp GF) pkg_id.rabia.internal.config] : Prop where
  s : sneaky.spec GF

/-! ## The non-vacuity module's axioms -/

/-- About a library function: accepted. -/
axiom axOkNew (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : myNew.spec GF

/-- An `InitHyp`: accepted. -/
axiom axOkInit (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] :
  github_com.rs.zerolog.InitHyp GF

/-- `False`. expect: not a library spec -/
axiom axBadFalse : False

/-- About the system's function. expect: rabia -/
axiom axBadSystem (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : ∀ (s : GoString),
    {{ (⌜True⌝ : IProp GF) }} (App (Val (@! rabia.internal.config.getEnvInt)) (Val #s)) {{ (x : w64), RET #x; True }}

end
end Perennial.kitlibsCheckTest
