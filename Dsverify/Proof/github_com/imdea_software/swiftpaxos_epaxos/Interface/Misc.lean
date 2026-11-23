/-
Small packages on the replicas' paths:

* `dlog`: `(*Logger).Println`, `Printf`, `Fatal` on a non-nil, non-verbose logger
  (`&dlog.Logger{}`, as `serve` makes it): each tests `l == nil` (false) and `l.verbose` (false)
  and returns; the arguments are not formatted, so nothing is asked of them (the lab's `log`
  model's requirements, `fmt.ArgsWf` or the `Error()`/`String()` specs, only arise for a nil or
  verbose logger, which the run never has). `Fatal` does not exit.
* `config`: `(*ProxyInfo).IsProxy` on an empty `ProxyInfo` (`&config.ProxyInfo{}`, as
  `nodeConfig` makes it): `false` (lookups in nil maps).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Wire
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.dlog.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.config.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [replica.Assumptions]

/-- `l.Println(v...)` on a non-verbose logger. -/
def dlog.Logger.Println.spec : Prop :=
  ∀ (l : Loc) (lg : Loc) (v : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.dlog ∗
      l ↦□ dlog.Logger.mk lg false }}
    (App (Val (l @!! go.GoType.PointerType dlog.Logger.ty @!! go!"Println")) (Val #v))
  {{ RET #(); True }}

/-- `l.Printf(format, v...)` on a non-verbose logger. -/
def dlog.Logger.Printf.spec : Prop :=
  ∀ (l : Loc) (lg : Loc) (format : GoString) (v : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.dlog ∗
      l ↦□ dlog.Logger.mk lg false }}
    (App (App (Val (l @!! go.GoType.PointerType dlog.Logger.ty @!! go!"Printf")) (Val #format))
      (Val #v))
  {{ RET #(); True }}

/-- `l.Fatal(v...)` on a non-verbose logger: returns (does not exit). -/
def dlog.Logger.Fatal.spec : Prop :=
  ∀ (l : Loc) (lg : Loc) (v : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.dlog ∗
      l ↦□ dlog.Logger.mk lg false }}
    (App (Val (l @!! go.GoType.PointerType dlog.Logger.ty @!! go!"Fatal")) (Val #v))
  {{ RET #(); True }}

/-- `p.IsProxy(alias, addr)` on an empty `ProxyInfo`: `false`. -/
def config.ProxyInfo.IsProxy.spec : Prop :=
  ∀ (p : Loc) (als addr : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.config ∗
      p ↦□ (zeroValDef : config.ProxyInfo) }}
    (App (App (Val (p @!! go.GoType.PointerType config.ProxyInfo.ty @!! go!"IsProxy"))
      (Val #als)) (Val #addr))
  {{ RET #false; True }}

/-- The zero logger is non-verbose. -/
theorem dlog_zero_logger : (zeroValDef : dlog.Logger) = dlog.Logger.mk null false := by
  rfl

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
