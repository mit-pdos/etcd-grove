/-
What `watch.go` reads of package variables, the part `v3rpc`'s initializer gives (D19j,
2026-10-18: moved here from `InvWatch.lean`, so that `v3rpc`'s package facts (`Base.lean`,
`watchPkgVars`) can state them): the shapes of the error and histogram variables
(`msgErrVar`, `histVar`), the progress interval's lock and what it guards (`intervalMu`,
`intervalP`), and the lemmas that turn other packages' facts into these shapes (`auth`'s
`authErrVar`, the cache's `errorStringSpec`).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Proof.Lib.Heap
public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The progress interval's lock (the package variable `progressReportIntervalMu`). -/
abbrev v3rpc.intervalMu : Loc :=
  globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.progressReportIntervalMu

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package variable `g` holds a fixed error whose `Error()` returns (persistent). -/
def v3rpc.msgErrVar (g : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ errMsgOk e)

instance v3rpc.msgErrVar_persistent (g : GoString) : Persistent (v3rpc.msgErrVar (GF := GF) g) := by
  unfold v3rpc.msgErrVar errMsgOk; infer_instance

/-- The package variable `g` holds a fixed histogram whose `Observe` returns (persistent). -/
def v3rpc.histVar (g : GoString) : IProp GF :=
  iprop(∃ h : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok h ∗
    □ (∀ x : w64, {{ True }} (App (Val #(methods h.ty go!"Observe" h.v)) (Val #x))
      {{ RET #(); True }}))

instance v3rpc.histVar_persistent (g : GoString) : Persistent (v3rpc.histVar (GF := GF) g) := by
  unfold v3rpc.histVar; infer_instance

/-- **The progress interval** at the fraction `q` (what `progressReportIntervalMu` guards): a
duration of at least `10` nanoseconds (`GetProgressReportInterval`'s jitter `rand.Int63n(d / 10)`
needs `d / 10 > 0`) and at most `2 ^ 62` (`d + d / 10` must not wrap:
`issues/etcd-watch-progress-interval-overflow.md`). -/
def v3rpc.intervalP (q : Qp) : IProp GF :=
  iprop(∃ d : w64, typedPointsto (globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.progressReportInterval)
      d (DFrac.own q) ∗ ⌜10 ≤ sint.Z d ∧ sint.Z d ≤ 2 ^ 62⌝)

instance v3rpc.intervalP_fractional : Fractional (v3rpc.intervalP (GF := GF)) where
  fractional q1 q2 := by
    unfold v3rpc.intervalP
    constructor
    · iintro ⟨%d, Hd, %Hb⟩
      icases (ptsto_frac_add _ _ q1 q2).1 $$ Hd with ⟨H1, H2⟩
      isplitl [H1]
      · iexists d; iframe; ipureintro; exact Hb
      · iexists d; iframe; ipureintro; exact Hb
    · iintro ⟨⟨%d1, H1, %Hb⟩, ⟨%d2, H2, -⟩⟩
      icombine H1 H2 gives %Hd
      subst Hd
      iexists d1
      isplitl [H1 H2]
      · iapply (ptsto_frac_add _ _ q1 q2).2; iframe
      · ipureintro; exact Hb

/-- An `auth` error variable (`authErrVar`) in the apply package's shape (`errVarLeaf`). -/
theorem v3rpc.errVarLeaf_of_authErrVar (g : GoString) :
    go_etcd_io.etcd.server.v3.auth.authErrVar (GF := GF) g ⊢ errVarLeaf g := by
  unfold go_etcd_io.etcd.server.v3.auth.authErrVar errVarLeaf errLeaf errMsgOk
  iintro ⟨%e, #He, %Hl, #Hm⟩
  iexists e
  iframe He Hm
  ipureintro; exact Hl

/-- An error whose `Error()` returns (the cache's `errorStringSpec`), as a triple (`errMsgOk`). -/
theorem v3rpc.errMsgOk_of_errorStringSpec (e : GoInterfaceOk) :
    go_etcd_io.etcd.cache.v3.errorStringSpec (GF := GF) e ⊢ errMsgOk e := by
  unfold go_etcd_io.etcd.cache.v3.errorStringSpec errMsgOk
  iintro #H
  iintro !> %Φ - HΦ
  iapply H
  inext
  iintro %s
  iapply HΦ
  itrivial

/-- An error variable whose `Error()` returns (the cache's `errorStringSpec`), as `msgErrVar`. -/
theorem v3rpc.msgErrVar_of_spec (g : GoString) :
    (∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗
        go_etcd_io.etcd.cache.v3.errorStringSpec (GF := GF) e) ⊢ v3rpc.msgErrVar g := by
  iintro ⟨%e, #He, #Hs⟩
  unfold v3rpc.msgErrVar
  iexists e
  iframe He
  iapply v3rpc.errMsgOk_of_errorStringSpec
  iexact Hs

end defs

end EtcdGrove
end Perennial
