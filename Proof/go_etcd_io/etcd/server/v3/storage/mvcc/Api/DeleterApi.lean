/-
**The lessor's range deleter** (`mvccDeleter`, 2026-11-06; until then the placeholder
`mvccDeleter_M1`). Lean-first (no Rocq counterpart). Over the sealed definitions of `Api.lean`
(imported with `import all`).

The constructors give the lessor `func() lease.TxnDelete { return s.Write(traceutil.TODO()) }`,
which their internal specs state as `rdCalls rd ty v` (`RdCalls.lean`): `rd()` does what the
handle's `Write` does at a fresh trace. `mvccDeleter rd γ` follows from it and
`KV.Write.contract` at the handle's type (`store.Write.wp_api`, `watchableStore.Write.wp_api`,
neither with a hypothesis): the deleter's triple is `Write`'s at the `TODO()` trace, the trace
dropped.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RdCalls
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapLaws

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- **The deleter is the handle's `Write`**: from `rdCalls` at the handle's type and its
`KV.Write.contract`. -/
theorem mvccDeleter_of (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (ty : go.GoType) (v : val) (hW : KV.Write.contract (GF := GF) ty v) (rd : GoFunc)
    (γ : MvccName) :
    pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ rdCalls rd ty v ⊢ mvccDeleter rd γ := by
  iintro ⟨#Hpkg, #Hmv, #Hrc⟩
  iunfold rdCalls at Hrc
  icases Hrc with ⟨%hnn, #Hc⟩
  iunfold mvccDeleter
  isplitr
  · ipureintro; exact hnn
  iintro !> %q %B %P %Pre %Q %f %R %Φ !> ⟨Hrt, HB, #Hhk, HPre, Hrun, Hau⟩ HΦ
  ihave Hc' := Hc $$ %(iprop(mvccReaders γ 1 ∗ mvccBackend γ q B P ∗ Pre ∗ hookRun P f Pre Q ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ.pending = none⌝ ∗ mvccState γ σ, COMM R σ }>))
      %(fun t => iprop(mvccBackend γ q B P ∗
        (∃ (trace : Loc) (σ : MvccState), mvccTxn t γ trace (.write σ []) ∗ R σ) ∗ Q)) %hTODO
  ihave Hc'' := Hc' $$ []
  · iintro !> %tr %Ψ' !> ⟨⟨Hrt, HB, HPre, Hrun, Hau⟩, %Htr, Htrc⟩ HΨ'
    wp_apply (hW γ tr true q B P Pre Q f R) $$ [$Hpkg $Hmv $Hrt $Htrc $HB $Hhk $HPre $Hrun $Hau]
      as %t ⟨-, HB, ⟨%σ, Htx, HR⟩, HQ⟩
    · ipureintro; exact Htr
    iapply HΨ'
    dsimp only
    iframe HB HQ
    iexists tr, σ
    iframe Htx HR
  iapply Hc'' $$ [Hrt HB HPre Hrun Hau] HΦ
  iframe Hrt HB HPre Hrun Hau

end proof

end api
end mvcc
end EtcdGrove
end Perennial
