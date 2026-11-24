/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Replica/Base.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The replica unit's proof context and small library specs: `dlog.Printf`/`Println` (a no-op: `DLOG` is
`false` for good, dlog's package fact).
-/
module

public import Dsverify.Proof.gryff.src.gryff.Base
public import Perennial.Proof.time.Link

@[expose] public section

noncomputable section

namespace Perennial.gryff.replica

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [sem : go.Semantics]

/-- `dlog`'s package fact: `DLOG` is `false` for good (`etc/dsv/gryff.py`). -/
theorem dlog_init_access :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog ⊢
      globalAddr gryff.src.dlog.DLOG ↦□ false := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.gryff.src.dlog
end

section generic
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [dlog_sem : gryff.src.dlog.Assumptions]

set_option goose.wp.extras true

theorem wp_dlog_Printf (f : GoString) (v : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog ∗
        globalAddr gryff.src.dlog.DLOG ↦□ false }}
      (App (App (Val (@! gryff.src.dlog.Printf)) (Val #f)) (Val #v))
    {{ RET #(); True }} := by
  wp_start as #Hd
  wp_auto
  wp_end

/-- `t.IsZero()` (Perennial's translation). -/
theorem wp_Time_IsZero [time.Assumptions] (t : time.Time) :
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"IsZero")) (Val #()))
    {{ (b : Bool), RET #b; True }} := by
  wp_start
  wp_auto
  wp_if_destruct <;> wp_end

end generic

end Perennial.gryff.replica
