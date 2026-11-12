/-
What `DB.beginTx`/`DB.beginRWTx` share (U5 of `notes/bbolt-proof-plan.md`): the errors they
return (`beginErr`: one of bbolt's error variables `ErrDatabaseNotOpen`, `ErrInvalidMapping`,
`ErrDatabaseReadOnly`), and the read update fired at the meta copy (`au_read_fire`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.State
public import Proof.go_etcd_io.bbolt.PkgInit
public import Spec.fmt.ErrorOk
public import Proof.go_etcd_io.bbolt.Mmap.Infra

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section begin
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **An error `Begin` returns** (persistent): the value of one of bbolt's error variables
`ErrDatabaseNotOpen`, `ErrInvalidMapping`, `ErrDatabaseReadOnly`, not nil. -/
def beginErr (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∗
    (globalAddr go_etcd_io.bbolt.errors.ErrDatabaseNotOpen ↦□ err ∨
      globalAddr go_etcd_io.bbolt.errors.ErrInvalidMapping ↦□ err ∨
      globalAddr go_etcd_io.bbolt.errors.ErrDatabaseReadOnly ↦□ err))

instance beginErr_persistent (err : GoInterface) : Persistent (beginErr (GF := GF) err) := by
  unfold beginErr; infer_instance

/-- **The error of `Begin` is `fmtErrorOk`** (B1: `Open` logs a failed `Begin` with `%v`). Needs
bbolt's error variables' package facts to say each is an `errors.New` error (`IsPointerError` and
`errorString_fmtErrorOk`'s method spec: batch 30's `bboltErrVar`, `beginErrs_fmtErrorOk`). -/
theorem beginErr_fmtErrorOk (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors ∗ beginErr err ⊢ fmtErrorOk err := by
  unfold beginErr
  iintro ⟨#Hep, -, #Hor⟩
  iapply beginErrs_fmtErrorOk err
  iframe #

/-- **The read update fired at the meta copy** (design §3.13, `Begin(false)`'s linearization
point): with `metalock`'s quarter of the committed data `D`, the client's update commits at `D`. -/
theorem au_read_fire (B : BNs) (N : Namespace) (D : Data) (Q : Data → IProp GF) :
    ghostVar B.st (1 : Qp).half.half D ∗
      AU <{ ∃∃ (q : Qp) (D' : Data), boltStateDef B q D' }> @ ⊤ \ ↑N, ∅
        <{ boltStateDef B q D', COMM Q D' }> ⊢
    |={⊤}=> ghostVar B.st (1 : Qp).half.half D ∗ Q D := by
  iintro ⟨Hst, Hau⟩
  ihave Hau := atomic_update_mask_weaken (Eo2 := ⊤) (fun _ _ => CoPset.mem_full) $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%q, %D', Hx, Hucl⟩
  ihave %Hd := boltStateDef_agree_lib B q D' D $$ [Hx Hst]
  · iframe
  subst Hd
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  imod Hcommit $$ Hx with HQ
  imodintro
  iframe

end begin

end bbolt
end EtcdGrove
end Perennial
