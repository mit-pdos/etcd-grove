/-
`DB.Logger` and logging (U4, `notes/bbolt-proof-plan.md`): `db.Logger()` returns the database's
logger, which `dbFixed` (batch 15) says is a `boltLogger` (never nil: the option's, or bbolt's
`discardLogger`'s value, which `Open` stores), and `wp_boltLog`, a call of one of its methods
(`lg.Errorf(fmt, args...)`, ...) under `boltLogger`'s contract.
-/
module

public import Spec.go_etcd_io.bbolt.Logger
public import Proof.go_etcd_io.bbolt.PkgInit
public import Spec.fmt.Errorf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section logger
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.Logger()`** with the database's logger `lg` (`dbFixed`'s, a `boltLogger`): `lg` itself
(the nil test fails: a `boltLogger` is not nil). -/
abbrev DB.Logger.spec : Prop :=
  ∀ (db : Loc) (lg : GoInterface), db ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ db.[DB, go!"logger"] ↦□ lg ∗
      boltLogger lg }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Logger")) (Val #()))
  {{ RET #lg; True }}

omit hos in
theorem DB.Logger.wp_proof : DB.Logger.spec (GF := GF) (hG := hG) := by
  intro db lg hdb
  wp_start as ⟨#Hl, #Hlg⟩
  cases lg with
  | nil => unfold boltLogger; iexfalso; iexact Hlg
  | ok li =>
    wp_auto
    rw [decide_eq_false hdb]
    wp_auto
    iapply HΦ
    itrivial

omit hos package_sem in
/-- **A call of a logging method** of a `boltLogger` `.ok li` (`lg.Errorf(fmtS, args...)`, with
`m` one of `boltLogMethods`, after `wp_auto` resolved the method): given the format's verbs
(`fmtVerbs`, by `decide` on a literal), the arguments' slice and each argument good under its verb
with the lent `R`, the call returns, giving them back. -/
theorem wp_boltLog (li : GoInterfaceOk) (m fmtS : GoString) (vs : List w8) (args : GoSlice)
    (xs : List GoInterface) (dq : DFrac) (R : IProp GF) (Φ : val → IProp GF)
    (hm : m ∈ boltLogMethods) (hv : fmtVerbs fmtS = some vs) (hl : vs.length = xs.length) :
    boltLogger (.ok li) -∗ args ↦*{dq} xs -∗ ([∗list] p ∈ vs.zip xs, logArgOk R p.1 p.2) -∗ R -∗
    (args ↦*{dq} xs -∗ R -∗ Φ #()) -∗
    WP (App (App (Val #(methods li.ty m li.v)) (Val #fmtS)) (Val #args)) {{ Φ }} := by
  iintro #Hlg Hs Ha HR HΦ
  simp only [boltLogger]
  ihave #H := Hlg $$ %m %fmtS %vs %args %xs %dq %R []
  · ipureintro; exact ⟨hm, hv, hl⟩
  iapply H $$ [Hs Ha HR]
  · iframe
  inext
  iintro ⟨Hs, HR⟩
  iapply HΦ $$ Hs HR

omit hos package_sem in
/-- An error `fmt` formats by its `Error()` (or nil) is a good log argument under a method verb. -/
theorem logArgOk_of_fmtErrorOk (R : IProp GF) (v : w8) (hv : v ∈ methodVerbs)
    (err : GoInterface) : fmtErrorOk (GF := GF) err ⊢ logArgOk R v err := by
  cases err with
  | nil => unfold logArgOk; iintro -; itrivial
  | ok ii =>
    unfold logArgOk
    iintro #H
    iright; ileft
    isplitr
    · ipureintro; exact hv
    · iexact H

omit hos package_sem in
/-- A value `fmt` formats with no method (`fmt.ArgWf`: a string, an integer) is a good log
argument under any verb. -/
theorem logArgOk_of_argWf (R : IProp GF) (v : w8) (ii : GoInterfaceOk)
    (h : _root_.Perennial.fmt.ArgWf ii) : ⊢ logArgOk (GF := GF) R v (.ok ii) := by
  unfold logArgOk
  iintro
  ileft; ipureintro; exact h

end logger

/-- Proves `[∗list] p ∈ vs.zip xs, logArgOk R p.1 p.2` of a literal argument list: a `string`
or an `int`/`int64`/`uint64` by `fmt.ArgWf`, an error by a `fmtErrorOk` hypothesis in the
context (under a method verb). -/
macro "log_args_ok" : tactic => `(tactic| (
  try simp only [List.zip_cons_cons, List.zip_nil_left, List.zip_nil_right,
    Iris.BI.BigSepL.bigSepL_cons, Iris.BI.BigSepL.bigSepL_nil]
  repeat' (first
    | isplitr
    | itrivial
    | (iapply Perennial.EtcdGrove.bbolt.logArgOk_of_argWf
       apply Perennial.EtcdGrove.fmt.argWf_of_argsWf
       first
        | exact .cons_string _ _ .nil
        | exact .cons_int _ _ _ (.int64 _) .nil
        | exact .cons_int _ _ _ (.int _) .nil
        | exact .cons_int _ _ _ (.uint64 _) .nil)
    | (iapply Iris.BI.BigSepL.bigSepL_nil.2; iempintro)
    | (iapply Perennial.EtcdGrove.bbolt.logArgOk_of_fmtErrorOk
       · simp [Perennial.EtcdGrove.bbolt.methodVerbs]
       iassumption))))

end bbolt
end EtcdGrove
end Perennial
