/-
A counterexample to the bbolt key-value axioms (`notes/axiom-review/bbolt.md`).
`bboltnan.Run` (`examples/axiomcx/bboltnan`) opens a new database, creates a
bucket, sets its `FillPercent` to NaN (`ownWTxG_fill` gives the field for any value), puts 70000
three-byte keys with empty values and commits. The axioms prove that it returns
(`Run.wp_proof`, from the specs it calls; `Run.wp_axioms`, from the axioms themselves); in Go
its `Commit` panics, `inode overflow: 69997` (`bboltnan_test.go`, amd64).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.axiomcx.bboltnan
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BboltOptions
public import Proof.go_etcd_io.bbolt.Open_kv
public import Proof.go_etcd_io.bbolt.DB__Begin_kv
public import Proof.go_etcd_io.bbolt.Tx__CreateBucketIfNotExists_kv
public import Proof.go_etcd_io.bbolt.Bucket__Put_kv
public import Proof.go_etcd_io.bbolt.Tx__Commit_kv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.axiomcx.bboltnan

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package's fact: `True` (no package variable, no `init()`), as `putget`'s. -/
instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.bboltnan :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.bboltnan :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.axiomcx.bboltnan

namespace EtcdGrove
namespace bboltnan

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [cx_sem : github_com.mit_pdos.etcd_grove.examples.axiomcx.bboltnan.Assumptions]

/-- `Run(path)` returns, from a new file at `path` (`fileHolds path ∅`). -/
abbrev Run.spec : Prop :=
  ∀ path : GoString,
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.bboltnan ∗
      fileHolds path ∅ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.axiomcx.bboltnan.Run)) (Val #path))
  {{ RET #(); True }}

theorem Run.wp_proof
    (hOpen : bbolt.Open_kv.spec (GF := GF) (hG := hG))
    (hBegin : bbolt.DB.Begin_kv.spec (GF := GF) (hG := hG))
    (hCreate : bbolt.Tx.CreateBucketIfNotExists_kv.spec (GF := GF) (hG := hG))
    (hPut : bbolt.Bucket.Put_kv.spec (GF := GF) (hG := hG))
    (hCommit : bbolt.Tx.Commit_kv.spec (GF := GF) (hG := hG)) :
    Run.spec (GF := GF) (hG := hG) := by
  intro path
  wp_start as Hfile
  ihave #Hbi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt $$ []
  · iPkgInit
  wp_auto
  wp_apply_core wp_optsLit
  iintro %v0 %hv0
  wp_apply_core (wp_optsAlloc v0 optsZero hv0)
  iintro %bo Hbo
  wp_auto
  -- `bolt.Open(path, 0600, &bolt.Options{})`
  wp_apply (hOpen path (W32 384) bo (DFrac.own 1) optsZero ∅) $$ [$Hfile $Hbo]
    as %db %err ⟨Hbo, Hres⟩
  · iframe #
    isplitr
    · ipureintro; exact optsZero_ok
    · ileft; ipureintro; rfl
  icases Hres with (%Herr | ⟨%Herr, %γd, Hown, Hwr, #Hdb⟩)
  · rcases err with ei | _
    · wp_auto
      iapply HΦ; itrivial
    · exact absurd rfl Herr
  subst Herr
  wp_auto
  -- `db.Begin(true)`
  wp_apply (hBegin db γd ∅ true) $$ [$Hown Hwr] as %tx %err2 ⟨Hown, -, Hres⟩
  · iframe #
    simp only [↓reduceIte]
    iexact Hwr
  icases Hres with (⟨%Herr, -⟩ | ⟨%Herr, #Htxdb, Hw⟩)
  · rcases err2 with ei | _
    · wp_auto
      iapply HΦ; itrivial
    · exact absurd rfl Herr
  subst Herr
  icases Hw with ⟨%G, Hw⟩
  wp_auto
  -- `tx.CreateBucketIfNotExists([]byte("b"))`
  wp_apply wp_string_to_bytes as %nm ⟨Hnm, -⟩
  wp_apply (hCreate tx γd ∅ ∅ G nm go!"b" (DFrac.own 1) (by decide) (by decide)) $$ [$Hw $Hnm]
    as %b %err3 ⟨%Herr3, Hw, #Hwb, -⟩
  subst Herr3
  wp_auto
  -- `b.FillPercent = z / z` (NaN): the field from `ownWTxG_fill`, given back with any value
  icases ownWTxG_fill tx b γd ∅ _ G go!"b" (G go!"b") $$ [$Hw $Hwb] with ⟨%f, Hf, Hback⟩
  wp_auto
  ihave Hw := Hback $$ %_ Hf
  -- the loop: the bucket holds some entries
  ihave HI : (∃ (j : w64) (m : BktData),
      "i" ∷ i_ptr ↦ j ∗ "Hw" ∷ ownWTxG tx γd ∅ (<[go!"b" := m]>∅) G : IProp GF) $$ [i Hw]
  · iexists W64 0, ∅
    iframe
  wp_for HI
  split
  · wp_auto
    -- `k := []byte{...}`, `b.Put(k, []byte{})`
    wp_apply wp_slice_literal (V := w8)
      [W8 (uint.Z (j >>> W64 16)), W8 (uint.Z (j >>> W64 8)), W8 (uint.Z j)]
    isplitr
    · ipureintro; rfl
    iintro %ks ⟨Hks, -⟩
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) ([] : List w8)
    isplitr
    · ipureintro; rfl
    iintro %vs ⟨Hvs, -⟩
    ipersist Hvs
    (try wp_auto)
    wp_apply (hPut tx γd ∅ (<[go!"b" := m]>∅) G b go!"b" (G go!"b") m _ _ _ [] (DFrac.own 1)
        rfl (GMap.lookup_insert _ _ _) (by simp) (by simp [maxKeySize]))
      $$ [$Hw $Hwb $Hks $Hvs] as %err4 ⟨-, Hres⟩
    icases Hres with (⟨%Hok, Hw⟩ | ⟨%Hbig, -⟩)
    · obtain ⟨-, rfl⟩ := Hok
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, _
      simp only [GMap.insert_insert]
      iframe
    · exfalso; simp [maxValueSize] at Hbig
  · -- `tx.Commit()`, which the axioms say returns
    wp_auto
    wp_apply (hCommit db tx γd ∅ (<[go!"b" := m]>∅)) $$ [$Hown Hw] as %err5 -
    · iframe #
      iexists G
      iexact Hw
    iapply HΦ; itrivial

/-- `Run` returns, from the bbolt axioms themselves; in Go it panics. -/
theorem Run.wp_axioms : Run.spec (GF := GF) (hG := hG) :=
  Run.wp_proof bbolt.Open_kv.wp_proof bbolt.DB.Begin_kv.wp_proof
    bbolt.Tx.CreateBucketIfNotExists_kv.wp_proof bbolt.Bucket.Put_kv.wp_proof
    bbolt.Tx.Commit_kv.wp_proof

end proof

#print axioms Run.wp_proof
#print axioms Run.wp_axioms

end bboltnan
end EtcdGrove
end Perennial
