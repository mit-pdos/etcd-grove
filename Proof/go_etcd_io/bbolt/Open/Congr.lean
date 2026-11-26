/-
`simp`'s congruence lemmas (`X.congr_simp`) of the predicates whose goals `Open`'s and
`DB.Close_own`'s proofs `simp` (session bbolt-inv), made in this module so that they are not a proof
file's (`etc/api/bbolt-layout.txt`: a proof file exposes only its `wp_proof`).
-/
module

public import Spec.go_etcd_io.bbolt.Api
public import Proof.go_etcd_io.bbolt.Open.CloseMapDefs
public import Proof.go_etcd_io.bbolt.Inv.Txs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI go_etcd_io.bbolt

section congr
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `boltIno` of equal arguments. -/
theorem boltIno_congr {γ γ' : BoltName} {i i' : Ino} (hγ : γ = γ') (hi : i = i') :
    boltIno (GF := GF) γ i = boltIno γ' i' := by
  simp only [hγ, hi]

/-- `fileHolds` of equal arguments. -/
theorem fileHolds_congr {i i' : Ino} {D D' : Data} (hi : i = i') (hD : D = D') :
    fileHolds (GF := GF) i D = fileHolds i' D' := by
  simp only [hi, hD]

/-- `boltState` of equal arguments. -/
theorem boltState_congr {γ γ' : BoltName} {q q' : Qp} {D D' : Data} (hγ : γ = γ') (hq : q = q')
    (hD : D = D') : boltState (GF := GF) γ q D = boltState γ' q' D' := by
  simp only [hγ, hq, hD]

/-- `txsInv` of equal arguments. -/
theorem txsInv_congr {B B' : BNs} {p p' : BFile} {sp sp' : Loc} {t0 t0' : Nat} (hB : B = B')
    (hp : p = p') (hsp : sp = sp') (ht : t0 = t0') :
    txsInv (GF := GF) B p sp t0 = txsInv B' p' sp' t0' := by
  simp only [hB, hp, hsp, ht]

/-- `closeKeep` of equal arguments. -/
theorem closeKeep_congr {p p' : BFile} {C : CommitSt} {L : List (Nat × Nat)} {m m' : OsMeta}
    {ms ms' : MapSt} (hp : p = p') (hm : m = m') (hms : ms = ms') :
    closeKeep (GF := GF) p C L m ms = closeKeep p' C L m' ms' := by
  simp only [hp, hm, hms]

end congr

end bbolt
end EtcdGrove
end Perennial
