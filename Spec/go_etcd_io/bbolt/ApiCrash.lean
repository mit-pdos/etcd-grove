/-
**bbolt's crash record** (W3 of `plans/bbolt-crash-plan.md` §3; Lean-first, no Rocq counterpart): what
C-I1's `dbCrashKeep`/`dbCrashHole` (`Proof/go_etcd_io/etcd/server/v3/storage/backend/CrashInterim.lean`)
are, sealed, and the laws of them that need no file reasoning.

`boltCrashRec γ i0 Dl Dn`: half of the committed data at its version `ν` (`boltStateV γ ½ Dn ν`) and the
crash record's evidence `cRec`: the file's crash invariant (`csInvIR` at `crashN γ.ns`, its client
resource `bR`), the crash names' registration (`cnReg`, so the committed data's crash part is the
invariant's), and either `syncedE ν` (the commit that made `ν` finished its second sync) or the
history's element of `ν - 1` (`histE`), whose data is `Dl` or `Dn`. The hole keeps the evidence and
the history's element of `ν` (`Dn`), which the next commit's record takes as its fallback.

* `boltCrashRec_take`, `boltCrashRec_putSame`, `boltCrashRec_putStep`, `boltCrashRec_close`: the
  repackaging laws (C-I1's `take`, `putSame`, `putStep`, `close`).
-/
module

public import Spec.go_etcd_io.bbolt.Api
import all Spec.go_etcd_io.bbolt.Api
import Proof.go_etcd_io.bbolt.CrashMode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open Iris Iris.BI Iris.ProofMode

section crec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **The crash record's evidence** at version `ν` (see the file header). -/
private def cRecDef (B : BNs) (N : Namespace) (i0 : Ino) (c : CsN) (Dl Dn : Data) (ν : Nat) : IProp GF :=
  iprop(⌜c.gc = B.bq ∧ c.N = crashN N⌝ ∗ csInvIR c.N i0 c.g c.ga c.gc bCsOk (bR c.cg) ∗
    cnReg B (some c.cg) ∗
    (syncedE c.cg ν ∨ ∃ P : Data, histE c.cg (ν - 1) P ∗ ⌜1 ≤ ν ∧ (P = Dl ∨ P = Dn)⌝))

private instance cRecDef_persistent (B : BNs) (N : Namespace) (i0 : Ino) (c : CsN) (Dl Dn : Data)
    (ν : Nat) : Persistent (cRecDef (GF := GF) B N i0 c Dl Dn ν) := by
  unfold cRecDef; infer_instance

/-- **The crash record of the open database `γ`, whose file is the inode `i0`** (exclusive; C-I1's
`dbCrashKeep`): the committed data `Dn` (half of it, at its version), the data `Dl` its file falls
back to (see the file header). -/
@[no_expose] def boltCrashRec (γ : BoltName) (i0 : Ino) (Dl Dn : Data) : IProp GF :=
  iprop(∃ (ν : Nat) (c : CsN), boltStateV γ (1 : Qp).half Dn ν ∗
    cRecDef (bnsOf γ.gs) γ.ns i0 c Dl Dn ν)

/-- **The crash record with its half lent at version `ν`** (C-I1's `dbCrashHole`). -/
@[no_expose] def boltCrashHole (γ : BoltName) (i0 : Ino) (Dl Dn : Data) (ν : Nat) : IProp GF :=
  iprop(∃ c : CsN, cRecDef (bnsOf γ.gs) γ.ns i0 c Dl Dn ν ∗ histE c.cg ν Dn)

variable [sem : go.Semantics]

/-- The committed data's crash part, in crash mode, holds the history's element of its version. -/
private theorem crashPart_histE (B : BNs) (g : CsG) (q : Qp) (D : Data) (ν : Nat) :
    cnReg (GF := GF) B (some g) ∗ crashPart B q D ν ⊢ crashPart B q D ν ∗ histE g ν D := by
  unfold crashPart
  iintro ⟨#Hr, %o, #Hr', Hc⟩
  ihave %ho := cnReg_agree B (some g) o $$ [Hr Hr']
  · iframe #
  subst ho
  icases (cpart_some g q D ν).1 $$ Hc with ⟨Hv, #He⟩
  iframe He
  iexists (some g)
  iframe Hr
  iapply (cpart_some g q D ν).2
  iframe Hv; iframe #

/-- **C-I1's `take`**: the half at its version, and the hole. -/
theorem boltCrashRec_take (γ : BoltName) (i0 : Ino) (Dl Dn : Data) :
    boltCrashRec (GF := GF) γ i0 Dl Dn ⊢
      ∃ ν, boltStateV γ (1 : Qp).half Dn ν ∗ boltCrashHole γ i0 Dl Dn ν := by
  unfold boltCrashRec boltCrashHole boltStateV boltStateVDef
  iintro ⟨%ν, %c, ⟨Hs, Hbq, Hcp⟩, #Hrec⟩
  ihave #Hreg : cnReg (GF := GF) (bnsOf γ.gs) (some c.cg) $$ []
  · unfold cRecDef; icases Hrec with ⟨-, -, $, -⟩
  icases crashPart_histE (bnsOf γ.gs) c.cg _ Dn ν $$ [Hcp] with ⟨Hcp, #He⟩
  · iframe; iframe #
  iexists ν
  iframe Hs Hbq Hcp
  iexists c
  iframe #

/-- **C-I1's `putSame`**: the half back at the same version. -/
theorem boltCrashRec_putSame (γ : BoltName) (i0 : Ino) (Dl Dn : Data) (ν : Nat) :
    boltCrashHole (GF := GF) γ i0 Dl Dn ν ∗ boltStateV γ (1 : Qp).half Dn ν ⊢
      boltCrashRec γ i0 Dl Dn := by
  unfold boltCrashRec boltCrashHole
  iintro ⟨⟨%c, #Hrec, -⟩, Hs⟩
  iexists ν, c
  iframe Hs; iframe #

open Classical in
/-- **C-I1's `putStep`**: the half back one commit later; the fallback is the data of `ν`, `Dn`
(the hole's history element), or stays `Dl` when the commit kept the data. -/
theorem boltCrashRec_putStep (γ : BoltName) (i0 : Ino) (Dl Dn S : Data) (ν : Nat) :
    boltCrashHole (GF := GF) γ i0 Dl Dn ν ∗ boltStateV γ (1 : Qp).half S (ν + 1) ⊢
      boltCrashRec γ i0 (if S = Dn then Dl else Dn) S := by
  unfold boltCrashRec boltCrashHole
  iintro ⟨⟨%c, #Hrec, #He⟩, Hs⟩
  iexists (ν + 1), c
  iframe Hs
  unfold cRecDef
  icases Hrec with ⟨%hc, #Hinv, #Hreg, -⟩
  iframe Hinv Hreg
  isplitr
  · ipureintro; exact hc
  iright
  iexists Dn
  rw [show ν + 1 - 1 = ν by omega]
  iframe He
  ipureintro
  refine ⟨by omega, ?_⟩
  by_cases h : S = Dn
  · rw [if_pos h]; exact .inr h.symm
  · rw [if_neg h]; exact .inl rfl

/-- **C-I1's `close`**: the half back (a write transaction may be live: no commit is in flight). -/
theorem boltCrashRec_close (γ : BoltName) (i0 : Ino) (Dl Dn : Data) :
    boltCrashRec (GF := GF) γ i0 Dl Dn ⊢ boltState γ (1 : Qp).half Dn := by
  unfold boltCrashRec
  iintro ⟨%ν, %c, Hs, -⟩
  iapply (boltState_eq_V (GF := GF) γ (1 : Qp).half Dn).2
  iexists ν; iexact Hs

end crec

end bbolt
end EtcdGrove
end Perennial
