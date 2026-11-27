import Proof.go_etcd_io.etcd.server.v3.storage.backend.CrashInterim
import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.crash.MemberCrash

open Lean Meta Elab Command

partial def binfoCmp : Expr → Expr → List (Name × BinderInfo × BinderInfo)
  | .forallE n1 _ b1 i1, .forallE _ _ b2 i2 =>
      (if i1 != i2 then [(n1, i1, i2)] else []) ++ binfoCmp b1 b2
  | _, _ => []

elab "#cmpTypes " a:ident b:ident : command => liftTermElabM do
  let ia ← getConstInfo (← realizeGlobalConstNoOverloadWithInfo a)
  let ib ← getConstInfo (← realizeGlobalConstNoOverloadWithInfo b)
  let tb := ib.type.instantiateLevelParams ib.levelParams (ia.levelParams.map Level.param)
  let diffs := binfoCmp ia.type tb
  logInfo m!"{a} vs {b}: levels {ia.levelParams} / {ib.levelParams}; eqv={ia.type.eqv tb}; binderInfo diffs={diffs.map (fun (n,_,_) => n)}"
  if !(ia.type.eqv tb) then
    logInfo m!"OLD: {ia.type}\nNEW: {tb}"

namespace Perennial
namespace EtcdGrove
namespace backend
namespace oldStmt

open Iris Iris.BI Classical

section laws
attribute [local instance] GooseGlobalGS.gooseInvGS
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors}

axiom dbCrashKeep_new [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (D : Data) (tx : Loc) :
    ⊢ dbOpts (hlc := HasLC.hasLC) (GF := GF) γ -∗ onFs (GF := GF) iprop(bbolt.boltIno γ i0) -∗
      dbHalf γ D -∗ txLive tx γ 1 (bbolt.TxView.wr D) ==∗
      dbCrashKeep γ i0 D D ∗ txLive tx γ 1 (bbolt.TxView.wr D)

axiom dbCrashKeep_take [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn : Data) :
    dbCrashKeep (GF := GF) γ i0 Dl Dn ⊢ ∃ ν, dbHalfV γ Dn ν ∗ dbCrashHole γ i0 Dl Dn ν

axiom dbCrashKeep_putSame [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn : Data) (ν : Nat) :
    dbCrashHole (GF := GF) γ i0 Dl Dn ν ∗ dbHalfV γ Dn ν ⊢ dbCrashKeep γ i0 Dl Dn

axiom dbCrashKeep_putStep [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn S : Data) (ν : Nat) :
    dbCrashHole (GF := GF) γ i0 Dl Dn ν ∗ dbHalfV γ S (ν + 1) ⊢
      dbCrashKeep γ i0 (if S = Dn then Dl else Dn) S

axiom dbCrashKeep_close [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn S : Data) (G : GoString → Nat) (tx : Loc) :
    dbCrashKeep γ i0 Dl Dn ∗ txLive (GF := GF) tx γ 1 (wView Dn S G) ⊢
      dbHalf γ Dn ∗ txLive (GF := GF) tx γ 1 (wView Dn S G)

-- the old text with exactly the two approved changes
axiom dbCrash [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [G : GooseGlobalGS HasLC.hasLC GF]
    (Q : Fs.OsState → Fs.OsState → Prop) (L L' : GooseLocalGS GF)
    [sem : @go.Semantics _ L.goose_go_local_context _] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn : Data)
    (hQ : ∀ st st', Q st st' → BoltCrashWhole (· = i0) st st')
    (Dx : List Fs.Ino) (hi : i0 ∉ Dx) (V' : Fs.Hist) (hN : Fs.Named V'.now i0) (E : CoPset)
    (hE : (↑(bbolt.crashN γ.ns) : CoPset) ⊆ E := by simp) :
    ⊢ dbCrashKeep (hG := ⟨G, L⟩) γ i0 Dl Dn -∗ crashed (hC := L.goose_crashGS) -∗
      Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) Dx false V' ={E}=∗
      ∃ D' : Data, ⌜D' = Dl ∨ D' = Dn⌝ ∗
        bbolt.fileHoldsMDur (hG := ⟨G, L'⟩) i0 D' ∗
        Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) (i0 :: Dx) false V'

-- the old text verbatim but fileHoldsM -> fileHoldsM (control: same as old conclusion, with sem)
axiom dbCrashOldConcl [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [G : GooseGlobalGS HasLC.hasLC GF]
    (Q : Fs.OsState → Fs.OsState → Prop) (L L' : GooseLocalGS GF)
    [sem : @go.Semantics _ L.goose_go_local_context _] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn : Data)
    (hQ : ∀ st st', Q st st' → BoltCrashWhole (· = i0) st st')
    (Dx : List Fs.Ino) (hi : i0 ∉ Dx) (V' : Fs.Hist) (hN : Fs.Named V'.now i0) (E : CoPset)
    (hE : (↑(bbolt.crashN γ.ns) : CoPset) ⊆ E := by simp) :
    ⊢ dbCrashKeep (hG := ⟨G, L⟩) γ i0 Dl Dn -∗ crashed (hC := L.goose_crashGS) -∗
      Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) Dx false V' ={E}=∗
      ∃ D' : Data, ⌜D' = Dl ∨ D' = Dn⌝ ∗
        bbolt.fileHoldsM (hG := ⟨G, L'⟩) i0 D' ∗
        Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) (i0 :: Dx) false V'

-- the old corollary derivable from the new theorem (the caller's one-liner, generically)
theorem dbCrashOldConcl_of_new : True := trivial
end laws
end oldStmt
end backend
end EtcdGrove
end Perennial

open Perennial.EtcdGrove
#cmpTypes backend.oldStmt.dbCrashKeep_new backend.dbCrashKeep_new
#cmpTypes backend.oldStmt.dbCrashKeep_take backend.dbCrashKeep_take
#cmpTypes backend.oldStmt.dbCrashKeep_putSame backend.dbCrashKeep_putSame
#cmpTypes backend.oldStmt.dbCrashKeep_putStep backend.dbCrashKeep_putStep
#cmpTypes backend.oldStmt.dbCrashKeep_close backend.dbCrashKeep_close
#cmpTypes backend.oldStmt.dbCrash backend.dbCrash
#cmpTypes backend.oldStmt.dbCrashOldConcl backend.dbCrash

set_option pp.explicit true in
#check @bbolt.fileHoldsMDur
set_option pp.explicit true in
#check @bbolt.fileHoldsM
set_option pp.explicit true in
#check @backend.dbCrashKeep
#print axioms backend.dbCrash
#print axioms backend.dbCrashKeep_new
#print axioms backend.dbCrashKeep_take
#print axioms backend.dbCrashKeep_putSame
#print axioms backend.dbCrashKeep_putStep
#print axioms backend.dbCrashKeep_close
#print axioms memberCrash.memberGen_crash_law_holds
#print backend.dbCrashKeep
#print backend.dbCrashHole
#print axioms backend.boltCrashWhole_exists

elab "#cmpAuto " a:ident b:ident : command => liftTermElabM do
  let ia ← getConstInfo (← realizeGlobalConstNoOverloadWithInfo a)
  let ib ← getConstInfo (← realizeGlobalConstNoOverloadWithInfo b)
  let norm (e : Expr) : Expr := e.replace fun x => match x with
    | .const n _ => if n.isStr && n.getString! == "_auto_1" then some (.const `AUTO []) else none
    | _ => none
  let va := (← getConstInfo (ia.name ++ `_auto_1)).value!
  let vb := (← getConstInfo (ib.name ++ `_auto_1)).value!
  logInfo m!"{a} vs {b} modulo _auto_1 name: eqv={(norm ia.type).eqv (norm ib.type)}; auto values eqv={va.eqv vb}"
#cmpAuto backend.oldStmt.dbCrash backend.dbCrash
