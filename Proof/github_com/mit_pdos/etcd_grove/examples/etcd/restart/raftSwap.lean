/-
Proofs of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restart/raftSwap.lean` (restart3 C3,
2026-11-15): `ServeHTTP` (lock, read `sw.h`, the slot token traded for a copy of the current
incarnation's resource, `sw_enter`; unlock; the incarnation's handler, `http.handlerOk`'s invocation;
the copy traded back for the token, `sw_exit`) and `set` (lock, the new incarnation installed,
`sw_install`; `sw.h` stored; unlock). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.raftSwap
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

theorem raftSwap.ServeHTTP.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    raftSwap.ServeHTTP.spec (GF := GF) (hG := hG) := by
  intro sw γS γn a wi r R γk rd
  iintro #Hpkg #Hsw #Hra %Hh #Hreq Htk Hbody Hw Hhd %Hfl Htok
  iunfold swapOk at Hsw
  icases Hsw with ⟨%Hn, %mu, #Hmu, #Hlock, #HG⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  rw [method_unfold (t := go.GoType.PointerType
    github_com.mit_pdos.etcd_grove.examples.etcd.restart.raftSwap.ty) (m := go!"ServeHTTP")]
  wp_pures
  wp_auto
  -- `sw.mu.Lock()`
  wp_apply (lc := 1) (wp_Lock mu (swLock sw γS γn a)) $$ [$Hlock] as ⟨Hown, Hinv⟩
  iunfold swLock at Hinv
  icases Hinv with ⟨%h, %c, %b, %τ, Hhf, Hcur, #Hh⟩
  -- `h := sw.h`
  wp_auto
  -- the slot token for a copy of the current incarnation's resource
  imod sw_enter γS γn c b τ $$ [Hcur Htok Hlc1] with ⟨Hcur, Hcp, Hrc⟩
  · iframe; iframe #
  -- `sw.mu.Unlock()`
  wp_apply (wp_Unlock mu (swLock sw γS γn a)) $$ [Hown Hhf Hcur]
  · iframe; iframe #
    inext
    iunfold swLock
    iexists h, c, b, τ
    iframe; iframe #
  -- `h.ServeHTTP(w, r)`, with the copy
  iunfold http.handlerOk at Hh
  icases Hh with ⟨%hi, %Hhi, #Hwp⟩
  subst Hhi
  wp_auto
  ihave Hcall := Hwp $$ %wi %r %R %γk %rd Hra %Hh Hreq Htk Hbody Hw Hhd %Hfl Hcp
  wp_bind (App (App (Val _) (Val _)) (Val _))
  iapply wp_wand $$ Hcall
  iintro %v ⟨Hcp, Hdone⟩
  -- the copy back for the slot token
  imod sw_exit γS γn c b τ $$ [Hrc Hcp] with Htok
  · iframe; iframe #
  cases hp : v.isPanic
  · -- the handler returned: so does `ServeHTTP`
    wp_auto
    iframe Htok
    iunfold http.handlerDone at Hdone
    iunfold http.handlerDone
    icases Hdone with (H | ⟨%Hp, -⟩)
    · ileft; iexact H
    · rw [hp] at Hp; cases Hp
  · -- the handler panicked: the panic unwinds `ServeHTTP` (`http.Serve` recovers it)
    obtain ⟨p, rfl⟩ := val.isPanic_eq_true hp
    wp_auto
    iframe

theorem raftSwap.set.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    raftSwap.set.spec (GF := GF) (hG := hG) := by
  intro sw γS γn a h τ
  wp_start as ⟨#Hsw, #Hh, Hcp⟩
  iunfold swapOk at Hsw
  icases Hsw with ⟨%Hn, %mu, #Hmu, #Hlock, #HG⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  -- `sw.mu.Lock()`
  wp_apply (wp_Lock mu (swLock sw γS γn a)) $$ [$Hlock] as ⟨Hown, Hinv⟩
  iunfold swLock at Hinv
  icases Hinv with ⟨%h0, %c, %b, %τ0, Hhf, Hcur, -⟩
  -- the new incarnation installed
  have Hins := sw_install (GF := GF) γS γn c b τ0 τ
  rw [Hn] at Hins
  imod Hins $$ [Hcur Hcp] with ⟨%c', %b', Hcur⟩
  · iframe; iframe #
  -- `sw.h = h`
  wp_auto
  -- `sw.mu.Unlock()`
  wp_apply (wp_Unlock mu (swLock sw γS γn a)) $$ [Hown Hhf Hcur]
  · iframe; iframe #
    inext
    iunfold swLock
    iexists h, c', b', τ
    iframe; iframe #
  iapply HΦ
  itrivial

end proof

end etcd_restart
end EtcdGrove
end Perennial
