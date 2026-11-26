/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__isActive.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__isActive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__getLatestTickTs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.isActive.wp_proof
    (hGLT : raftNode.getLatestTickTs.spec (GF := GF) (hG := hG)) :
    EtcdServer.isActive.spec (GF := GF) (hG := hG) := by
  intro s tm l
  wp_start as ⟨#Htm, #Hlc, Hl, %Hlok⟩
  iunfold srvLeadCheckOk at Hlc
  icases Hlc with ⟨⟨%mu, #Hmu, #Htp⟩, -, -⟩
  iunfold rnTickPool at Htp
  ihave ⟨%γ, #Hp⟩ := Htp $$ %l %Hlok
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto_lc 1
  -- `s.r.getLatestTickTs()`, with a reader slot of `tickMu` borrowed from its pool at level `l`
  iapply wp_fupd
  imod threadPool.borrowL_lc (rnTickPoolN l) l γ _ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hlc1 Hp Hl]
    with ⟨HR, Hloan⟩
  · iframe Hlc1 Hl; iexact Hp
  wp_apply hGLT (srvRAddr s) mu $$ [HR] as %t HR
  · iframe #; iframe HR
  imod threadPool.giveBackL (rnTickPoolN l) l γ _ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp Hloan HR]
    with Hl
  · iframe Hloan HR; iexact Hp
  (try wp_auto)
  -- `latestTickTs.Add(threshold).After(time.Now())`
  wp_apply _root_.Perennial.time.wp_Now as %now -
  (try wp_auto)
  wp_apply _root_.Perennial.time.Time.wp_ptr_Add $$ [$latestTickTs] as %t' latestTickTs
  (try wp_auto)
  wp_apply _root_.Perennial.time.Time.wp_After
  (try wp_auto)
  iapply HΦ
  iframe Hl

end proof

end EtcdGrove
end Perennial
