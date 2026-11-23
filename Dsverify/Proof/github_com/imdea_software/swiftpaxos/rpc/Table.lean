/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/rpc/Table.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`rpc` (fastrpc): the message table (`rpc/rpc.go`), internal specs with their proofs.

`rpc.isTable t dq nid ents`: the `*Table` at `t` with the next id `nid` and the registered
pairs `ents` (message-type id ↦ `Pair{Obj, Chan}`), with fraction `dq` (the registration phase
owns it, `DFrac.own 1`; after `initCs` the replica's readers share it, `DFrac.discard`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.rpc.TableDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [rpc.Assumptions]

end defs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [rpc.Assumptions]

set_option goose.wp.extras true

theorem rpc.NewTableId.wp_proof : rpc.NewTableId.spec := by
  intro id
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := w8) (V := rpc.Pair')) as %mp Hm
  iapply HΦ
  unfold rpc.isTable
  iexists mp
  iframe

theorem rpc.Table.Register.wp_proof : rpc.Table.Register.spec := by
  intro t nid ents obj ch
  wp_start as Ht
  unfold rpc.isTable
  icases Ht with ⟨%mp, Ht, Hm⟩
  wp_auto
  wp_apply (wp_mapInsert (K := w8) (V := rpc.Pair')) $$ Hm as Hm
  iapply HΦ
  iexists mp
  iframe

theorem rpc.Table.Get.wp_proof : rpc.Table.Get.spec := by
  intro t nid ents id
  wp_start as #Ht
  unfold rpc.isTable
  icases Ht with ⟨%mp, #Ht, #Hm⟩
  iStructNamed Ht
  wp_auto
  wp_apply (wp_map_lookup2 (K := w8) (V := rpc.Pair')) $$ Hm as -
  iapply HΦ $$ [-]
  itrivial

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
