/- Lean-first (no Rocq counterpart).

`New(id, node, storage, send)` (register.go:96): replica `id` on its running node (the
driver's token at the empty committed log) and its storage; it starts `run`. Since
2026-10-15 (stage N) the node is in raft's dynamic mode (`RegCC`: the cluster's conf changes are
`op`), with the driver's view of its configuration (`nodeCfg`), which `run` keeps. The replica's
seq token (`id ↪[γr.seq] 0`, from the cluster's allocation) gives it `2^64 - 1` operation
credits.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- See the file header. -/
abbrev New.spec : Prop :=
  ∀ (γr : RegNames) (γn : NodeNames) (id : w64) (n st : Loc) (send : GoFunc) (op : CCOp)
    (c0 c1 : CCState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗ regInv γr ∗ nodeDriver γn id n [] ∗ ⌜γn.raft = γr.raft⌝ ∗
      -- (2026-10-15, stage N) the node in the dynamic mode of a cluster whose conf changes are
      -- `op` (`RegCC`), and the driver's view of its configuration, the initial one
      ⌜RegCC γn op c0 c1⌝ ∗ nodeCfg γn 0 c0 ∗
      ⌜γn.stor = regStorIface st⌝ ∗ (∃ (ms : Loc) (γs : MemStorNames), regStorRec st ms γs) ∗ isCommitted γr.raft [] ∗ id ↪[γr.seq] (W64 0) ∗
      sendSpec send γn }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.register.New))
      (Val #id)) (Val #(interface.mkOk (go.GoType.PointerType node.ty) #n))) (Val #st))
      (Val #send))
  {{ (r : Loc), RET #r; ∃ γp : RepNames, ⌜γp.node = γn⌝ ∗ isRegister γr γp r ∗
      opCred γp (2 ^ 64 - 1) }}

end spec

end register
end EtcdGrove
end Perennial
