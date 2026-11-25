/-
`examples/etcd/dist/kvremote`'s linked results: every proved function's proof applied to its callees'
linked proofs (`enc`'s, `EtcdGrove.enc`; txnlin's `IsWrite`, from its proofs: txnlin's `Link` reaches the whole server).
Hand-written, as `enc`'s (`etc/gen-link.py` has no mode for it).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encCmp
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decCmp
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encTOp
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decTOp
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encVR
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decVR
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encTRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decTRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encKV
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decKV
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.EncInput
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.DecInput
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.EncOutput
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.DecOutput
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Codec
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.IsWrite
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.isWrite
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.thenOf
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.elseOf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace EtcdGrove.kvremote

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
open EtcdGrove.enc

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]

theorem wp_IsWrite : EtcdGrove.etcd_txnlin.IsWrite.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.IsWrite.wp_proof (EtcdGrove.etcd_txnlin.isWrite.wp_proof
    EtcdGrove.etcd_txnlin.thenOf.wp_proof EtcdGrove.etcd_txnlin.elseOf.wp_proof)
theorem wp_encCmp : encCmp.spec (GF := GF) (hG := hG) := encCmp.wp_proof Enc.wp_Int Enc.wp_Str Enc.wp_I64
theorem wp_decCmp : decCmp.spec (GF := GF) (hG := hG) := decCmp.wp_proof Dec.wp_Int Dec.wp_Str Dec.wp_I64
theorem wp_encTOp : encTOp.spec (GF := GF) (hG := hG) := encTOp.wp_proof Enc.wp_Int Enc.wp_Str
theorem wp_decTOp : decTOp.spec (GF := GF) (hG := hG) := decTOp.wp_proof Dec.wp_Int Dec.wp_Str
theorem wp_encVR : encVR.spec (GF := GF) (hG := hG) := encVR.wp_proof Enc.wp_Str Enc.wp_I64
theorem wp_decVR : decVR.spec (GF := GF) (hG := hG) := decVR.wp_proof Dec.wp_Str Dec.wp_I64
theorem wp_encTRes : encTRes.spec (GF := GF) (hG := hG) :=
  encTRes.wp_proof Enc.wp_Int Enc.wp_Bool wp_encVR Enc.wp_I64
theorem wp_decTRes : decTRes.spec (GF := GF) (hG := hG) :=
  decTRes.wp_proof Dec.wp_Int Dec.wp_Bool wp_decVR Dec.wp_I64
theorem wp_encKV : encKV.spec (GF := GF) (hG := hG) := encKV.wp_proof Enc.wp_Str wp_encVR
theorem wp_decKV : decKV.spec (GF := GF) (hG := hG) := decKV.wp_proof Dec.wp_Str wp_decVR
theorem wp_EncInput : EncInput.spec (GF := GF) (hG := hG) :=
  EncInput.wp_proof Enc.wp_Int Enc.wp_Str wp_encCmp wp_encTOp
theorem wp_DecInput : DecInput.spec (GF := GF) (hG := hG) :=
  DecInput.wp_proof Dec.wp_Int Dec.wp_Str wp_decCmp wp_decTOp wp_NewDec Dec.wp_Done
theorem wp_EncOutput : EncOutput.spec (GF := GF) (hG := hG) :=
  EncOutput.wp_proof Enc.wp_Bool Enc.wp_I64 wp_encVR Enc.wp_Int wp_encTRes wp_encKV
theorem wp_DecOutput : DecOutput.spec (GF := GF) (hG := hG) :=
  DecOutput.wp_proof Dec.wp_Bool Dec.wp_I64 wp_decVR Dec.wp_Int wp_decTRes wp_decKV wp_NewDec Dec.wp_Done
theorem wp_Codec : Codec.spec (GF := GF) (hG := hG) :=
  Codec.wp_proof wp_EncInput wp_DecInput wp_EncOutput wp_DecOutput wp_IsWrite

end linked

end EtcdGrove.kvremote
end Perennial
