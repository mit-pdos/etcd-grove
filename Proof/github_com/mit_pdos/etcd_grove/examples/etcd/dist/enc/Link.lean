/-
`examples/etcd/dist/enc`'s linked results: every function's proof applied to its callees' linked
proofs (`I64`, `Int` and `Str` call `U64`). Hand-written, as `remote`'s (`etc/gen-link.py` has no
mode for it). All twelve are exported: the codecs of the etcd-dist workloads call them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__U64
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__I64
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Int
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Bool
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Str
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.NewDec
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__U64
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__I64
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Int
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Bool
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Str
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Done

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace EtcdGrove.enc

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Assumptions]

theorem Enc.wp_U64 : Enc.U64.spec (GF := GF) (hG := hG) := Enc.U64.wp_proof
theorem Enc.wp_I64 : Enc.I64.spec (GF := GF) (hG := hG) := Enc.I64.wp_proof Enc.wp_U64
theorem Enc.wp_Int : Enc.Int.spec (GF := GF) (hG := hG) := Enc.Int.wp_proof Enc.wp_U64
theorem Enc.wp_Bool : Enc.Bool.spec (GF := GF) (hG := hG) := Enc.Bool.wp_proof
theorem Enc.wp_Str : Enc.Str.spec (GF := GF) (hG := hG) := Enc.Str.wp_proof Enc.wp_U64
theorem wp_NewDec : NewDec.spec (GF := GF) (hG := hG) := NewDec.wp_proof
theorem Dec.wp_U64 : Dec.U64.spec (GF := GF) (hG := hG) := Dec.U64.wp_proof
theorem Dec.wp_I64 : Dec.I64.spec (GF := GF) (hG := hG) := Dec.I64.wp_proof Dec.wp_U64
theorem Dec.wp_Int : Dec.Int.spec (GF := GF) (hG := hG) := Dec.Int.wp_proof Dec.wp_U64
theorem Dec.wp_Bool : Dec.Bool.spec (GF := GF) (hG := hG) := Dec.Bool.wp_proof
theorem Dec.wp_Str : Dec.Str.spec (GF := GF) (hG := hG) := Dec.Str.wp_proof Dec.wp_U64
theorem Dec.wp_Done : Dec.Done.spec (GF := GF) (hG := hG) := Dec.Done.wp_proof

end linked

end EtcdGrove.enc
end Perennial
