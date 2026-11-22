/-
The frame helpers of `examples/lib/remote`, linked (a linking module): each proof of
`putU64`, `getU64`, `writeAll`, `readFull`, `writeFrame`, `readFrame` applied to its callees'
linked proofs, down to the net package's own (`net.Conn.Write.wp_proof`, `net.Conn.Read.wp_proof`,
closed). No hypothesis is left.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.putU64
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.getU64
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.writeAll
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.readFull
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.writeFrame
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.readFrame
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Read

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

theorem wp_putU64 : putU64.spec (GF := GF) (hG := hG) := putU64.wp_proof

theorem wp_getU64 : getU64.spec (GF := GF) (hG := hG) := getU64.wp_proof

theorem wp_writeAll : writeAll.spec (GF := GF) (hG := hG) :=
  writeAll.wp_proof net.Conn.Write.wp_proof

theorem wp_readFull : readFull.spec (GF := GF) (hG := hG) :=
  readFull.wp_proof net.Conn.Read.wp_proof

theorem wp_writeFrame : writeFrame.spec (GF := GF) (hG := hG) :=
  writeFrame.wp_proof wp_putU64 wp_writeAll

theorem wp_readFrame : readFrame.spec (GF := GF) (hG := hG) :=
  readFrame.wp_proof wp_readFull wp_getU64

end linked

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
