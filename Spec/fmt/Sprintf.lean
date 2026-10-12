/- Port of election_proof/spec_fmt_Sprintf.v (feb5c73d4). -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `fmt.Sprintf` is not translated (`fmt`'s printer reaches `reflect`); Perennial
models it (`Perennial/TrustedCode/fmt.lean`) and proves `fmt.wp_Sprintf`. `newRaft` uses
it only to build a log line. Two triples:

* the general one, proved from Perennial's: the postcondition is *some* string. It asks
  only that an argument's dynamic type tell the truth about its value for the types
  Perennial's model formats (`fmt.ArgsWf`: a `string` holds a string, an integer type an
  integer);
* `Sprintf("%x", n)` for a `uint64` `n` returns at most 16 bytes (its hexadecimal digits,
  without leading zeros). Perennial's model leaves the output of `%x` arbitrary, so this half
  is at the trust boundary (`fmt.Sprintf.wp_hex`, `Proof/fmt/Sprintf.lean`). `newRaft` needs
  it for `strings.Join` of the voters' ids, which panics on a join longer than `maxAlloc`. -/
abbrev fmt.Sprintf.spec : Prop :=
  (∀ (format : GoString) (args : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args ↦*{dq} xs ∗
        ⌜_root_.Perennial.fmt.ArgsWf xs⌝ }}
      (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #format)) (Val #args))
    {{ (s : GoString), RET #s; args ↦*{dq} xs }}) ∧
  (∀ (args : GoSlice) (n : w64) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
        args ↦*{dq} [interface.mkOk go.uint64 #n] }}
      (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #(go!"%x")))
        (Val #args))
    {{ (s : GoString), RET #s; args ↦*{dq} [interface.mkOk go.uint64 #n] ∗
        ⌜s.length ≤ 16⌝ }})

end spec

end EtcdGrove
end Perennial
